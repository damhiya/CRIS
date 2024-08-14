Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ISim.
Require Import MapHeader Mem1.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.
Set Implicit Arguments.

Module MapAS.
Section MAP.
  Context `{_W: CtxWD.t}.

  Global Instance RA: URA.t := URA.prod (Excl.t unit) (Auth.t (Z ==> (Excl.t Z)))%ra.
  Context `{@GRA.inG RA Γ}.

  Definition points_to_r (k: Z) (v: Z): RA :=
    (ε, Auth.white ((fun n => if Z.eq_dec n k then Excl.just v else ε): @URA.car (Z ==> (Excl.t Z))%ra)).
  Definition points_to (k: Z) (v: Z): iProp :=
    OwnM (points_to_r k v).

  Definition pending_r: RA :=
    (Excl.just tt, ε).
  Definition pending: iProp :=
    OwnM pending_r.

  Definition initial_r: (Z ==> (Excl.t Z))%ra := (fun _ => Excl.just 0%Z).
  Definition initial_map_r: RA :=
    (ε, (Auth.black initial_r) ⋅ (Auth.white initial_r)).
  Definition initial_map: iProp :=
    OwnM initial_map_r.

  Definition black_map_r (f: Z -> Z): RA :=
    (Excl.unit, Auth.black ((fun k => Excl.just (f k)): (Z ==> (Excl.t Z))%ra)).
  Definition black_map (f: Z -> Z): iProp :=
    OwnM (black_map_r f).

  Definition unallocated_r (sz: Z): RA :=
    (Excl.unit, Auth.white ((fun k =>
                               if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                               else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                             : (Z ==> (Excl.t Z))%ra)).
  Definition unallocated (sz: Z): iProp :=
    OwnM (unallocated_r sz).

  Definition initial_points_tos (sz: nat) : iProp :=
    ([∗ list] i↦v ∈ (repeat (0:Z) sz), points_to i%Z v)%I.
  
  Definition init_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun (sz: nat) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint sz]: list val)↑⌝
                                    ∗ ⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝
                                    ∗ pending)%I),
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ initial_points_tos sz)%I)))).

  Definition get_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, v) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k])↑⌝
                                     ∗ points_to k v)%I),
                      (fun vret => (⌜vret = (Vint v)↑⌝ ∗ points_to k v)%I)))).

  Definition set_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, w, v) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k; Vint v])↑⌝
                                     ∗ points_to k w)%I),
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ points_to k v)%I)))).

  Definition set_by_user_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, w) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k])↑⌝
                                     ∗ points_to k w)%I),
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ ∃ v, points_to k v)%I)))).
  
  Definition Stb: alist gname fspec :=
    Seal.sealing "stb" [(MapName.init, init_spec);
                        (MapName.get, get_spec);
                        (MapName.set, set_spec);
                        (MapName.set_by_user, set_by_user_spec)].
  
End MAP.
End MapAS.

Module MapAR.
  Class t
    `{@GRA.inG MapAS.RA Γ}
    := MapARes: unit.

End MapAR.

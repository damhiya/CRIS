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

Module MapMS.
Section MAP.
  Context `{_W: CtxWD.t}.

  Definition RA: URA.t := Excl.t unit.
  Context `{@GRA.inG RA Γ}. 

  Definition pending_r: RA := Excl.just tt.

  Definition pending: iProp :=
    OwnM pending_r.

  Global Opaque pending.

  Definition init_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun (sz: nat) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint sz]: list val)↑⌝
                                     ∗ ⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝
                                     ∗ pending)%I),
                      (fun vret => True%I)))).

  Definition get_spec: fspec := 
    mk_fspec_inv 0
    (fun _ _ => mk_simple (fun k =>
                  (ord_top,
                    (fun varg => (⌜varg = ([Vint k])↑⌝)%I),
                    (fun vret => True%I)))).  

  Definition set_spec: fspec :=
    mk_fspec_inv 0
    (fun _ _ => mk_simple (fun '(k, v) =>
                  (ord_top,
                    (fun varg => (⌜varg = ([Vint k; Vint v])↑⌝)%I),
                    (fun vret => True%I)))).  

  Definition set_by_user_spec: fspec := 
    mk_fspec_inv 0
    (fun _ _ => mk_simple (fun k =>
                  (ord_top,
                    (fun varg => (⌜varg = ([Vint k])↑⌝)%I),
                    (fun vret => True%I)))).  

  Definition fnsems: list (string * fspecbody) :=
    [(MapName.init, init_spec);
     (MapName.get, get_spec);
     (MapName.set, set_spec);
     (MapName.set_by_user, set_by_user_spec)]
  
  Definition Stb: alist gname fspec :=
    Seal.sealing "stb" [(MapName.init, init_spec);
                        (MapName.get, get_spec);
                        (MapName.set, set_spec);
                        (MapName.set_by_user, set_by_user_spec)].

End MAP.
End MapMS.

Module MapMR.
  Class t
    `{@GRA.inG MapMS.RA Γ}
    := MapRA: unit.

End MapMR.


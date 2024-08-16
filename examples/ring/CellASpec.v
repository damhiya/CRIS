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
Require Import CellHeader.

Set Implicit Arguments.

Module CellAS.
Section SPEC.
  Context `{Σ: GRA.t}.

  Variable idx: nat.

  Definition pendingRA: URA.t := (nat ==> Excl.t unit)%ra.
  Definition cellRA: URA.t := (nat ==> (Excl.t Z))%ra.
  Global Instance RA: URA.t := URA.prod pendingRA (Auth.t cellRA).
  Context `{@GRA.inG RA Σ}.

  Definition pending_r: pendingRA :=
    (fun n => if Nat.eq_dec n idx then Excl.just tt else ε).
  Definition pending: iProp :=
    OwnM ((pending_r, ε) : RA).

  Definition cell_r (v: Z) : cellRA :=
    (fun n => if Nat.eq_dec n idx then Excl.just v else ε).
  Definition cell (v: Z): iProp :=
    OwnM ((ε, Auth.white (cell_r v)) : RA).
  Definition auth (v: Z) : iProp :=
    OwnM ((ε, Auth.black (cell_r v)): RA).

  Global Opaque cell auth.

  Definition init_spec : fspec :=
    mk_simple (fun _: unit =>
                 (ord_top,
                 (fun arg => ⌜arg = tt↑⌝ ∗ pending),
                 (fun ret => ⌜ret = tt↑⌝ ∗ cell 0)))%I.

  Definition get_spec : fspec :=
    mk_simple (fun v: Z =>
                 (ord_top,
                 (fun arg => ⌜arg = tt↑⌝ ∗ cell v),
                 (fun ret => ⌜ret = v↑⌝ ∗ cell v)))%I.

  Definition set_spec : fspec :=
    mk_simple (fun '(v0,v) =>
                 (ord_top,
                 (fun arg => ⌜arg = v↑⌝ ∗ cell v0),
                 (fun ret => ⌜ret = tt↑⌝ ∗ cell v)))%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "stb" [(CellName.init idx, init_spec);
                        (CellName.get idx, get_spec);
                        (CellName.set idx, set_spec)].

End SPEC.
End CellAS.

Global Hint Unfold CellAS.Stb: stb.

Module CellRA.
  Class t
    `{Σ: GRA.t}
    `{@GRA.inG CellAS.RA Σ}
    := CellRA: unit.
End CellRA.

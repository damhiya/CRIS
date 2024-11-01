Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB ITactics.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import CellHeader.

Set Implicit Arguments.

Module CellAS.
Section SPEC.
  Context `{Σ : GRA.t}.

  Variable idx : nat.

  Definition pendingRA : URA.t := (nat ==> Excl.t unit)%ra.
  Definition cellRA : URA.t := (nat ==> (Excl.t Z))%ra.
  Global Instance RA : URA.t := URA.prod pendingRA (Auth.t cellRA).
  Context `{@GRA.inG RA Σ}.

  Definition pending_r : RA :=
    ((fun n => if Nat.eq_dec n idx then Excl.just tt else ε) : pendingRA, ε).
  Definition pending : iProp :=
    Seal.sealing "ccr"
      (OwnM pending_r).

  Definition cellraw_r (v : Z) : cellRA :=
    (fun n => if Nat.eq_dec n idx then Excl.just v else ε).
  Definition cell_r (v : Z) : RA :=
    (ε, Auth.white (cellraw_r v)).
  Definition cell (v : Z) : iProp :=
    Seal.sealing "ccr"
      (OwnM (cell_r v)).
  Definition auth_r (v : Z) : RA :=
    (ε, Auth.black (cellraw_r v)).
  Definition auth (v : Z) : iProp :=
    Seal.sealing "ccr"
      (OwnM (auth_r v)).

  Definition get_spec : fspec :=
    fspec_simple (fun v: Z =>
     ((fun arg => ⌜arg = tt↑⌝ ∗ cell v),
      (fun ret => ⌜ret = v↑⌝ ∗ cell v)))%I.

  Definition set_spec : fspec :=
    fspec_simple (fun '(v0,v) =>
     ((fun arg => ⌜arg = v↑⌝ ∗ (pending ∨ cell v0)),
      (fun ret => ⌜ret = tt↑⌝ ∗ cell v)))%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr" [(CellName.get idx, get_spec);
                        (CellName.set idx, set_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.
  
End SPEC.
End CellAS.

Global Hint Unfold CellAS.Stb : stb.

Module CellRA.
  Class t
    `{Σ : GRA.t}
    `{@GRA.inG CellAS.RA Σ}
    := CellRA : unit.
End CellRA.

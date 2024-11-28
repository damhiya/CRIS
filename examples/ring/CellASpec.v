Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM STB sProp sWorld.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ISim.
Require Import CellHeader.
From iris.algebra Require Import auth excl functions.

Set Implicit Arguments.

Module CellAS. Section CellAS.
  Variable idx : nat.
 
  Definition pendingRA : ucmra := (nat -d> optionUR (exclR unitO)).
  Definition cellRA : ucmra := (nat -d> optionUR (exclR ZO)).

  Definition RA : ucmra := prodUR pendingRA (authUR cellRA).

  Class G (Γ : HRA.t) := { #[local] RA_inG :: GRA.inG RA Γ }.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.

  Notation iProp := (iProp Σ).

  Definition pending_r : RA :=
    ((fun n => if Nat.eq_dec n idx then Excl' tt else ε) : pendingRA, ε).

  Definition pending : iProp :=
    Seal.sealing "CellAS"
      (OwnM pending_r).
 
  Definition cellraw_r (v : Z) : cellRA :=
    (fun n => if Nat.eq_dec n idx then Excl' v else ε).
 
  Definition cell_r (v : Z) : RA :=
    (ε, ◯ (cellraw_r v)).
  Definition cell (v : Z) : iProp :=
    Seal.sealing "CellAS"
      (OwnM (cell_r v)).

  Definition auth_r (v : Z) : RA :=
    (ε, ● (cellraw_r v)).
  Definition auth (v : Z) : iProp :=
    Seal.sealing "CellAS"
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
    Seal.sealing "CellAS" [(CellName.get idx, get_spec);
                        (CellName.set idx, set_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "CellAS". prove_nodup.
  Qed.
  
End CellAS. End CellAS.

Global Hint Unfold CellAS.Stb : stb.


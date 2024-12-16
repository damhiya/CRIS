Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ISim.
Require Import CannonHeader.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

From iris.algebra Require Import excl_auth.

Set Implicit Arguments.

Module CannonAS.
Section Cannon.
  Class G (Γ: HRA.t) := { #[local] RA_inG :: GRA.inG (excl_authR unitO) Γ }.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Definition Ready: iProp := 
    Seal.sealing "CannonA" 
      (OwnM (●E tt)).
  Definition Ball: iProp :=
    Seal.sealing "CannonA"
      (OwnM (◯E tt)).
  Definition Fired: iProp :=
    Seal.sealing "CannonA"
      (OwnM ((●E tt) ⋅ (◯E tt))).

  Lemma ReadyBall: 
    Ready ∗ Ball ⊢ Fired.
  Proof.
    rewrite /Ready /Ball /Fired. unseal "CannonA".
    iIntros "[B W]". iSplitL "B"; iFrame.
  Qed.

  Lemma FiredReady: 
    Ready ∗ Fired ⊢ False.
  Proof. 
    rewrite /Ready /Fired. unseal "CannonA".
    iIntros "[B0 [B1 W]]". iCombine "B0 B1" as "X".
    iOwnWf "X" as X. rewrite excl_auth_auth_op_valid // in X.
  Qed.

  Lemma FiredBall: 
    Ball ∗ Fired ⊢ False.
  Proof.
    rewrite /Ball /Fired. unseal "CannonA".
    iIntros "[W0 [B W1]]". iCombine "W0 W1" as "X".
    iOwnWf "X" as X. rewrite excl_auth_frag_op_valid // in X.
  Qed.

  Definition fire_spec: fspec :=
    fspec_simple (fun (_: unit) =>
        ((fun varg => (⌜varg = ([]: list val)↑⌝ ∗ Ball)%I),
        (fun vret => (⌜vret = (1: Z)%Z↑⌝)%I))).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(CannonName.fire, fire_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End Cannon.
End CannonAS.

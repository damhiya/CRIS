Require Import sflib.
Require Import Coqlib ITreelib sflib.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB.

Require Import ISim.

From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Require Import Coq.Logic.ClassicalEpsilon.

Set Implicit Arguments.

Section GINV.

  Context `{_W: Inv.t}.

  Definition sch_ginv (univ: positive): Sk.t -> invspec :=
    fun _ _ => (∃ n, closed_universe univ n ⊤)%I.

End GINV.

Section AUX.

  Context `{_W: Inv.t}.
  Notation iProp := (iProp Σ).

  Global Instance inv_persistent 
  u n i p : Persistent (inv u n i p).
  Proof.
    Local Transparent inv.
    unfold inv. unfold Persistent. iIntros "#I". iModIntro. iApply "I".
  Qed.

  Definition close_inv (u: positive) (n invn: nat) (ns: namespace) (p: SRFSyn.t invn): iProp :=
    (⟦ p ⟧ -∗ closed_universe u n (⊤ ∖ ↑ns) ==∗ closed_universe u n ⊤).

  Lemma open_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    inv u lv0 ns p ∗ closed_universe u lv1 ⊤
    -∗ ( |==> ⟦ p ⟧ ∗ closed_universe u lv1 (⊤ ∖↑ns) ∗ close_inv u lv1 ns p).
  Proof.
    Local Transparent FUpd.
    iIntros "[#INV W]".
    iPoseProof (FUpd_open with "[INV]") as "F"; et.
    unfold FUpd. iPoseProof ("F" with "[W]") as "FU".
    { iDestruct "W" as "[U FW]". iFrame. iApply "FW". }
    iMod "FU". iDestruct "FU" as "(FW & W & P & FU)". iFrame.
    iModIntro. iIntros "P CW". iPoseProof ("FU" with "[P]") as "P"; et.
    iPoseProof ("P" with "[CW]") as ">[U [FW _]]".
    { iDestruct "CW" as "[U FW]". iFrame. }
    iModIntro. iFrame.
  Qed.

  Lemma close_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    ⟦ p ⟧ ∗ closed_universe u lv1 (⊤∖↑ns) ∗ @close_inv u lv1 lv0 ns p
    -∗ ( |==> closed_universe u lv1 ⊤).
  Proof.
    Local Transparent FUpd.
    iIntros "(INV & W & CLOSE)".
    unfold close_inv. iPoseProof ("CLOSE" with "[INV]") as "INV"; et.
    iPoseProof ("INV" with "[W]") as "W"; et.
  Qed.
    
End AUX.
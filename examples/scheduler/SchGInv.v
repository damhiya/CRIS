Require Import CRIS.

Require Import SchInvariants.

Set Implicit Arguments.

Section GINV.

  Context `{_W: sinvG}.

  Definition sch_ginv (univ: positive): Sk.t -> invspec :=
    fun _ _ => (∃ n, wsats univ n ⊤)%I.

End GINV.

Section AUX.
  Context `{@sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Definition close_inv (u: positive) (n invn: nat) (ns: namespace) (p: SRFSyn.t invn) : iProp :=
    (⟦p⟧ -∗ wsats u n (⊤ ∖ ↑ns) ==∗ wsats u n ⊤).

  Local Transparent FUpd.
  
  Lemma open_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    inv u lv0 ns p ∗ wsats u lv1 ⊤
    ⊢
    |==> (⟦ p ⟧ ∗ @close_inv u lv1 lv0 ns p ∗ wsats u lv1 (⊤∖↑ns)).
  Proof.
    iIntros "[#INV W]".
    iPoseProof (FUpd_open with "[INV]") as "F"; et.
    unfold FUpd, SchInvariants.fancy_wsats, wsats.
    iDestruct "W" as "(A & E & D & W)".
    iPoseProof ("F" with "[E D W]") as "FU". { iFrame. }
    iMod "FU". iDestruct "FU" as "(W & P & CI)". iSplitL "P"; et.
    iSplitR "A W". 2:{ iFrame. et. }
    iModIntro. unfold close_inv. iIntros "P W". iPoseProof ("CI" with "[P]") as "P"; et.
    iDestruct "W" as "[U W]". iPoseProof ("P" with "[W]") as ">((E & D & W) & _)". { iFrame. }
    iModIntro. iFrame.
  Qed.

  Lemma close_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    ⟦ p ⟧ ∗ wsats u lv1 (⊤∖↑ns) ∗ @close_inv u lv1 lv0 ns p
    ⊢
    |==> wsats u lv1 ⊤.
  Proof.
    iIntros "(INV & W & CLOSE)".
    unfold close_inv. iPoseProof ("CLOSE" with "[INV]") as "INV"; et.
    iPoseProof ("INV" with "[W]") as "W"; et.
  Qed.
    
End AUX.
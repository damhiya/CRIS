Require Import CRIS.

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

  (* Lemma open_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    inv u lv0 ns p -∗ ( =|u, lv1|={⊤}=> ⟦ p ⟧ ∗ @close_inv u lv1 lv0 ns p).
  Proof.
    iIntros "#INV". ss. iModIntro.
    iApply elim_acc_fupd.
    iInv "INV" as "T".
    Search fupd.
    iPoseProof (fupd_open with "[INV]") as "F"; et.
    unfold invariants.FUpd. iPoseProof ("F" with "[W]") as "FU".
    { iDestruct "W" as "[U FW]". iFrame. iApply "FW". }
    iMod "FU". iDestruct "FU" as "(FW & W & P & FU)". iFrame.
    iModIntro. iIntros "P CW". iPoseProof ("FU" with "[P]") as "P"; et.
    iPoseProof ("P" with "[CW]") as ">[U [FW _]]".
    { iDestruct "CW" as "[U FW]". iFrame. }
    iModIntro. iFrame.
  Admitted.

  Lemma close_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    ⟦ p ⟧ ∗ wsats u lv1 (⊤∖↑ns) ∗ @close_inv u lv1 lv0 ns p
    -∗ ( |==> wsats u lv1 ⊤).
  Proof.
    iIntros "(INV & W & CLOSE)".
    unfold close_inv. iPoseProof ("CLOSE" with "[INV]") as "INV"; et.
    iPoseProof ("INV" with "[W]") as "W"; et.
  Qed. *)
    
End AUX.
From CRIS.modules Require Import Mod ModTr.
From CRIS.simulations.msim Require Import MSimCommon MSim.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base.

Lemma msim_ist_frame `{Σ : GRA} contextual fl_src fl_tgt Rs Rt RR Ist P ps pt
    (sti_s: _ * itree crisE Rs) (sti_t: _ * itree crisE Rt) fmr0 fmr
    (SIM : msim contextual fl_src fl_tgt Ist RR ps pt sti_s sti_t fmr0)
    (FMR: Own fmr ⊢ |==> P ∗ Own fmr0) :
  msim contextual fl_src fl_tgt (λ x y, P ∗ Ist x y)%I (λ x y, P ∗ RR x y)%I ps pt sti_s sti_t fmr.
Proof.
  ginit. revert_until P. gcofix CIH. i.
  gstep.
  punfold SIM. move SIM before CIH. revert_until SIM.
  pattern ps, pt, sti_s, sti_t, fmr0.
  eapply _msim_tarski, SIM. i.
  econs. ii.
  exploit IN; et.
  { eapply Own_wand_valid, H. rewrite FMR. iIntros "[_ H]". et. }
  i; des. esplits; et.
  destruct x0;
    try by econs; et; i; eapply K; et;
           rewrite FMR x1; iIntros ">[? >?]"; iFrame; et.
  - (* Ret *)
    econs; et. rewrite FMR x1 RET. iIntros ">[? >>?]". iFrame. et.
  - (* Call *)
    econs; et.
    { rewrite FMR x1 INV. iIntros ">[? >>[? ?]]". iFrame. et. }
    i. rewrite -assoc in INV0.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in INV0; et. des.
    eapply K; et; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - (* Assume src *)
    econs; et; i.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Assume tgt *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* AssumeRes src *)
    econs; et; i.
    (* { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. } *)
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[> > ? ?]". iFrame. et.
  - (* AssumeRes tgt  *)
    econs; et; i.
    { rewrite FMR x1 CUR //. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et.
    }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); et; cycle 1.
    + rewrite NEW1; iIntros "$ //".
    + rewrite NEW NEW0. et.
    + eapply Own_wand_valid; [iIntros "H"; iMod (NEW with "H") as "[_ $]"|]; ss.
  - (* Guarantee src *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* Guarantee tgt *)
    econs; et; i.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Yield *)
    econs; et; i.
    { rewrite FMR x1 INV. iIntros ">[? >>[? ?]]". iFrame. et. }
    rewrite -assoc in INV0.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in INV0; et. des.
    eapply K; et; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - (* progress *)
    pclearbot. econs; et; i.
    gbase. eapply CIH; et.
    rewrite FMR x1. iIntros ">[? >?]". iFrame. et.
Qed.


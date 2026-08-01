From CRIS.common Require Import StatePredicate.
From CRIS.modules Require Import Mod ModTr.
From CRIS.simulations.msim Require Import MSimCommon MSim.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base.

Lemma msim_ist_frame `{!stateGS Σ} contextual fl_src fl_tgt Rs Rt RR Ist P ps pt
    (i_s: itree crisE Rs) (i_t: itree crisE Rt) fmr0 fmr
    (SIM : msim contextual fl_src fl_tgt Ist RR ps pt i_s i_t fmr0)
    (FMR: Own fmr ⊢ |==> P ∗ Own fmr0) :
  msim contextual fl_src fl_tgt (P ∗ Ist)%I (λ x y, P ∗ RR x y)%I ps pt i_s i_t fmr.
Proof.
  ginit. revert_until P. gcofix CIH. i.
  gstep.
  punfold SIM. move SIM before CIH. revert_until SIM.
  pattern ps, pt, i_s, i_t, fmr0.
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
    eapply Own_bupd_split in INV0; et. des.
    eapply (K vret a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - (* SPut src *)
    econs; et.
    { instantiate (1 := (P ∗ FMR0)%I). instantiate (1 := v).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut tgt *)
    econs; et.
    { instantiate (1 := (P ∗ FMR0)%I). instantiate (1 := v).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet src *)
    econs; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet tgt *)
    econs; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut src, uninitialized *)
    eapply msim_sput_src_uninit; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut tgt, uninitialized *)
    eapply msim_sput_tgt_uninit; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet src, uninitialized *)
    eapply msim_sget_src_uninit; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet tgt, uninitialized *)
    eapply msim_sget_tgt_uninit; et.
    { instantiate (1 := (P ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* Assume src *)
    econs; et; i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Assume tgt *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* AssumeRes src *)
    econs; et; i.
    (* { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. } *)
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[> > ? ?]". iFrame. et.
  - (* AssumeRes tgt  *)
    econs; et; i.
    { rewrite FMR x1 CUR //. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et.
    }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1; iIntros "$ //".
  - (* Guarantee src *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* Guarantee tgt *)
    econs; et; i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Yield *)
    econs; et; i.
    { rewrite FMR x1 INV. iIntros ">[? >>[? ?]]". iFrame. et. }
    rewrite -assoc in INV0.
    eapply Own_bupd_split in INV0; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - (* progress *)
    pclearbot. econs; et; i.
    gbase. eapply CIH; et.
    rewrite FMR x1. iIntros ">[? >?]". iFrame. et.
Qed.

Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.

Require Import Mod.
Require Import MSimCommon.
Require Import LSim LSimFacts.
Require Import ISim ISimFacts.
Require Import CtxRefine.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem closed_adequacy (ms mt : Mod.t) IC Ist P :
    ISim.t closed ms mt IC Ist →
    refines (ms, IC ∗ P)%I (mt, P).
  Proof using.
    split.
    { eapply ISim_wf; eauto. }
    intros rs Hrsval [rwinv [ric [Hrs [Hrwinv Hric]]]]%Own_bupd_split; ss; eauto.
    (* ii. ss. eapply Own_bupd_split in SRC; eauto. des. *)
    eapply Own_split in Hric as [ric1 [ric2 [Hric [Hric1 Hric2]]]]; eauto; cycle 1.
    { eapply Own_wand_valid, Hrsval. rewrite Hrs. iIntros ">[_ ?] //". }
    rewrite winv_split_empty in Hrwinv.
    eapply Own_split in Hrwinv as [rwinv1 [rwinv2 [Hrwinv [Hrwinv1 Hrwinv2]]]]; eauto; des; cycle 1.
    { eapply Own_wand_valid, Hrsval. rewrite Hrs. iIntros ">[$ ?] //". }
    exists (ric2 ⋅ rwinv2).
    esplits; eauto.
    { eapply Own_wand_valid, Hrsval. rewrite Hrs Hric Hrwinv !Own_op. iIntros ">[[? $] [? $]] //". }
    { rewrite Own_op Hrwinv2 Hric2 comm; eauto. }
    ii. eapply lsim_adequacy, PR.
    - eapply ISim_adequacy; et.
      rewrite Hrs Hric Own_op Hric1 Hrwinv !Own_op Hrwinv1.
      iIntros ">[[? ?] [? ?]]". iFrame. eauto.
  Qed.

  Theorem closed_adequacy_emp (ms mt : Mod.t) Ist P :
    ISim.t closed ms mt emp%I Ist →
    refines (ms, P) (mt, P).
  Proof using.
    intros Hsim%(closed_adequacy ms mt _ _ P).
    ii. exploit Hsim; eauto. i; des. esplits; eauto.
    i. exploit x1; eauto. ss. rewrite -bi.emp_sep_1. eauto.
  Qed.
End ADEQUACY.

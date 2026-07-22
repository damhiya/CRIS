From iris.proofmode Require Import proofmode.
From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy MainAdequacy.
From CRIS.simulations.msim Require Import Tactics TacticsInit MSimCommon ISimFacts.

(** Properties of contextual refinement *)
Section CtxRefineFacts.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Global Program Instance refines_mod_PreOrder : PreOrder (@refines_lmod).
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0. eapply H. ss. Qed.

  Lemma refines_refl M : ⊢ refines M M.
  Proof.
    iStartProof.
    iApply (ISim_closed_adequacy _ _ True%I IstEq); et.
    eapply ISim_refl; et.
  Qed.

  Lemma refines_trans M1 M2 M3 :
    refines M1 M2 ∗ refines M2 M3 ⊢ refines M1 M3.
  Proof.
    econs. intros x V_x. uPred.unseal.
    intros [r1 [r2 [SPLIT [H1 H2]]]]. revert H1 H2.
    intros R1 R2.
    rewrite refines_unseal; intros WF1.
    rewrite refines_unseal in R1; specialize (R1 WF1). destruct R1 as [WF2 R1].
    rewrite refines_unseal in R2; specialize (R2 WF2). destruct R2 as [WF3 R2].
    split. { eapply WF3. }
    intros rt rs H0 V_rs.
    assert (H1: Own rs ⊢ (Own rt ∗ Own r1 ∗ winv (∅,∅)) ∗ Own r2 ∗ winv (∅,∅)).
    { iIntros "H". iDestruct (H0 with "H") as "(H1 & H2 & H3)".
      rewrite SPLIT. iDestruct (Own_op with "H2") as "[H21 H22]".
      iDestruct (winv_split_empty with "H3") as "[H31 H32]".
      iFrame.
    }
    assert (H2: exists rs1, (Own rs1 ⊢ Own rt ∗ Own r1 ∗ winv (∅,∅)) /\ ✓ rs1
                       /\ (Own rs ⊢ Own rs1 ∗ Own r2 ∗ winv (∅,∅))).
    { clear - H1 V_rs.
      remember (Own rt ∗ Own r1 ∗ winv (∅,∅))%I as P.
      remember (Own r2 ∗ winv (∅,∅))%I as Q.
      eapply Own_general_soundness in H1; et.
      uPred.unseal_in H1. destruct H1 as [rs1 [rs2 [SPLIT [H1 H2]]]].
      exists rs1. splits.
      - eapply Own_general_completeness; et.
      - rewrite SPLIT in V_rs.
        eapply cmra_valid_op_l in V_rs.
        et.
      - rewrite SPLIT. iIntros "[$ H]". iStopProof.
        eapply Own_general_completeness; et.
    }
    destruct H2 as [rs1 [H_rs1 [V_rs1 H_rs]]].
    specialize (R1 rt rs1 H_rs1 V_rs1).
    specialize (R2 rs1 rs H_rs V_rs).
    clear - R1 R2. intros t H. eapply R2. eapply R1. et.
  Qed.

  (*** vertical composition ***)
  Lemma ctxr_refl M : ⊢ ctx_refines M M.
  Proof.
    iIntros (Ctx). iApply refines_refl.
  Qed.

  Lemma ctxr_trans M1 M2 M3 :
    ctx_refines M1 M2 ∗ ctx_refines M2 M3 ⊢ ctx_refines M1 M3.
  Proof.
    iIntros "[H1 H2] %Ctx".
    iSpecialize ("H1" $! Ctx).
    iSpecialize ("H2" $! Ctx).
    iApply refines_trans. iFrame.
  Qed.

  Lemma ctxr_refines Mt Ms
    : ctx_refines Mt Ms ⊢ refines Mt Ms.
  Proof.
    iIntros "H". iSpecialize ("H" $! Mod.empty).
    rewrite !right_id. et.
  Qed.

  (*** algebraic equalities ***)
  Lemma ctxr_comm (M N : Mod.t)
    : ⊢ ctx_refines (M ★ N) (N ★ M).
  Proof.
    rewrite comm. eapply ctxr_refl.
  Qed.

  Lemma ctxr_assoc
    M1 M2 M3
    : ⊢ ctx_refines ((M1 ★ M2) ★ M3) (M1 ★ (M2 ★ M3)).
  Proof.
    rewrite assoc.
    eapply ctxr_refl.
  Qed.

  Lemma ctxr_swap
    M1 M2 M3
    : ⊢ ctx_refines (M1 ★ (M2 ★ M3)) ((M2 ★ M1) ★ M3).
  Proof.
    rewrite (comm _ M2 M1).
    rewrite assoc.
    eapply ctxr_refl.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_module M
    : ⊢ ctx_refines M ⌽.
  Proof.
    iApply (main_adequacy _ _ True%I (fun _ _ => emp%I)); et.
    cStartModSim; ss.
  Qed.

  (*** frame rules ***)
  Lemma ctxr_frameL Mt Ms C :
    ctx_refines Mt Ms ⊢ ctx_refines (C ★ Mt) (C ★ Ms).
  Proof.
    iIntros "H %Ctx".
    iSpecialize ("H" $! (C ★ Ctx)).
    rewrite (comm _ C Mt).
    rewrite (comm _ C Ms).
    rewrite !assoc; et.
  Qed.

  Lemma ctxr_frameR Mt Ms C :
    ctx_refines Mt Ms ⊢ ctx_refines (Mt ★ C) (Ms ★ C).
  Proof.
    iIntros "H %Ctx".
    iSpecialize ("H" $! (C ★ Ctx)).
    rewrite !assoc; et.
  Qed.

  (*** horizontal composition ***)
  Lemma ctxr_compose_hor
    Mt Ms Nt Ns :
    ctx_refines Mt Ms ∗ ctx_refines Nt Ns
      ⊢ ctx_refines (Mt ★ Nt) (Ms ★ Ns).
  Proof.
    iIntros "[H1 H2]".
    iPoseProof (ctxr_frameR _ _ Nt with "H1") as "H1".
    iPoseProof (ctxr_frameL _ _ Ms with "H2") as "H2".
    iApply ctxr_trans; iFrame.
  Qed.

  (*** mixed composition ***)
  Lemma ctxr_compose_mix
    Mt Ms Nt Ns C :
    ctx_refines (Mt ★ C) (Ms ★ C) ∗ ctx_refines (Nt ★ C) (Ns ★ C)
      ⊢ ctx_refines (Mt ★ Nt ★ C) (Ms ★ Ns ★ C).
  Proof.
    iIntros "[H1 H2]".
    iPoseProof (ctxr_frameL _ _ Nt with "H1") as "H1".
    iPoseProof (ctxr_frameL _ _ Ms with "H2") as "H2".
    replace (Nt ★ Mt ★ C) with (Mt ★ Nt ★ C).
    2:{
      rewrite !assoc.
      rewrite (comm _ Mt Nt).
      et.
    }
    replace (Nt ★ Ms ★ C) with (Ms ★ Nt ★ C).
    2:{
      rewrite !assoc.
      rewrite (comm _ Ms Nt).
      et.
    }
    iApply ctxr_trans; iFrame.
  Qed.

End CtxRefineFacts.

Section ADEQUACY.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma refines_adequacy
    Mt Ms
    (WF : Mod.wf Mt)
    : winv (∅,∅) ∗ refines Mt Ms
        ⊢ ⌜ ∃ rs, ✓ rs /\ refines_lmod (Mod.to_lmod Mt ε) (Mod.to_lmod Ms rs) ⌝.
  Proof.
    eapply entails_pointwise. intros r Vr Hr.
    eapply Own_general_soundness in Hr; et.
    uPred.unseal_in Hr. destruct Hr as [r1 [r2 [SPLIT [WINV REF]]]].
    eapply Own_general_completeness in WINV.
    rewrite refines_unseal in REF. specialize (REF WF). destruct REF as [WFS REF].
    specialize (REF ε r).
    eapply Own_general_completeness. uPred.unseal. exists r. split; et.
    eapply REF; et. rewrite SPLIT.
    iIntros "[H1 H2]". rewrite WINV. iFrame. iApply Own_unit.
  Qed.

End ADEQUACY.

(** tactics for composing ctx_refines *)
Ltac ctxr_refl :=
  iApply ctxr_refl.

Tactic Notation "ctxr_transL" :=
  iApply ctxr_trans; iSplitL.

Tactic Notation "ctxr_transL" uconstr(hyp) :=
  iApply ctxr_trans; iSplitL hyp.

Tactic Notation "ctxr_transR" :=
  iApply ctxr_trans; iSplitR.

Tactic Notation "ctxr_transR" uconstr(hyp) :=
  iApply ctxr_trans; iSplitR hyp.

Ltac ctxr_norm :=
  try rewrite <- !mod_add_assoc;
  try rewrite mod_add_empty_l;
  try rewrite mod_add_empty_r.

Ltac ctxr_swap :=
  ctxr_transR;
  [ iApply ctxr_swap
  | ctxr_transR; [ iApply ctxr_assoc |]
  ].

Ltac ctxr_rotate :=
  ctxr_transR;
  [ iApply ctxr_comm | ctxr_norm ].

Ltac ctxr_drop :=
  iApply ctxr_frameL.

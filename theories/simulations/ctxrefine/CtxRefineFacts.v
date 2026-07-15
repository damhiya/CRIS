From iris.proofmode Require Import proofmode.
From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod.
From CRIS.simulations.ctxrefine Require Import CtxRefine MainAdequacy.
From CRIS.simulations.msim Require Import Tactics TacticsInit.

(** Properties of contextual refinement *)
Section CtxRefineFacts.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Global Program Instance refines_mod_PreOrder : PreOrder (@refines_lmod).
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0. eapply H. ss. Qed.

  Global Program Instance refines_PreOrder : PreOrder refines.
  Next Obligation.
    ii. esplits; eauto. ii. esplits; eauto. refl.
  Qed.
  Next Obligation.
    ii.
    edestruct H0; eauto; edestruct H; eauto. des.
    esplits; eauto. ii.
    specialize (H2 rs WFR SRC). des.
    specialize (H4 rt H2 H5). des. 
    exists rt0. esplits; eauto.
    etrans; eauto.
  Qed.

  Global Program Instance refines_Proper : Proper ((≡) ==> (≡) ==> iff) refines.
  Next Obligation.
    intros mt1 mt2 mteq ms1 ms2 mseq; split; intros CTXR.
    { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
      { apply CTXR; s; eauto. }
      { hexploit (CTXR WFM); ss; i; des; eauto.
        hexploit (H1 rs); eauto; [rewrite H0 //|].
        i; des; esplits; eauto; rewrite -H2 //. 
      }
    }
    { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
      { apply CTXR; s; eauto. }
      { hexploit (CTXR WFM); ss; i; des; eauto.
        hexploit (H1 rs); eauto; [rewrite -H0 //|].
        i; des; esplits; eauto; rewrite H2 //. 
      }
    }
  Qed.

  (*** vertical composition ***)
  Global Program Instance ctx_refines_PreOrder : PreOrder ctx_refines.
  Next Obligation. r. r. i. refl. Qed.
  Next Obligation.
    r. r. i. etrans.
    - apply H.
    - apply H0.
  Qed.

  Global Program Instance ctx_refines_Proper : Proper ((≡) ==> (≡) ==> iff) ctx_refines.
  Next Obligation.
    intros mt1 mt2 mteq ms1 ms2 mseq; split; intros CTXR.
    { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
      { apply CTXR; s; eauto. }
      { ii. destruct (CTXR _ WFM). hexploit (H1 rs); eauto; ss.
        { rewrite H0; done. }
        { intros [rt Hrt]; rewrite H2 in Hrt; des; exists rt; esplits; eauto. }
      }
    }
    { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
      { apply CTXR; s; eauto. }
      { ii. destruct (CTXR _ WFM). hexploit (H1 rs); eauto; ss.
        { rewrite -H0; done. }
        { intros [rt Hrt]; rewrite -H2 in Hrt; des; exists rt; esplits; eauto. }
      }
    }
  Qed.

  Global Program Instance ctx_refines_Proper2 mc : Proper ((≡) ==> iff) (ctx_refines mc).
  Next Obligation.
    i. eapply ctx_refines_Proper. et.
  Qed.

  Lemma ctxr_refines mct mcs (REF : ctx_refines mct mcs) :
    refines mct mcs.
  Proof using.
    i. specialize (REF Mod.empty_mc).
    destruct mcs, mct. ss.
    rewrite !right_id in REF.
    ii; split; ii; des; ss; red in REF; hexploit REF; eauto; i; des; ss.
    hexploit (H0 rs); ss.
  Qed.

  (*** weakening for initial condition ***)
  Lemma refines_consequence (m : Mod.t) (P Q : iProp Σ)
      (IMPL : P ⊢ Q) :
    refines (m, Q) (m, P).
  Proof using.
    ii. ss; split; first done. ii; ss; exists rs. esplits; eauto.
    + rewrite SRC IMPL. et.
    + refl.
  Qed.

  Lemma ctxr_consequence (m : Mod.t) (P Q : iProp Σ)
      (IMPL : P ⊢ Q) :
    ctx_refines (m, Q) (m, P).
  Proof using.
    r; i. apply refines_consequence; s; et.
    rewrite IMPL. et.
  Qed.

  (*** frame rule for initial condition ***)

  Lemma ctxr_cond_frameR (mt ms : Mod.t) Pt Ps Q
      (REF : ctx_refines (mt, Pt) (ms, Ps)) :
    ctx_refines (mt, Pt ∗ Q)%I (ms, Ps ∗ Q)%I.
  Proof using.
    ii. specialize (REF (ctx.1, Q ∗ ctx.2)%I).
    destruct ctx. ss.
    split.
    { red in REF. hexploit REF; ss; i; des; eauto. }
    ii. ss. des. red in REF. hexploit REF; ss; i; des; eauto.
    hexploit (H0 rs); ss.
    { rewrite SRC. iIntros ">[? [[? ?] ?]]". iFrame. et. }
    i; des; esplits; eauto.
    rewrite H2. iIntros ">[? [? [? ?]]]". iFrame. et.
  Qed.

  Lemma ctxr_cond_frameL (mt ms : Mod.t) Pt Ps Q
      (REF : ctx_refines (mt, Pt) (ms, Ps)) :
    ctx_refines (mt, Q ∗ Pt)%I (ms, Q ∗ Ps)%I.
  Proof using.
    etrans; [|etrans]; cycle 1.
    { apply ctxr_cond_frameR with (Q:=Q) in REF. apply REF. }
    { eapply ctxr_consequence. i. iIntros "(H1 & H2)". iFrame. }
    { eapply ctxr_consequence. i. iIntros "(H1 & H2)". iFrame. }
  Qed.

  (*** commutativity ***)
  Theorem ctxr_comm (ma mb : Mod.t) P:
    ctx_refines (Mod.add ma mb, P) (Mod.add mb ma, P).
  Proof using. rewrite comm //. Qed.

  (*** elimination of a module ***)
  Theorem elim_module mc P : ctx_refines (mc, P) (⌽, P).
  Proof using.
    rewrite -!(mod_addc_empty_l _ P).
    eapply ctxr_cond_frameR.
    eapply main_adequacy with (Ist := λ _ _, emp%I).
    cStartModSim; ss.
  Qed.

  (*** frame rules ***)
  Lemma ctxr_frameR mt Pt ms Ps mc (REFA : ctx_refines (mt, Pt) (ms, Ps)) :
    ctx_refines (mt ★ mc, Pt) (ms ★ mc, Ps).
  Proof using.
    intro. specialize (REFA (Mod.add mc ctx.1, ctx.2)). ss.
    move: REFA; rewrite !assoc; eauto.
  Qed.

  Lemma ctxr_frameL mt Pt mc ms Ps (REFA : ctx_refines (mt, Pt) (ms, Ps)) :
    ctx_refines (mc ★ mt, Pt) (mc ★ ms, Ps).
  Proof using.
    etrans. { eapply ctxr_comm. }
    etrans. { eapply ctxr_frameR. apply REFA. }
    apply ctxr_comm.
  Qed.

  (*** horizontal composition ***)
  Lemma ctxr_compose_hor mta Pta msa Psa mtb Ptb msb Psb
      (REFA : ctx_refines (mta, Pta) (msa, Psa))
      (REFB : ctx_refines (mtb, Ptb) (msb, Psb)) :
    ctx_refines (mta ★ mtb, Pta ∗ Ptb)%I
                (msa ★ msb, Psa ∗ Psb)%I.
  Proof using.
    etrans.
    - eapply ctxr_frameR, ctxr_cond_frameR. apply REFA.
    - eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. 
  Qed.

  (*** mixed composition ***)
  Lemma ctxr_compose_mix mta Pta msa Psa mtb Ptb msb Psb mc
      (REFA : ctx_refines (mta ★ mc, Pta) (msa ★ mc, Psa))
      (REFB : ctx_refines (mtb ★ mc, Ptb) (msb ★ mc, Psb)) :
    ctx_refines (mta ★ mtb ★ mc, Pta ∗ Ptb)%I
                (msa ★ msb ★ mc, Psa ∗ Psb)%I.
  Proof using.
    etrans.
    { eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. }
    etrans.
    { eapply ctxr_frameL, ctxr_comm. }
    etrans.
    { rewrite assoc.
      eapply ctxr_frameR, ctxr_cond_frameR. apply REFA. }
    rewrite -assoc.
    apply ctxr_frameL, ctxr_comm.
  Qed.

  (*** Corollaries for tactics ***)

  Corollary ctxr_compose_hor_simplR mta msa mtb msb P Pa
      (REFA : ctx_refines (mta, P) (msa, Pa))
      (REFB : ctx_refines (mtb, emp%I) (msb, emp%I)) :
    ctx_refines (mta ★ mtb, P)%I
                (msa ★ msb, Pa)%I.
  Proof using.
    rewrite -(mod_addc_empty_r _ P) -(mod_addc_empty_r _ Pa).
    eapply ctxr_compose_hor; et.
  Qed.

  Corollary ctxr_cond_frameR_simpl (mt ms : Mod.t) P Q
    (REF : ctx_refines (mt, emp%I) (ms, P))
    :
    ctx_refines (mt, Q)%I (ms, P ∗ Q)%I.
  Proof using.
    rewrite -(mod_addc_empty_l _ Q).
    eapply ctxr_cond_frameR. et.
  Qed.
End CtxRefineFacts.

(** tactics for composing ctx_refines *)
Ltac ctxr_norm :=
  try rewrite ->!mod_add_assoc;
  try rewrite <-!mod_add_assoc;
  (hrepeat do 1 first [rewrite !mod_addc_empty_l|rewrite !mod_addc_empty_r]);
  try(try (match goal with [|-_ (_,emp%I) _] => fail 2 end);
      eapply ctxr_cond_frameR_simpl).

Ltac _ctxr_swap :=
  try (rewrite mod_add_assoc; eapply ctxr_compose_hor_simplR; [|refl]);
  eapply ctxr_comm.

Ltac ctxr_swap :=
  ctxr_norm;
  etrans; [_ctxr_swap|];
  ctxr_norm.

Ltac ctxr_rotate :=
  ctxr_norm;
  (etrans; [eapply ctxr_comm|]);
  ctxr_norm.

Ltac ctxr_drop :=
  ctxr_norm;
  eapply ctxr_frameL.

Ltac ctxr_refl :=
  ctxr_norm;
  refl.

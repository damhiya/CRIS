From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import Mod.
Require Import MSimCommon ISim ISimFacts.
Require Import CtxRefine MainAdequacy.
Require Import Tactics TacticsInit.

(** Properties of contextual refinement *)
Section CtxRefineFacts.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Global Program Instance refines_mod_PreOrder : PreOrder (@refines_lmod).
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H. eapply H0. ss. Qed.

  Global Program Instance refines_PreOrder : PreOrder refines.
  Next Obligation.
    ii. esplits; eauto. ii. esplits; eauto. refl.
  Qed.
  Next Obligation.
    ii.
    edestruct H; eauto; edestruct H0; eauto. des.
    esplits; eauto. ii.
    specialize (H2 rs WFR SRC). des.
    specialize (H4 rt H2 H5). des. 
    exists rt0. esplits; eauto.
    etrans; eauto.
  Qed.

  Global Program Instance refines_Proper : Proper ((≡) ==> (≡) ==> iff) refines.
  Next Obligation.
    intros ms1 ms2 mseq mt1 mt2 mteq; split; intros CTXR.
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
    intros ms1 ms2 mseq mt1 mt2 mteq; split; intros CTXR.
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

  Lemma ctxr_refines mcs mct (REF : ctx_refines mcs mct) :
    refines mcs mct.
  Proof using.
    i. specialize (REF Mod.empty_mc).
    destruct mcs, mct. ss.
    rewrite -!mod_add_empty_r in REF.
    ii; split; ii; des; ss; red in REF; hexploit REF; eauto; i; des; ss.
    hexploit (H0 rs); ss.
    { rewrite SRC. iIntros ">[? ?]"; iFrame; et. }
    i; des; esplits; eauto.
    rewrite H2. iIntros ">[? [? ?]]". iFrame. et.
  Qed.

  (*** weakening for initial condition ***)
  Lemma ctxr_cond_strengthen (m : Mod.t) (P Q : iProp Σ) (IMPL : P ⊢ Q) :
    ctx_refines (m, P) (m, Q).
  Proof using.
    ii. ss; split; first done. ii; ss; exists rs. esplits; eauto.
    + rewrite SRC IMPL. et.
    + refl.
  Qed.

  (*** frame rule for initial condition ***)
  Lemma ctxr_cond_frameR (ms mt : Mod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms, Ps ∗ Q)%I (mt, Pt ∗ Q)%I.
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

  Lemma ctxr_cond_frameL (ms mt : Mod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms, Q ∗ Ps)%I (mt, Q ∗ Pt)%I.
  Proof using.
    etrans; [|etrans]; cycle 1.
    { apply ctxr_cond_frameR with (Q:=Q) in REF. apply REF. }
    { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
    { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
  Qed.

  (*** commutativity ***)
  Theorem ctxr_comm (ma mb : Mod.t) P:
    ctx_refines (Mod.add ma mb, P) (Mod.add mb ma, P).
  Proof using. rewrite Mod.add_comm //. Qed.

  (*** frame rules ***)
  Lemma ctxr_frameR ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
  Proof using.
    intro. specialize (REFA (Mod.add mc ctx.1, ctx.2)). ss.
    move: REFA; rewrite !mod_add_assoc; eauto.
  Qed.

  Lemma ctxr_frameL ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
  Proof using.
    etrans. { eapply ctxr_comm. }
    etrans. { eapply ctxr_frameR. apply REFA. }
    apply ctxr_comm.
  Qed.

  (*** horizontal composition ***)
  Lemma ctxr_compose_hor msa Psa mta Pta msb Psb mtb Ptb
      (REFA : ctx_refines (msa, Psa) (mta, Pta))
      (REFB : ctx_refines (msb, Psb) (mtb, Ptb)) :
    ctx_refines (msa ★ msb, Psa ∗ Psb)%I
                (mta ★ mtb, Pta ∗ Ptb)%I.
  Proof using.
    etrans.
    - eapply ctxr_frameR, ctxr_cond_frameR. apply REFA.
    - eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. 
  Qed.

  (*** mixed composition ***)
  Lemma ctxr_compose_mix msa Psa mta Pta msb Psb mtb Ptb mc
      (REFA : ctx_refines (msa ★ mc, Psa) (mta ★ mc, Pta))
      (REFB : ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb)) :
    ctx_refines (msa ★ msb ★ mc, Psa ∗ Psb)%I
                (mta ★ mtb ★ mc, Pta ∗ Ptb)%I.
  Proof using.
    etrans.
    { eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. }
    etrans.
    { eapply ctxr_frameL, ctxr_comm. }
    etrans.
    { rewrite <-mod_add_assoc.
      eapply ctxr_frameR, ctxr_cond_frameR. apply REFA. }
    rewrite mod_add_assoc.
    apply ctxr_frameL, ctxr_comm.
  Qed.

  (*** Corollaries for tactics ***)

  Corollary ctxr_compose_hor_simplR msa mta msb mtb P Pa
      (REFA : ctx_refines (msa, Pa) (mta, P))
      (REFB : ctx_refines (msb, emp%I) (mtb, emp%I)) :
    ctx_refines (msa ★ msb, Pa)%I
                (mta ★ mtb, P)%I.
  Proof using.
    rewrite (mod_addc_empty_r _ P) (mod_addc_empty_r _ Pa).
    eapply ctxr_compose_hor; et.
  Qed.

  Corollary ctxr_cond_frameR_simpl (ms mt : Mod.t) P Q
    (REF : ctx_refines (ms, P) (mt, emp%I))
    :
    ctx_refines (ms, P ∗ Q)%I (mt, Q)%I.
  Proof using.
    rewrite (mod_addc_empty_l _ Q).
    eapply ctxr_cond_frameR. et.
  Qed.
End CtxRefineFacts.

(** tactics for composing ctx_refines *)
Ltac ctxr_norm :=
  try rewrite <-!mod_add_assoc;
  try rewrite ->!mod_add_assoc;
  (hrepeat do 1 first [rewrite -!mod_addc_empty_l|rewrite -!mod_addc_empty_r]);
  try(try (match goal with [|-_ (_,emp%I)] => fail 2 end);
      eapply ctxr_cond_frameR_simpl).

Ltac _ctxr_swap :=
  try (rewrite -mod_add_assoc; eapply ctxr_compose_hor_simplR; [|refl]);
  eapply ctxr_comm.

Ltac ctxr_swap :=
  ctxr_norm;
  etrans; [|_ctxr_swap];
  ctxr_norm.

Ltac ctxr_rotate :=
  ctxr_norm;
  (etrans; [|eapply ctxr_comm]);
  ctxr_norm.

Ltac ctxr_drop :=
  ctxr_norm;
  eapply ctxr_frameL.

Ltac ctxr_refl :=
  ctxr_norm;
  refl.

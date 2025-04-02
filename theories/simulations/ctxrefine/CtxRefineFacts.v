From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import Mod HMod.
Require Import ModSim ModSimFacts ISim ISimInit ISimFacts.
Require Import CtxRefine MainAdequacy.

Global Program Instance refines_mod_PreOrder : PreOrder refines_mod.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H. eapply H0. ss. Qed.

Global Program Instance refines_PreOrder `{Σ : GRA} : PreOrder refines.
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

(*** vertical composition ***)
Global Program Instance ctx_refines_PreOrder `{Σ : GRA} : PreOrder ctx_refines.
Next Obligation. r. r. i. refl. Qed.
Next Obligation.
  r. r. i. etrans.
  - apply H.
  - apply H0.
Qed.

Global Program Instance ctx_refines_Proper `{Σ : GRA} : Proper ((≡) ==> (≡) ==> iff) (@ctx_refines Σ).
Next Obligation.
    intros Σ ms1 ms2 mseq mt1 mt2 mteq; split; intros CTXR.
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

Lemma ctxr_refines `{Σ : GRA} mcs mct (REF : ctx_refines mcs mct) :
  refines mcs mct.
Proof.
  i. specialize (REF HMod.empty_mc).
  destruct mcs, mct. ss.
  rewrite !hmod_add_empty_r in REF.
  ii; split; ii; des; ss; red in REF; hexploit REF; eauto; i; des; ss.
  hexploit (H0 rs); ss; first (iIntros "H"; iSplit; eauto; iApply SRC; eauto).
  i; des; esplits; eauto.
  iIntros "H". iPoseProof (H2 with "H") as "(? & _)". eauto.
Qed.

(*** weakening for initial condition ***)
Lemma ctxr_cond_strengthen `{Σ : GRA} (m : HMod.t) (P Q : iProp Σ) (IMPL : P -∗ Q) :
  ctx_refines (m, P) (m, Q).
Proof.
  ii. ss; split; first done. ii; ss; exists rs. esplits; eauto.
  + iIntros "H". iPoseProof (SRC with "H") as "(X & Y)".
    iFrame. iApply IMPL. eauto.
  + refl.
Qed.

(*** frame rule for initial condition ***)
Lemma ctxr_cond_frameR `{Σ : GRA} (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms, Ps ∗ Q)%I (mt, Pt ∗ Q)%I.
Proof.
  ii. specialize (REF (ctx.1, Q ∗ ctx.2)%I).
  destruct ctx. ss.
  split.
  { red in REF. hexploit REF; ss; i; des; eauto. }
  ii. ss. des. red in REF. hexploit REF; ss; i; des; eauto.
  hexploit (H0 rs); ss.
  { iIntros "H". iPoseProof (SRC with "H") as "((? & ?) & ?)".
    iFrame. }
  i; des; esplits; eauto.
  { iIntros "H". iPoseProof (H2 with "H") as "(? & (? & ?))".
    iFrame. }
Qed.

Lemma ctxr_cond_frameL `{Σ : GRA} (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms, Q ∗ Ps)%I (mt, Q ∗ Pt)%I.
Proof.
  etrans; [|etrans]; cycle 1.
  { apply ctxr_cond_frameR with (Q:=Q) in REF. apply REF. }
  { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
  { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
Qed.

(*** commutativity ***)
Theorem ctxr_comm `{Σ : GRA} (ma mb : HMod.t) P:
  ctx_refines (HMod.add ma mb, P) (HMod.add mb ma, P).
Proof.
  etrans.
  { eapply (ctxr_cond_strengthen _ _ ((emp ∗ P)%I)). eauto. }
  etrans.
  { eapply ctxr_cond_frameR, main_adequacy, hmod_add_comm. }
  eapply (ctxr_cond_strengthen _ _ P). i. iIntros "(H & H')". iFrame.
Qed.

(*** frame rules ***)
Lemma ctxr_frameR `{Σ : GRA} ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
Proof.
  intro. specialize (REFA (HMod.add mc ctx.1, ctx.2)). ss.
  move: REFA; rewrite !hmod_add_assoc; eauto.
Qed.

Lemma ctxr_frameL `{Σ : GRA} ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
Proof.
  etrans. { eapply ctxr_comm. }
  etrans. { eapply ctxr_frameR. apply REFA. }
  apply ctxr_comm.
Qed.

(*** horizontal composition ***)
Lemma ctxr_compose_hor `{Σ : GRA} msa Psa mta Pta msb Psb mtb Ptb
    (REFA : ctx_refines (msa, Psa) (mta, Pta))
    (REFB : ctx_refines (msb, Psb) (mtb, Ptb)) :
  ctx_refines (msa ★ msb, Psa ∗ Psb)%I
              (mta ★ mtb, Pta ∗ Ptb)%I.
Proof.
  etrans.
  - eapply ctxr_frameR, ctxr_cond_frameR. apply REFA.
  - eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. 
Qed.

(*** mixed composition ***)
Lemma ctxr_compose_mix `{Σ : GRA} msa Psa mta Pta msb Psb mtb Ptb mc
    (REFA : ctx_refines (msa ★ mc, Psa) (mta ★ mc, Pta))
    (REFB : ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb)) :
  ctx_refines (msa ★ msb ★ mc, Psa ∗ Psb)%I
              (mta ★ mtb ★ mc, Pta ∗ Ptb)%I.
Proof.
  etrans.
  { eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. }
  etrans.
  { eapply ctxr_frameL, ctxr_comm. }
  etrans.
  { rewrite <-hmod_add_assoc.
    eapply ctxr_frameR, ctxr_cond_frameR. apply REFA. }
  rewrite hmod_add_assoc.
  apply ctxr_frameL, ctxr_comm.
Qed.

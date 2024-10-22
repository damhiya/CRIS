Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton ModSimFacts.
Require Import PCM IPM HMod ISimCore ISimFacts.
Require Import ModSim MainAdequacy CtxRefine.

Section PROPERTIES.

  (*** refines_modsem ***)
  Global Program Instance refines_modsem_PreOrder : PreOrder refines_modsem.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H. eapply H0. ss. Qed.

  Context `{Σ : GRA.t}.

  Global Program Instance refines_PreOrder : PreOrder refines.
  Next Obligation.
    split.
    { rr. refl. }
    ii. exists rs. esplits; eauto. refl.
  Qed.
  Next Obligation.
    split.
    { rr. etrans. apply H. apply H0. }
    ii. destruct H, H0. des.
    hexploit (H1 sk).
    { etrans; eauto. } { eauto. } { eauto. } { eauto. } { eauto. }
    i. des.
    hexploit (H2 sk).
    { etrans; eauto. refl. } { eauto. } { eauto. } { eauto. } { eauto. }
    i; des.
    exists rt0. esplits; eauto.
    etrans; eauto.
  Qed.

  Lemma ctxr_refines mcs mct
    (REF : ctx_refines mcs mct)
    :
    refines mcs mct.
  Proof.
    i. specialize (REF HMod.empty_mc).
    destruct mcs, mct. ss.
    rewrite !hmod_add_empty_r in REF.
    destruct REF. split; eauto.
    ii. des. ss. hexploit H0; eauto.
    { iIntros "H". iSplit; eauto. iApply SRC. eauto. }
    i; des; esplits; eauto.
    iIntros "H". iPoseProof (H2 with "H") as "(? & _)". eauto.
  Qed.

  (*** vertical composition ***)
  
  Global Program Instance ctxr_PreOrder : PreOrder ctx_refines.
  Next Obligation.
    r. r. i. refl.
  Qed.
  Next Obligation.
    r. r. i. etrans.
    - apply H.
    - apply H0.
  Qed.
  
  (*** weakening for initial condition ***)

  Lemma ctxr_cond_strengthen (m : HMod.t) (P Q : Sk.t -> iProp)
    (IMPL : forall sk, P sk -∗ Q sk)
    :
    ctx_refines (m, P) (m, Q).
  Proof.
    split.
    - rr. refl.
    - ii. ss. exists rs. esplits; eauto.
      + iIntros "H". iPoseProof (SRC with "H") as "(X & Y)".
        iFrame. iApply IMPL. eauto.
      + refl.
  Qed.

  (*** frame rule for initial condition ***)

  Lemma ctxr_cond_frameR (ms mt : HMod.t) Ps Pt Q
    (REF : ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms, Ps ∗∗ Q)%I (mt, Pt ∗∗ Q)%I.
  Proof.
    ii. specialize (REF (ctx.1, HMod.addc Q ctx.2)).
    destruct ctx. unfold HMod.addc in *. ss.
    destruct REF. split; eauto.
    ii. ss. des. hexploit H0; eauto.
    { iIntros "H". iPoseProof (SRC with "H") as "((? & ?) & ?)".
      unfold HMod.addc. iFrame. }
    i; des. esplits; eauto.
    { iIntros "H". iPoseProof (H2 with "H") as "(? & (? & ?))".
      unfold HMod.addc. iFrame. }
  Qed.

  Lemma ctxr_cond_frameL (ms mt : HMod.t) Ps Pt Q
    (REF : ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms, Q ∗∗ Ps)%I (mt, Q ∗∗ Pt)%I.
  Proof.
    etrans; [|etrans]; cycle 1.
    { apply ctxr_cond_frameR with (Q:=Q) in REF. apply REF. }
    { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
    { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
  Qed.
  
  (*** commutativity ***)

  Theorem ctxr_comm (ma mb : HMod.t) P:
    ctx_refines (HMod.add ma mb, P) (HMod.add mb ma, P).
  Proof.
    etrans.
    { eapply (ctxr_cond_strengthen _ _ (fun sk => (emp ∗ P sk)%I)). eauto. }
    etrans.
    { eapply ctxr_cond_frameR, main_adequacy, hmod_add_comm. }
    eapply (ctxr_cond_strengthen _ _ P). i. iIntros "(H & H')". iFrame.
  Qed.

  (*** frame rules ***)

  Lemma ctxr_frameR ms Ps mt Pt mc
    (REFA : ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
  Proof.
    ii. specialize (REFA (HMod.add mc ctx.1, ctx.2)). ss.
    rewrite !hmod_add_assoc in *. eauto.
  Qed.

  Lemma ctxr_frameL ms Ps mt Pt mc
    (REFA : ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
  Proof.
    etrans. { eapply ctxr_comm. }
    etrans. { eapply ctxr_frameR. apply REFA. }
    apply ctxr_comm.
  Qed.

  (*** horizontal composition ***)

  Lemma ctxr_compose_hor msa Psa mta Pta msb Psb mtb Ptb
    (REFA : ctx_refines (msa, Psa) (mta, Pta))
    (REFB : ctx_refines (msb, Psb) (mtb, Ptb))
    :
    ctx_refines (msa ★ msb, Psa ∗∗ Psb)
                (mta ★ mtb, Pta ∗∗ Ptb).
  Proof.
    etrans.
    - eapply ctxr_frameR, ctxr_cond_frameR. apply REFA.
    - eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. 
  Qed.

  (*** mixed composition ***)

  Lemma ctxr_compose_mix msa Psa mta Pta msb Psb mtb Ptb mc
    (REFA : ctx_refines (msa ★ mc, Psa) (mta ★ mc, Pta))
    (REFB : ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb))
    :
    ctx_refines (msa ★ msb ★ mc, Psa ∗∗ Psb)
                (mta ★ mtb ★ mc, Pta ∗∗ Ptb).
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

End PROPERTIES.

Require Import Common.

Require Import Skeleton Mod HMod.
Require Import ModSim ModSimFacts ISimCore ISimFacts.
Require Import CtxRefine MainAdequacy.

Section CtxRefineFacts.
  Context `{Σ : GRA}.
  Notation iProp := (iProp Σ).

  Global Program Instance refines_modsem_PreOrder : PreOrder refines_modsem.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H. eapply H0. ss. Qed.

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
    hexploit (H1 sk); eauto.
    { etrans; eauto. }
    i. des.
    hexploit (H2 sk); eauto.
    i; des.
    exists rt0. esplits; eauto.
    etrans; eauto.
  Qed.

  (*** vertical composition ***)
  Global Program Instance ctx_refines_PreOrder : PreOrder ctx_refines.
  Next Obligation. r. r. i. refl. Qed.
  Next Obligation.
    r. r. i. etrans.
    - apply H.
    - apply H0.
  Qed.

  Global Program Instance ctx_refines_Proper : Proper ((≡) ==> (≡) ==> iff) (@ctx_refines Σ).
  Next Obligation.
    intros ms1 ms2 mseq mt1 mt2 mteq; split; intros CTXR;
      destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ss; clarify; econs; ss;
      specialize (CTXR ctx); inv CTXR; ss;
      intros sk rs skequiv wfsk wfrs rsimpl wfmod; hexploit (H1 sk rs); eauto.
    { iIntros "H"; iPoseProof (rsimpl with "H") as "[H1 H2]"; iSplitL "H1"; eauto; iApply H0; ss. }
    { i; des; esplits; eauto; iIntros "H"; iPoseProof (H4 with "H") as "[H1 H2]";
        iSplitL "H1"; eauto; iApply H2; ss. }
    { iIntros "H"; iPoseProof (rsimpl with "H") as "[H1 H2]"; iSplitL "H1"; eauto; iApply H0; ss. }
    { i; des; esplits; eauto; iIntros "H"; iPoseProof (H4 with "H") as "[H1 H2]";
        iSplitL "H1"; eauto; iApply H2; ss. }
  Qed.

  Lemma ctxr_refines mcs mct (REF : ctx_refines mcs mct) :
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

  (*** weakening for initial condition ***)
  Lemma ctxr_cond_strengthen (m : HMod.t) (P Q : Sk.t → iProp) (IMPL : ∀ sk, P sk -∗ Q sk) :
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
  Lemma ctxr_cond_frameR (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
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

  Lemma ctxr_cond_frameL (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
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
  Lemma ctxr_frameR ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
  Proof.
    ii. specialize (REFA (HMod.add mc ctx.1, ctx.2)). ss.
    move: REFA; rewrite !hmod_add_assoc; eauto.
  Qed.

  Lemma ctxr_frameL ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
  Proof.
    etrans. { eapply ctxr_comm. }
    etrans. { eapply ctxr_frameR. apply REFA. }
    apply ctxr_comm.
  Qed.

  (*** horizontal composition ***)
  Lemma ctxr_compose_hor msa Psa mta Pta msb Psb mtb Ptb
      (REFA : ctx_refines (msa, Psa) (mta, Pta))
      (REFB : ctx_refines (msb, Psb) (mtb, Ptb)) :
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
      (REFB : ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb)) :
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
End CtxRefineFacts.

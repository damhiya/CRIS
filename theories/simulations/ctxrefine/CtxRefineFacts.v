Require Import Common.
Require Import Mod HMod.
Require Import ModSim ModSimFacts ISimCore ISimFacts.
Require Import CtxRefine MainAdequacy.

Section CtxRefineFacts.
  Context `{Σ : GRA}.

  Global Program Instance refines_mod_PreOrder : PreOrder refines_mod.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H. eapply H0. ss. Qed.

  Global Program Instance refines_PreOrder : PreOrder refines.
  Next Obligation.
    ii. exists rs. esplits; eauto. refl.
  Qed.
  Next Obligation.
    ii.
    edestruct H; eauto. des.
    edestruct H0; eauto. des.
    exists x1. esplits; eauto.
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
      destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ss; clarify; ii;
      specialize (CTXR ctx); ss; hexploit (CTXR rs); eauto.
    { iIntros "H"; iPoseProof (SRC with "H") as "[H1 H2]"; iSplitL "H1"; eauto; iApply H0; ss. }
    { i. des; esplits; eauto. iIntros "H". iPoseProof (H1 with "H") as "[H1 H2]".
      iSplitL "H1"; eauto; iApply H2; ss. }
    { iIntros "H"; iPoseProof (SRC with "H") as "[H1 H2]"; iSplitL "H1"; eauto; iApply H0; ss. }
    { i; des; esplits; eauto. iIntros "H"; iPoseProof (H1 with "H") as "[H1 H2]".
        iSplitL "H1"; eauto; iApply H2; ss. }
  Qed.

  Lemma ctxr_refines mcs mct (REF : ctx_refines mcs mct) :
    refines mcs mct.
  Proof.
    i. specialize (REF HMod.empty_mc).
    destruct mcs, mct. ss.
    rewrite !hmod_add_empty_r in REF.
    ii. des. ss. red in REF. hexploit REF; eauto.
    { iIntros "H". iSplit; eauto. iApply SRC. eauto. }
    i; des; esplits; eauto.
    iIntros "H". iPoseProof (H0 with "H") as "(? & _)". eauto.
  Qed.

  (*** weakening for initial condition ***)
  Lemma ctxr_cond_strengthen (m : HMod.t) (P Q : iProp Σ) (IMPL : P -∗ Q) :
    ctx_refines (m, P) (m, Q).
  Proof.
    ii. ss. exists rs. esplits; eauto.
    + iIntros "H". iPoseProof (SRC with "H") as "(X & Y)".
      iFrame. iApply IMPL. eauto.
    + refl.
  Qed.

  (*** frame rule for initial condition ***)
  Lemma ctxr_cond_frameR (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms, Ps ∗ Q)%I (mt, Pt ∗ Q)%I.
  Proof.
    ii. specialize (REF (ctx.1, Q ∗ ctx.2)%I).
    destruct ctx. ss.
    ii. ss. des. red in REF. hexploit REF; eauto.
    { iIntros "H". iPoseProof (SRC with "H") as "((? & ?) & ?)".
      iFrame. }
    i; des. esplits; eauto.
    { iIntros "H". iPoseProof (H0 with "H") as "(? & (? & ?))".
      iFrame. }
  Qed.

  Lemma ctxr_cond_frameL (ms mt : HMod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms, Q ∗ Ps)%I (mt, Q ∗ Pt)%I.
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
    { eapply (ctxr_cond_strengthen _ _ ((emp ∗ P)%I)). eauto. }
    etrans.
    { eapply ctxr_cond_frameR, main_adequacy, hmod_add_comm. }
    eapply (ctxr_cond_strengthen _ _ P). i. iIntros "(H & H')". iFrame.
  Qed.

  (*** frame rules ***)
  Lemma ctxr_frameR ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
    ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
  Proof.
    intro. specialize (REFA (HMod.add mc ctx.1, ctx.2)). ss.
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
    ctx_refines (msa ★ msb, Psa ∗ Psb)%I
                (mta ★ mtb, Pta ∗ Ptb)%I.
  Proof.
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

(* Composition lemmas for w_ctx_refines *)
Section w_ctx_refines.
  Context `{Σ : GRA}.

  (* TODO : move to somewhere else *)
  Lemma pair_impl_subseteq (m : univ_id → HMod.t) (P Q : iProp Σ) :
    (Q ⊢ P) → (m, P) ⊆ (m, Q).
  Proof. by econs; ss. Qed.

  Definition w_ctx_refines (ms mt : HMod.pair) : Prop :=
    ∃ κ : positive,
      ∀ υ ν : univ_id, (υ >= ν + κ)%positive →
        ctx_refines (ms.1 υ, ms.2) (mt.1 ν, mt.2).
  Global Instance: Params (@w_ctx_refines) 1 := {}.

  Global Program Instance w_ctx_refines_PreOrder : Transitive w_ctx_refines.
  (* Next Obligation. rr; intros x; exists 0; intros ? ν H; rewrite Nat.add_0_r in H; inv H; done. Qed. *)
  Next Obligation.
    intros x y z [k1 H1] [k2 H2]; exists (k1 + k2)%positive; intros υ ν H; etrans.
    { apply (H1 _ (ν + k2)%positive); eauto; lia. }
    { apply H2; lia. }
  Qed.

  Global Program Instance w_ctx_refines_Proper : Proper ((≡) ==> (≡) ==> iff) (w_ctx_refines).
  Next Obligation.
    intros ms1 ms2 mseq mt1 mt2 mteq; split; intros [k CTXR]; exists k; intros υ ν H.
    { rewrite -(Pos2Nat.id υ) -(mseq (Pos.of_nat (Pos.to_nat υ))).
      rewrite -{1}(Pos2Nat.id ν) -(mteq _). apply CTXR. lia.
    }
    { rewrite -(Pos2Nat.id υ) (mseq (Pos.of_nat (Pos.to_nat υ))).
      rewrite -{1}(Pos2Nat.id ν) (mteq _). apply CTXR. lia. }
  Qed.

  Global Program Instance w_ctx_refines_subseteq : Proper ((⊆) ==> flip (⊆) ==> impl) w_ctx_refines.
  Next Obligation.
    intros [ms1 cs1] [ms2 cs2] Hssub [mt1 ct1] [mt2 ct2] Htsub [k REF]; exists k.
    intros u v Huv; hexploit REF; eauto; intros REF'; ss.
    inv Hssub; inv Htsub; ss; rewrite -H H1.
    etrans; first eapply ctxr_cond_strengthen.
    { iIntros "H"; iPoseProof (H0 with "H") as "H"; iExact "H". }
    { etrans; first eauto.
      eapply ctxr_cond_strengthen; iIntros "H"; iApply H2; iFrame.
    }
  Qed.

  (*** weakening for initial condition ***)
  Lemma w_ctx_refines_cond_weaken
      (m : univ_id → HMod.t) (mt : HMod.pair) (P Q : iProp Σ) (IMPL : P -∗ Q)
      (REF : w_ctx_refines (λ u, m u, Q) mt) :
    w_ctx_refines (λ υ, m υ, P) mt.
  Proof.
    eapply w_ctx_refines_subseteq; last eapply REF; ss.
    eapply pair_impl_subseteq; iIntros "H"; iApply IMPL; iFrame.
  Qed.

  Lemma w_ctx_refines_cond_strengthen
      (m : univ_id → HMod.t) (ms : HMod.pair) (P Q : iProp Σ) (IMPL : P -∗ Q)
      (REF : w_ctx_refines ms (λ u, m u, P)) :
    w_ctx_refines ms (λ υ, m υ, Q).
  Proof.
    eapply w_ctx_refines_subseteq; last eapply REF; ss.
    eapply pair_impl_subseteq; iIntros "H"; iApply IMPL; iFrame.
  Qed.

  (*** frame rule for initial condition ***)
  Lemma w_ctx_refines_cond_frameR
      (ms mt : univ_id → HMod.t) (Ps Pt Q : iProp Σ)
      (REF : w_ctx_refines (ms, Ps) (mt, Pt)) :
    w_ctx_refines (ms, Ps ∗ Q)%I (mt, Pt ∗ Q)%I.
  Proof.
    destruct REF as [k REF]; exists k; intros u v Huv; specialize (REF u v Huv).
    apply ctxr_cond_frameR; done.
  Qed.

  Lemma w_ctx_refines_cond_frameL
      (ms mt : univ_id → HMod.t) (Ps Pt Q :  iProp Σ)
      (REF : w_ctx_refines (ms, Ps) (mt, Pt)) :
    w_ctx_refines (ms, Q ∗ Ps)%I (mt, Q ∗ Pt)%I.
  Proof.
    destruct REF as [k REF]; exists k; intros u v Huv; specialize (REF u v Huv).
    apply ctxr_cond_frameL; done.
  Qed.
  
  (*** commutativity ***)
  (* Lemma w_ctx_refines_comm  (ma mb : univ_id → HMod.t) (P : univ_id → iProp Σ) :
    w_ctx_refines (λ υ, ((ma υ) ★ (mb υ), P υ)) (λ υ, ((mb υ) ★ (ma υ), P υ)).
  Proof.
    exists 0; intros u v Huv; rewrite Nat.add_0_r in Huv; inv Huv; apply ctxr_comm.
  Qed. *)

  (*** frame rules ***)
  Lemma w_ctx_refines_frameR ms Ps mt Pt mc
      (REF : w_ctx_refines (ms, Ps) (mt, Pt)) :
    w_ctx_refines ((λ υ, (ms υ) ★ mc), Ps) ((λ ν, (mt ν) ★ mc), Pt).
  Proof.
    destruct REF as [k REF]; exists k; intros u v Huv; specialize (REF u v Huv).
    apply ctxr_frameR; done.
  Qed.

  Lemma w_ctx_refines_frameL ms Ps mt Pt mc
      (REF : w_ctx_refines (ms, Ps) (mt, Pt)) :
    w_ctx_refines ((λ υ, mc ★ (ms υ)), Ps) ((λ ν, mc ★ (mt ν)), Pt).
  Proof.
    destruct REF as [k REF]; exists k; intros u v Huv; specialize (REF u v Huv).
    apply ctxr_frameL; done.
  Qed.

  (*** horizontal composition ***)
  Lemma w_ctx_compose_hor msa Psa mta Pta msb Psb mtb Ptb
      (REFA : w_ctx_refines (msa, Psa) (mta, Pta))
      (REFB : w_ctx_refines (msb, Psb) (mtb, Ptb)) :
    w_ctx_refines (λ υ, (msa υ) ★ (msb υ), Psa ∗ Psb)%I
                  (λ ν, (mta ν) ★ (mtb ν), Pta ∗ Ptb)%I.
  Proof.
    move: REFA REFB; case => k1 REFA; case => k2 REFB; exists (k1 + k2)%positive => u v Huv.
    apply ctxr_compose_hor; [apply REFA|apply REFB]; lia.
  Qed.

  (*** mixed composition ***)
  (* Lemma ctxr_compose_mix msa Psa mta Pta msb Psb mtb Ptb mc
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
  Qed. *)
End w_ctx_refines.

(* Section test.
  Context (A : Type).
  Context (R : A → A → Prop).
  Context (P : A → Prop).
  Context `{!Transitive R} `{!RewriteRelation R}.
  Context `{!Proper (flip R ==> impl) P}.
  Context (a b : A).
  Context `(R a b).
  (* Global Instance cmra_update_rewrite_relation :
  RewriteRelation (@cmra_update A) | 170 := {}. *)
  Goal P a.
    rewrite R0. rewrite -R0. *)
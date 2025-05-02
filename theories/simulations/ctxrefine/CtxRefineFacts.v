From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import Mod HMod.
Require Import ModSim ModSimFacts ISim ISimInit ISimFacts.
Require Import CtxRefine MainAdequacy.
Require Import Tactics TacticsInit.

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

(*** elimination of a module ***)
Lemma ctxr_elim_module `{Σ : GRA} m mc:
  ctx_refines (m, emp)%I (m ★ mc, emp)%I.
Proof.
  eapply main_adequacy with (Ist := IstProd (IstSB m.(HMod.scopes) IstEq) (IstSB mc.(HMod.scopes) IstTrue)).
  init_sim; s; eauto.
  { iIntros "_". unfold IstProd, IstSB, IstEq, IstTrue, state_scopes.
    iPureIntro. esplits; eauto using List.app_nil_r, HMod.well_scoped_init.
    ii. ss.
  }
  { eauto using sub_perm_remove_tail. }
  { rewrite List.map_app. eauto using sub_perm_remove_tail. }

  econs. s. erewrite alist_find_app; et. esplits; et.
  destruct fs as [sc bd].
  r. r. i. subst y. unfold HModTr.sandbox_body. s.
  generalize (bd x) as itr. clear x NODS NODD.
  combine_quant st_src; combine_quant st_tgt; combine_quant nths.
  eapply isim_coind.
  iIntros (g' [nths [st_tgt [st_ssrc itr]]] MON) "[#IST #CIH]". s.

  assert (CASE:= case_itrH itr). des; subst; s.
  - step; et.
  - steps_l. steps_r. by_coind "CIH"; et.
  - steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
  - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
  - destruct c; s; steps_l; steps_r.
    + call "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
    + step; et. steps_l. steps_r. by_coind "CIH"; et.
    + yield "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
  - destruct s; s.
    + rewrite SBRed.bind SBRed.put. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sput_src. iApply isim_sput_tgt. by_coind "CIH"; et.
      iDestruct "IST" as "%". des; subst. iPureIntro.
      eapply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      esplits; try rewrite alist_upd_not_tail; et; 
        try rewrite state_scopes_update; et.
      { ii. eapply NoDup_app_disjoint; try apply WFT.
        - eapply HMod.well_scoped_fns. unfold fnsems_scopes. erewrite FIND. eauto.
        - eapply H1. eapply in_map in H. rewrite List.map_map in H. et.
      }
      { ii. eapply NoDup_app_disjoint; try apply WFT.
        - eapply HMod.well_scoped_fns. unfold fnsems_scopes. erewrite FIND. eauto.
        - eapply H3. eapply in_map in H. rewrite List.map_map in H. et.
      }
    + rewrite SBRed.bind SBRed.get. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      iDestruct "IST" as "%". des; subst.
      eapply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      rewrite !alist_find_app_o.
      rewrite (alist_find_fst_notin _ x1); cycle 1.
      { ii. eapply NoDup_app_disjoint; try apply WFT.
        - eapply HMod.well_scoped_fns. unfold fnsems_scopes. erewrite FIND. eauto.
        - eapply H1. eapply in_map in H. rewrite List.map_map in H. et.
      }
      rewrite (alist_find_fst_notin _ x2); cycle 1.
      { ii. eapply NoDup_app_disjoint; try apply WFT.
        - eapply HMod.well_scoped_fns. unfold fnsems_scopes. erewrite FIND. eauto.
        - eapply H3. eapply in_map in H. rewrite List.map_map in H. et.
      }
      by_coind "CIH"; et.
      iPureIntro. esplits; eauto.
  - destruct e.
    + steps_r. force_l q. steps_l. by_coind "CIH"; et.
    + steps_l. force_r q. steps_r. by_coind "CIH"; et.
    + step. steps_l. steps_r. by_coind "CIH"; et.
Qed.

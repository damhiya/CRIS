Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics GSimAux.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff HelpingAux.

Ltac unfold_trans :=
  rewrite /ModTr.trans_fnsem /SB.sandbox_body
    /ModTr.trans /SModTr.trans_fnsem /SModTr.trans /=.

Section HelpingOnOff.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.
  (* sp, module name for the helping module *)
  Context (sp : specmap) (mn : string).
  Context {jobID retID : Type} (jobs : jobID → itree crisE retID).

  Definition mod_src := (HelpingOff.t mn jobs sp) ★ (CFilter.filter (Helping.exports mn) SchI.t).
  Definition mod_tgt := (HelpingOn.t mn jobs sp) ★ (CFilter.filter (Helping.exports mn) SchI.t).

  Local Lemma wf_src ctx : Mod.wf (mod_tgt ★ ctx) → Mod.wf (mod_src ★ ctx).
  Proof using.
    (* wf proof *)
    intros WF; ss.
    pose proof WF as WF1; eapply Mod.add_wf_inv in WF1 as [[? [? ?]]%Mod.add_wf_inv [? [Hdom ?]]].
    apply Mod.add_wf; eauto.
    { apply Mod.add_wf; eauto.
      { econs; ss.
        { rewrite /Mod.fnsems /HelpingOff.fnsems /= ?fmap_insert fmap_empty. mod_tac scope_solver. }
        { rewrite /HelpingOff.scopes; multiset_solver. }
      }
      { set_solver. }
      { multiset_solver. }
    }
    { clear -Hdom.
      intros ? a ?; eapply Hdom; [|done]; move: a.
      rewrite ?dom_union_with /=. set_solver.
    }
  Qed.

  Definition msk_ctx (msk : emask) : Prop :=
    (∀ k, msk _ (subevent _ (SGet k)) = true → k.1 ∉ SchI.scopes ∪ HelpingOn.scopes mn) ∧
    (∀ k v, msk _ (subevent _ (SPut k v)) = true → k.1 ∉ SchI.scopes ∪ HelpingOn.scopes mn).

  Notation prog_s ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOff.Mod mn jobs)
      ★ CFilter.filter (Helping.exports mn) (SMod.to_mod ∅ SchI.smod)) ★ ctx) rs)).
  Notation prog_t ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOn.Mod mn jobs sp)
      ★ CFilter.filter (Helping.exports mn) (SMod.to_mod ∅ SchI.smod)) ★ ctx) rs)).

  Definition run_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOff.run jobs x)))).
  Definition run_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOn.run mn jobs x)))).

  Definition help_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOff.help x)))).
  Definition help_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOn.help mn jobs sp x)))).

  Definition help_yield_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      (tau;; ⇓smod(sp) (fbody_trivial x))).
  Definition help_yield_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
      (tau;; ⇓smod(sp) ((λ arg, tid <- arg ↓?;; HelpingOn.try_run mn jobs tid;;; Ret ()↑) x))).

  Definition yield : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchI.yield x))).
  Definition inner_spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchI.inner_spawn x))).
  Definition spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchI.spawn x))).
  Definition join : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchI.join x))).
  Definition get_tid : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchI.get_tid x))).

  Local Lemma dom_helping_on :
    dom (Mod.fnsems (HelpingOn.t mn jobs sp)) = set_map Some (Helping.exports mn).
  Proof. set_solver. Qed.

  Local Lemma dom_helping_off :
    dom (Mod.fnsems (HelpingOff.t mn jobs sp)) = set_map Some (Helping.exports mn).
  Proof. set_solver. Qed.

  Lemma prog_s_run ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs (Helping.run mn) = Some run_s.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOff.fnsems; simpl_map; s; eauto.
  Qed.

  Lemma prog_t_run ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs (Helping.run mn) = Some run_t.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOn.fnsems; simpl_map; s; eauto.
  Qed.

  Lemma prog_s_help ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs (Helping.help mn) = Some help_s.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOff.fnsems; simpl_map; s; eauto.
  Qed.

  Lemma prog_t_help ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs (Helping.help mn) = Some help_t.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOn.fnsems; simpl_map; s; eauto.
  Qed.

  Lemma prog_s_yield ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.yield = Some yield.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_t_yield ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.yield = Some yield.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_s_inner_spawn ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr._spawn = Some inner_spawn.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_t_inner_spawn ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr._spawn = Some inner_spawn.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_s_spawn ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.spawn = Some spawn.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_t_spawn ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.spawn = Some spawn.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_s_join ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.join = Some join.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_t_join ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.join = Some join.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_s_get_tid ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.get_tid = Some get_tid.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_t_get_tid ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.get_tid = Some get_tid.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_r_2 //.
  Qed.

  Lemma prog_s_prog_t fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter (Helping.exports mn) SchI.t) ★ ctx) →
    (prog_s ctx rs fn = None ∧ prog_t ctx rs fn = None) ∨
    ((fn = Helping.run mn ∧ prog_s ctx rs fn = Some run_s ∧ prog_t ctx rs fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs fn = Some help_s ∧ prog_t ctx rs fn = Some help_t)) ∨
    (Some fn ∈ dom (Mod.fnsems SchI.t) ∧
      (∃ bd, prog_s ctx rs fn = Some (ModTr.trans_fnsem (SB.sandbox_body
        (CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)), bd)))) ∧
      prog_t ctx rs fn = prog_s ctx rs fn) ∨
    (Some fn ∈ dom (Mod.fnsems ctx) ∧
      prog_t ctx rs fn = prog_s ctx rs fn ∧
      (∃ msk bd, prog_s ctx rs fn = Some (ModTr.trans_fnsem (SB.sandbox_body (msk, bd))) ∧
        msk_ctx msk)).
  Proof using.
    intros Hwf; pose proof Hwf as Hwf2; apply Mod.add_wf_inv in Hwf2 as [Hwfl [Hwfctx [Hdisj ?]]].
    pose proof Hwfl as Hwftgt; apply Mod.add_wf_inv in Hwfl as [Hwfhelp [Hwfsch [Hdisj2 ?]]].
    apply wf_src in Hwf as Hwfsrc.
    destruct (decide (Some fn ∈ dom (Mod.fnsems (mod_tgt ★ ctx)))) as [Hfn|Hfn]; cycle 1.
    { left; split.
      { rewrite /LMod.prog Mod.to_lmod_fnsems not_elem_of_dom_1; first ss.
        revert Hfn; rewrite ?Mod.dom_fnsems_add dom_helping_off dom_helping_on //.
      }
      { rewrite /LMod.prog Mod.to_lmod_fnsems not_elem_of_dom_1; ss. }
    }
    right.
    rewrite ?Mod.dom_fnsems_add in Hfn; set_unfold in Hfn; destruct Hfn as [[Hfn|Hfn]|Hfn].
    { left; pose proof Hwfsrc as ?; apply Mod.add_wf_inv in Hwfsrc as [? [? ?]].
      des; clarify; [left|right]; split; auto; split;
        rewrite /LMod.prog Mod.to_lmod_fnsems; erewrite (lookup_fnsems_l); auto;
        try (erewrite lookup_fnsems_l; auto; s; rewrite /HelpingOff.fnsems /HelpingOn.fnsems;
          simpl_map; ss; fail); ss.
    }
    { pose proof Hwfsrc as ?; apply Mod.add_wf_inv in Hwfsrc as [? [? ?]].
      right; left; split; first by (des; clarify; set_solver).
      assert (Hfn2 : Some fn ∈ dom (Mod.fnsems (CFilter.filter (Helping.exports mn) SchI.t))).
      { des; clarify; set_solver. }
      clear Hfn.
      assert (Mod.fnsems ctx !! Some fn = None) by
        (rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj; eauto;
          rewrite Mod.dom_fnsems_add elem_of_union; right; done).
      assert (Mod.fnsems (HelpingOff.t mn jobs sp) !! Some fn = None).
      { rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj2; set_solver. }
      assert (Mod.fnsems (HelpingOn.t mn jobs sp) !! Some fn = None).
      { rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj2; eauto. }
      rewrite /LMod.prog ?Mod.to_lmod_fnsems ?(lookup_fnsems_None_r _ ctx) //.
      rewrite ?(lookup_fnsems_None_l) //; split; [|refl].
      set_unfold in Hfn2; des; clarify; simpl_map; eauto.
    }
    { right; right; split; first done.
      apply elem_of_dom in Hfn as [[[msk bd]|] Hfn]; cycle 1.
      { exfalso; inv Hwfctx; rewrite map_Forall_lookup in wf_fns;
          hexploit (wf_fns (Some fn) None); auto; by (intros []).
      }
      rewrite /LMod.prog ?Mod.to_lmod_fnsems; try repeat erewrite lookup_fnsems_r; eauto.
      esplits; eauto.
      eapply Mod.add_wf_inv in Hwf as [? [? [? ?]]].
      hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ (Some fn) (msk, bd)).
      rewrite lookup_omap Hfn => /(_ eq_refl) [? ?]; split.
      { i. multiset_solver. }
      { i. multiset_solver. }
    }
  Qed.

  Definition reqmap_rel
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (option retID * jobID))))
      (reqmap : gmap nat (option retID * jobID)) : Prop :=
    NoDup (omap id tl.*2).*1 ∧
    (∀ stid rid jid bo,
      (tl.*2 !! stid = Some (Some (rid, (bo, jid))) → reqmap !! rid = Some (bo, jid))) ∧
    (∀ rid jid, reqmap !! rid = Some (None, jid) →
      ∃ stid, tl.*2 !! stid = Some (Some (rid, (None, jid)))).

  Lemma reqmap_rel_id stid es0 es1 r tl reqmap :
    tl !! stid = Some (es0, r) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, r)]> tl) reqmap.
  Proof using.
    intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
    rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
    rewrite ?omap_app ?fmap_app; cbn; destruct r; eauto.
  Qed.

  Lemma reqmap_rel_Some tl reqmap stid rid b jid es :
    tl !! stid = Some (es, Some (rid, (b, jid))) →
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (b, jid).
  Proof using.
    rewrite /reqmap_rel; intros Hin [Hnodup [Hrel1 Hrel2]].
    apply (Hrel1 stid rid jid b). rewrite list_lookup_fmap Hin; eauto.
  Qed.

  Lemma reqmap_rel_Some_2 tl reqmap rid jid :
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (None, jid) →
    ∃ stid i_s i_t, tl !! stid = Some (i_s, i_t, Some (rid, (None, jid))).
  Proof using.
    rewrite /reqmap_rel; intros [? [? Hsome]] [stid Hstid]%Hsome; exists stid.
    apply list_lookup_fmap_inv in Hstid as [[[? ?] [[? [? ?]]|]] [? ?]]; ss.
    clarify; esplits; eauto.
  Qed.

  Lemma reqmap_rel_delete_true tl stid rid jid es0 es1 reqmap (ret : retID) :
    tl !! stid = Some (es0, Some (rid, (None, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (<[rid := (Some ret, jid)]> reqmap).
  Proof using.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app ?fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert // in Hstid1. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_true_2 tl stid rid jid es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (rid, (None, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, Some (rid, (Some ret, jid)))]> tl) (<[rid := (Some ret, jid)]> reqmap).
  Proof using.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      revert Hnodup; rewrite ?fmap_app ?omap_app ?fmap_app //; cbn.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert //= in Hstid1; clarify. rewrite lookup_insert //. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_false tl stid rid jid es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (rid, (Some ret, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (reqmap).
  Proof using.
    intros Hin [Hnodup [Hrel1 Hrel2]].
    split.
    { revert Hin; intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid' ??? Hstid'; eapply (Hrel1 stid'); eauto.
      rewrite list_fmap_insert /= in Hstid'.
      apply lookup_lt_Some in Hstid' as Hlen'. rewrite length_insert in Hlen'.
      destruct (decide (stid = stid')); subst.
      { rewrite list_lookup_insert // in Hstid'; ss. }
      rewrite list_lookup_insert_ne // in Hstid'.
    }
    intros ?? [stid' Hlookup]%Hrel2; exists stid'.
    rewrite list_fmap_insert /= list_lookup_insert_ne ?Hlookup //.
    ii; clarify.
    rewrite list_lookup_fmap Hin //= in Hlookup.
  Qed.

  Lemma reqmap_rel_insert_false tl reqmap rid jid ret :
    rid ∉ (dom reqmap) →
    reqmap_rel tl reqmap →
    reqmap_rel tl (<[rid:=(Some ret, jid)]> reqmap).
  Proof using.
    intros Hrid [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ???? Hstid%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify; apply elem_of_dom_2 in Hstid; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    ii; clarify.
  Qed.

  Lemma reqmap_rel_insert_true tl reqmap stid es0 es1 rid jid :
    rid ∉ (dom reqmap) →
    tl !! stid = Some (es0, None) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, Some (rid, (None, jid)))]> tl) (<[rid:=(None, jid)]> reqmap).
  Proof using Σ mn jobs.
    intros Hrid Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { rewrite insert_take_drop //.
      rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
      rewrite cons_app Permutation_app_swap_app.
      eapply take_drop_middle in Hin as Hmid; rewrite -Hmid in Hnodup; clear Hmid.
      revert Hnodup; rewrite ?fmap_app ?omap_app fmap_app; cbn.
      intros ?; apply NoDup_cons; split; eauto.
      rewrite -fmap_app -omap_app -fmap_app.
      intros [[? [? ?]] [? Hrid2]]%elem_of_list_fmap; ss; clarify.
      apply elem_of_list_omap in Hrid2 as [[[? [? ?]] |] [Hrid2 ?]]; ss; clarify.
      apply elem_of_list_fmap in Hrid2 as [[? [[? [? ?]] |]] [? Hrid2]]; ss; clarify.
      apply Hrid, elem_of_dom.
      assert (Hlem : (p, Some (n0, (o0, j0))) ∈ tl).
      { eapply take_drop_middle in Hin as Hmid; rewrite -Hmid; clear Hmid. set_solver. }
      apply elem_of_list_lookup in Hlem as [i Hlem].
      hexploit (Hrel1 i); cycle 1.
      { intros ->; ss. }
      rewrite list_lookup_fmap Hlem //.
    }
    split.
    { intros stid1 ? ? ?; destruct (decide (stid1 = stid)); subst.
      { rewrite list_lookup_fmap list_lookup_insert /=; i; clarify; rewrite lookup_insert //. }
      rewrite list_fmap_insert list_lookup_insert_ne //; intros Hcont%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify.
      apply Hrid, elem_of_dom; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    { ii; clarify. exists stid; rewrite list_fmap_insert list_lookup_insert // length_fmap //. }
    intros ? [??]%Hrel2; exists x; rewrite list_fmap_insert list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in H1; clarify.
  Qed.

  Lemma reqmap_rel_append tl reqmap es :
    reqmap_rel tl reqmap →
    reqmap_rel (tl ++ [(es, None)]) reqmap.
  Proof using.
    rewrite /reqmap_rel ?fmap_app ?omap_app ?fmap_app app_nil_r; cbn.
    intros [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ????; rewrite lookup_app_Some; intros [?%Hrel1|[??%list_lookup_singleton_Some]]; eauto.
      des; clarify.
    }
    { intros ?? [stid Hstid]%Hrel2; apply lookup_lt_Some in Hstid as Hlen.
      exists stid; rewrite lookup_app_l //.
    }
  Qed.

  Definition inner_spawn_pend (arg : Any.t) ktr : itree lmodE Any.t :=
    ⇓cris (x <- ⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (
        'arg : SAny.t <- (arg↓)?;;
        'x1 : thpool <- (cgetU SchI.v_ths);;
        'x2 : nat <- (cgetU SchI.v_tid);;
        r <-
          (match x1 !! x2 with
          | Some (stid, _) =>
              cput SchI.v_ths (<[x2 := (stid, Some arg)]> x1);;;
              Sch.terminate
          | None => triggerUB
          end);;
        Ret (r↑)));;
      ktr x).

  Definition join_pend (arg : Any.t) jtid ktr : itree lmodE Any.t :=
    ⇓cris (x <- ⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (
        'arg : () <- (arg↓)?;;
        x_3 <- iterC (λ _ : (),
          'x_1 : thpool <- cgetU SchI.v_ths;;
          match x_1 !! jtid with
          | Some (_, Some rv) => Ret (inr (Some rv))
          | Some (_, None) =>
              '() : _ <- ccallU SchHdr.yield tt;; Ret (inl ())
          | None => Ret (inr None)
          end
        ) ();;
        Ret (x_3↑)));; ktr x).

  Definition helpee_pend_s
      (j : jobID) k
      (fspo : option fspec_rel) x_fsp
      : itree lmodE Any.t :=
    ⇓cris (tau;; r <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
      HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x_fsp (()↑);;;
      ret <- ⇓smod(sp) (𝒴;;; r <- SB.sandbox (HelpingOn.msk_pure) (jobs j);; 𝒴;;; Ret r↑);;
      (* vret <- trigger (Choose Any.t);;
      trigger (Guarantee (postcond fspec_trivial () ret vret));;; *)
      Ret ret
    );; k r).

  Definition helpee_pend_t
      (tid_stid_cur : nat) (j : jobID)
      (fspo : option fspec_rel) x_fsp k
      : itree lmodE Any.t :=
    ⇓cris (tau;; x_ <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      x <- ⇓smod(sp) (𝒴;;; r <- HelpingOn.try_run mn jobs tid_stid_cur;; 𝒴;;; Ret r↑);;
      (* vret <- trigger (Choose Any.t);;
      trigger (Guarantee (postcond fspec_trivial () x vret));;; *)
      Ret x
    );; k x_).

  Inductive help_rel : itree lmodE Any.t → itree lmodE Any.t → option (nat * (option retID * jobID)) → Prop :=
  | help_rel_ret ret : help_rel (Ret ret) (Ret ret) None
  | help_rel_eq itr_s itr_t ktr_s ktr_t itr msk :
      itr_s = ⇓cris (x <- SB.sandbox msk itr;; ktr_s x) →
      itr_t = ⇓cris (x <- SB.sandbox msk itr;; ktr_t x) →
      msk_ctx msk →
      (∀ ret, itr ≠ Ret ret) →
      (∀ (ret : Any.t), help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_loop itr_s itr_t ktr_t ktr_s x (ret : Any.t) :
      itr_t = (
        ⇓cris (tau;;
          x_ <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
            (HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x (()↑);;;
            ⇓smod(sp) (𝒴);;;
            (* vret <- trigger (Choose Any.t);;
            trigger (Guarantee (postcond fspec_trivial () ret vret));;; *)
            Ret ret);;
          ktr_t x_)) →
      itr_s = (
        ⇓cris (tau;;
          x_ <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
            (HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x (()↑);;;
            ⇓smod(sp) (𝒴);;;
            (* vret <- trigger (Choose Any.t);;
            trigger (Guarantee (postcond fspec_trivial () ret vret));;; *)
            Ret ret);;
          ktr_s x_)) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_helpee_done tid jid itr_s itr_t ktr_s ktr_t x ret :
      itr_t = helpee_pend_t tid jid (sp !! speckey_fn SchHdr.yield) x ktr_t →
      itr_s = (
        ⇓cris (tau;;
          x_ <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
            (HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x (()↑);;;
            ⇓smod(sp) (𝒴);;;
            (* vret <- trigger (Choose Any.t);;
            trigger (Guarantee (postcond fspec_trivial () ret↑ vret));;; *)
            Ret ret↑);;
          ktr_s x_)) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t (Some (tid, (Some ret, jid)))
  | help_rel_helpee_pend tid jid itr_s itr_t k_s k_t x_fsp :
      itr_s = helpee_pend_s jid k_s (sp !! speckey_fn SchHdr.yield) x_fsp →
      itr_t = helpee_pend_t tid jid (sp !! speckey_fn SchHdr.yield) x_fsp k_t →
      (∀ ret, help_rel (⇓cris (k_s ret)) (⇓cris (k_t ret)) None) →
      help_rel itr_s itr_t (Some (tid, (None, jid)))
  | help_rel_call itr_s itr_t ktr_t ktr_s ctx rs fn arg :
      Some fn ∈ dom (Mod.fnsems (HelpingOn.t mn jobs sp)) ∪ dom (Mod.fnsems SchI.t) →
      Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter (Helping.exports mn) SchI.t) ★ ctx) →
      (* prog_s ctx rs fn = Some (ModTr.trans_fnsem ktr_s) →
      prog_t ctx rs fn = Some (ModTr.trans_fnsem ktr_t) → *)
      itr_s = bd <- (prog_s ctx rs fn)?;; x <- bd arg;; ⇓cris (ktr_s x) →
      itr_t = bd <- (prog_t ctx rs fn)?;; x <- bd arg;; ⇓cris (ktr_t x) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_inner_spawn itr_s itr_t (arg : Any.t) ktr_s ktr_t :
      itr_t = inner_spawn_pend arg ktr_t →
      itr_s = inner_spawn_pend arg ktr_s →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_join itr_s itr_t (arg : Any.t) ktr_s ktr_t tid :
      itr_t = join_pend arg tid ktr_t →
      itr_s = join_pend arg tid ktr_s →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_terminate itr_s itr_t ktr_s ktr_t :
      itr_s =
        (⇓cris (x <- ⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
          (⇓smod(∅) (x_ <- Sch.terminate;; Ret x_↑));; ktr_s x)) →
      itr_t =
        (⇓cris (x <- ⇓sb(CFilter.msk_filter (Helping.exports mn) (msk_real (msk_scp SchI.scopes msk_true)))
          (⇓smod(∅) (x_ <- Sch.terminate;; Ret x_↑));; ktr_t x)) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None.

  Lemma gsim_Yield_tgt r g RR p_s p_t tid_s tid_t tp_s tp_t
      scp (k_s k_t : itree crisE _) ctx st_ctx rs
      (ths : list (nat * option SAny.t))
      (mtid_s mtid_t : nat)
      (res : Σ)
      (reqmap : gmap nat (option retID * jobID)) :
    Mod.wf (mod_src ★ ctx) →
    Mod.wf (mod_tgt ★ ctx) →
    let st_src (ths : list (nat * option SAny.t)) (mtid_s : nat) :=
      (union_with (λ _ _, Some None)
        {[SchI.v_ths := Some ths↑; SchI.v_tid := Some mtid_s↑]}
          st_ctx) in
    let st_tgt (reqmap : gmap nat (option retID * jobID)) (ths : list (nat * option SAny.t)) (mtid_t : nat) :=
      (union_with (λ _ _, Some None)
        (union_with (λ _ _, Some None)
          {[HelpingOn.v_reqs mn := Some reqmap↑]}
          {[SchI.v_ths := Some ths↑; SchI.v_tid := Some mtid_t↑]})
        st_ctx) in
    map_Forall (const is_Some) (st_src ths mtid_s) →
    map_Forall (const is_Some) (st_tgt reqmap ths mtid_t) →
    ✓ res →
    tp_s !! tid_s = Some (⇓cris ((⇓sb(msk_scp scp msk_true) (⇓smod(sp) (𝒴)));;; k_s)) →
    tp_t !! tid_t = Some (⇓cris ((⇓sb(msk_scp scp msk_true) (⇓smod(sp) (𝒴)));;; k_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s:=⇓cris (⇓sb( msk_scp scp msk_true) (⇓smod(sp) 𝒴);;; k_s)]> tp_s))
        (Any.pair (ModTr.state_encode (st_src ths mtid_s)) res↑))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs)) (tid_t, <[tid_t:=⇓cris k_t]> tp_t))
        (Any.pair
          (ModTr.state_encode (st_tgt reqmap ths mtid_t)) res↑)) →
    (ths.*1 !! mtid_s = Some tid_s →
      ths.*1 !! mtid_t = Some tid_t ∧
      ∀ mtid_t1 stid_t1, ths.*1 !! mtid_t1 = Some stid_t1 →
        ∃ mtid_s1 stid_s1, ths.*1 !! mtid_s1 = Some stid_s1 ∧
        ∀ x (res2 : Σ),
        ✓ res2 →
        gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (prog_s ctx rs))
            (stid_s1, <[tid_s:=⇓cris (tau;;
              ⇓sb(msk_scp scp msk_true)
                (HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x ()↑;;;
                 ⇓smod(sp) 𝒴);;; k_s)]> tp_s))
          (Any.pair (ModTr.state_encode (st_src ths mtid_s1)) res2↑))
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (prog_t ctx rs))
            (stid_t1, <[tid_t:=⇓cris (tau;;
              ⇓sb(msk_scp scp msk_true)
                (HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) x ()↑;;;
                 ⇓smod(sp) 𝒴);;; k_t)]> tp_t))
          (Any.pair
            (ModTr.state_encode (st_tgt reqmap ths mtid_t1)) res2↑))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, tp_s))
        (Any.pair (ModTr.state_encode (st_src ths mtid_s)) res↑))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, tp_t))
        (Any.pair (ModTr.state_encode (st_tgt reqmap ths mtid_t)) res↑)).
  Proof using.
    intros Hwfsrc Hwftgt. revert res p_s p_t tp_s tp_t.
    gcofix CIH.
    intros res p_s p_t tp_s tp_t Hst1 Hst2 Hres Htids Htidt ? Hk2.
    eapply lookup_lt_Some in Htids as ?, Htidt as ?.
    revert Htids Htidt; rewrite yield_unfold; intros Htids Htidt.
    eapply gsim_tau_tgt; [rewrite Htidt; do 2 f_equal; hnorm_itr|].
    eapply gsim_tau_src; [rewrite Htids; do 2 f_equal; hnorm_itr|].
    eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    intros [[|]|]; rewrite list_insert_insert; cycle 1.
    { ghnorm_r.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (Some false). ghnorm_l. rewrite list_insert_insert.
      zprogress. gbase.
      eapply CIH; (try by lookup_tac); auto; rewrite ?list_insert_insert //.
      intros temp; specialize (Hk2 temp) as [? Hk2]; split; first done.
      intros temp1 temp2 temp3; specialize (Hk2 temp1 temp2 temp3) as [? [? [? ?]]].
      esplits; eauto.
      ii; rewrite ?list_insert_insert //; eauto.
    }
    { ghnorm_r.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (Some false). ghnorm_l. rewrite list_insert_insert.
      eapply gpaco7_mon; eauto.
    }
    eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    exists (Some true). rewrite list_insert_insert. ired.
    rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghnorm_l. rewrite list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghnorm_r. rewrite list_insert_insert.
    eapply gsim_HoareCall_prologue_both; (try by lookup_tac; s; do 2 f_equal; hnorm_itr); auto.
    intros res1 x Hres1. rewrite ?list_insert_insert. ghnorm_l; ghnorm_r.

    eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert. ghnorm_l.
    eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert. ghnorm_r.

    rewrite prog_s_yield // prog_t_yield //=.
    rewrite /yield /SchI.yield /cfunU; ired; rewrite -?interpV_bind.
    ghnorm_l; ghnorm_r.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghnorm_l. rewrite list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghnorm_r. rewrite list_insert_insert.
    destruct Any.downcast as [[]|]; s; cycle 1.
    { ghnorm_l. destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
      eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
    }
    ghnorm_l; ghnorm_r.

    eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    subst st_tgt; match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
    ghnorm_r. hss. ghnorm_r.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert. ghnorm_r.
    case_decide as temp; [set_solver +temp|]; s; clear temp.

    eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    subst st_src; match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
    ghnorm_l. hss. ghnorm_l.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert. ghnorm_l.
    case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.

    ghnorm_l; ghnorm_r.
    eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_l.
    eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_r.

    eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
    ghnorm_r. hss. ghnorm_r.

    eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
    ghnorm_l. hss. ghnorm_l.

    destruct (ths !! mtid_s) as [[? ?]|] eqn : Hthss; rewrite Hthss; cycle 1.
    { ghnorm_l. destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
      eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
    }
    case_decide; subst; cycle 1.
    { ghnorm_l. destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
      eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
    }
    hexploit Hk2; [rewrite list_lookup_fmap Hthss //|]; clear Hk2.
    intros [[[? ?] [Hthst ?]]%list_lookup_fmap_Some Hk2]; rewrite Hthst /=; clarify; s.
    case_decide; ss. ghnorm_r. ghnorm_l.

    eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    intros [[mtid_t1 stid_t1] Hmtid_t1]; rewrite list_insert_insert. ghnorm_r; ss.

    hexploit (Hk2 mtid_t1 stid_t1); eauto. clear Hk2; intros [mtid_s1 [stid_s1 [Hmtid_s1 Hk2]]].
    eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    eexists (exist _ (mtid_s1, stid_s1) Hmtid_s1); rewrite list_insert_insert. ghnorm_l.

    eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_r.
    eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_l.
    eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_l.
    eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_r.
    case_decide as temp; [set_solver +temp|]; s; clear temp. ghnorm_l; ghnorm_r.

    eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_l.
    eapply gsim_Yield_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghnorm_r. ired.
    repeat match goal with
    | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
      state_insert_simpl k1 v1 H
    end.
    eapply gpaco7_mon; [greplace_l; [|greplace_r]| | ]; cycle 2.
    { eapply (Hk2 x.1 res1); eauto. }
    { eauto. }
    { eauto. }
    { repeat f_equal; ss. extensionality a. hnorm_itr. }
    { repeat f_equal; ss. extensionality a. hnorm_itr. }
  (*SLOW*)Qed.

  Lemma helping_onoff_correct :
    ctx_refines (mod_src, emp%I) (mod_tgt, emp%I).
  Proof using.
    rewrite /mod_src /mod_tgt.
    intros [ctx ctxP] WF; ss; split; first by apply wf_src.

    (* simulation proof *)
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].
    intro arg; eapply (gsim_adequacy); repeat (instantiate (1:=smj_bot)).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    destruct (Mod.fnsems ctx !! None) as [[[msk bd]|]|] eqn : FIND; cycle 1.
    { simpl_map; ss. ginit. gstep_l. ss. }
    { rewrite {1}/Mod.fnsems {1}/Mod.add; simpl_map by eauto; rewrite lookup_union_with FIND.
      rewrite lookup_fnsems_None //. ginit. gstep_l. ss.
    }

    simpl_map; s. ired.
    rewrite /SB.sandbox_body /ModTr.trans_fnsem /ModTr.trans /=.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }

    (* Start coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    rewrite left_id_L.
    set (st_src := union_with _ _ _) at 1.
    set (st_tgt := union_with _ _ _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (option retID * jobID))))
        (mtid stid : nat) (ths : list (nat * option SAny.t)) st_ctx
        (reqmap : gmap nat (option retID * jobID)),
          st_src = union_with (λ _ _, Some None)
            {[SchI.v_ths := Some ths↑; SchI.SchI.v_tid := Some mtid↑]}
            st_ctx ∧
          st_tgt = union_with (λ _ _, Some None)
            (union_with (λ _ _, Some None)
              {[HelpingOn.v_reqs mn := Some reqmap↑]}
              {[SchI.v_ths := Some ths↑; SchI.SchI.v_tid := Some mtid↑]})
            st_ctx ∧
          tp_src = (stid, (fst ∘ fst <$> tl)) ∧ tp_tgt = (stid, (snd ∘ fst <$> tl)) ∧
          reqmap_rel tl reqmap ∧
          (∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) →
            help_rel itr_s itr_t no ∧
            match no with
            | Some _ => ∃ stid_i ro_i, ths !! stid_i = Some (i, ro_i)
            | None => True
            end) ∧
          map_Forall (const is_Some) st_src ∧ map_Forall (const is_Some) st_tgt); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { rr; ss; split; first econs.
        split; [intros ????; rewrite ?list_lookup_singleton_Some; i; des; clarify|].
        intros ??; rewrite lookup_empty; i; clarify.
      }
      { intros ???? [-> In]%list_lookup_singleton_Some; clarify; split; last done.
        { ides (bd ()↑).
          { by rewrite ?SBRed.ret ?interpV_ret; econs. }
          { eapply (help_rel_eq _ _ (λ x, Ret x) (λ x, Ret x)); eauto; try by grind.
            { eapply Mod.add_wf_inv in WF as [? [? [? ?]]].
              hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ None (msk, bd)).
              rewrite lookup_omap FIND => /(_ eq_refl) [? ?]; split.
              { i. multiset_solver. }
              { i. multiset_solver. }
            }
            { by i; rewrite ?interpV_ret; econs. }
          }
          { eapply (help_rel_eq _ _ (λ x, Ret x) (λ x, Ret x)); eauto; try by grind.
            { eapply Mod.add_wf_inv in WF as [? [? [? ?]]].
              hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ None (msk, bd)).
              rewrite lookup_omap FIND => /(_ eq_refl) [? ?]; split.
              { i. multiset_solver. }
              { i. multiset_solver. }
            }
            { by i; rewrite ?interpV_ret; econs. }
          }
        }
      }
      { apply wf_src in WF; inv WF; hexploit (Mod.nodup_init); eauto. }
      { inv WF; hexploit (Mod.nodup_init); eauto. }
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    generalize smj_bot at 1 as f_s. generalize smj_bot as f_t.
    clear st_src st_tgt tp_src tp_tgt FIND arg msk bd.
    revert_until WF.
    gcofix CIH.
    intros rs Hrs f_s f_t st_s st_t tp_s tp_t.
    intros [tl [mtid [stid [ths [st_ctx [reqmap temp]]]]]].
    destruct temp as [-> [-> [-> [-> [Hreqmap [Hlookup [Hst1 Hst2]]]]]]].

    destruct ((fst ∘ fst <$> tl) !! stid) as [i|] eqn : Htid; cycle 1.
    { giter_l. s. rewrite Htid. gstep_l. gnorm_l. gstep_l. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    destruct no as [[n [[retid|] j]]|].

    { (* Done Helpee *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.

      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      eapply gsim_HoareCall_epilogue_both;
        (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
      intros res1 x1 Hres1; rewrite ?list_insert_insert.

      eapply gsim_Yield_tgt; (eauto using wf_src);
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
      { rewrite !list_insert_insert.
        rewrite /HelpingOn.try_run.
        ghnorm_r.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.
        eapply reqmap_rel_Some in Hreqmap as Hsome; eauto. rewrite Hsome; clear Hsome. ghnorm_r.

        eapply gsim_Yield_tgt; (eauto using wf_src);
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
        { rewrite !list_insert_insert.
          ghnorm_r.
          rewrite {1}yield_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghnorm_l.
          zprogress. gbase. eapply (CIH res1); eauto.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_delete_false; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }

        intros; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros x2 res2 Hres2.
        rewrite !list_insert_insert.
        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 Hst1
        end.
        intros Hst1'; eauto.

        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 Hst2
        end.
        intros Hst2'; eauto.

        zprogress. gbase. eapply (CIH res2); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_false; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_loop with (ret:=retid↑); eauto.
            { f_equal. grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            { f_equal. grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
          }
        }
      }

      intros; split; first done.
      intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
      intros x2 res2 Hres2.
      rewrite !list_insert_insert.
      eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 Hst1
      end.
      intros Hst1'; eauto.

      eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst2 as Hst2'; revert Hst2'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 Hst2
      end.
      intros Hst2'; eauto.

      zprogress. gbase. eapply (CIH res2); try by des.

      eexists (<[stid := (_, _, (Some (n, (Some _, j))))]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; ss. esplits; eauto.
          eapply help_rel_helpee_done; eauto.
          { rewrite /helpee_pend_t; repeat f_equal; grind.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          { rewrite /helpee_pend_t; repeat f_equal; grind.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          { apply list_lookup_fmap_Some in H1 as [[? ?] [? ->]]; eauto. }
        }
      }
    }

    { (* Pending helpee *)
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.
      revert Htid; rewrite /helpee_pend_s /helpee_pend_t; intros Htid.

      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      eapply gsim_HoareCall_epilogue_both;
        (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
      intros res1 x1 Hres1; rewrite ?list_insert_insert.

      eapply gsim_Yield_tgt; (eauto using wf_src);
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
      { (* tired of waiting *)
        rewrite !list_insert_insert.

        rewrite /HelpingOn.try_run. ghnorm_r.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.
        eapply reqmap_rel_Some in Hreqmap as Hsome; eauto. rewrite Hsome; clear Hsome. ghnorm_r.

        rewrite {1}yield_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
        rewrite list_insert_insert. ghnorm_l.

        zprogress with smj_bot smj_bot _ _.
        eapply gsim_jobs_both; try by rewrite ?length_insert ?length_fmap.
        intros res2 ret2 Hres2.
        ghnorm_r.

        eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_r.
        eapply map_Forall_insert_union_with with (k:=HelpingOn.v_reqs mn) in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2'.

        eapply gsim_Yield_tgt; (eauto using wf_src);
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
        { rewrite !list_insert_insert.
          ghnorm_r.
          rewrite {1}yield_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghnorm_l.

          zprogress.
          gbase. eapply (CIH res2); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_delete_true; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }

        intros; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros x3 res3 Hres3.
        rewrite !list_insert_insert.

        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.

        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst2' as Hst2''; revert Hst2''.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2''.

        zprogress. gbase. eapply (CIH res3); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_true; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply help_rel_loop with (x:=x3); eauto; ss.
            { f_equal. grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            { f_equal. grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
          }
        }
      }

      intros; split; first done.
      intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
      intros x3 res3 Hres3.
      rewrite !list_insert_insert.

      eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hst1'.

      eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst2 as Hst2'; revert Hst2'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hst2'.

      zprogress. gbase. eapply (CIH res3); eauto.
      eexists (<[stid := (_, _, Some (n, (_, j)))]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split.
          { eapply (help_rel_helpee_pend n j); eauto.
            { rewrite /helpee_pend_s.
              instantiate (1:=x3). repeat f_equal.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            { rewrite /helpee_pend_t. f_equal.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
          }
          { apply list_lookup_fmap_Some in H1 as [[? ?] [? ->]]; eauto. }
        }
      }
    }


    (* Non-helpee case *)
    apply lookup_lt_Some in Htid as Hstid_cur_length.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [Hcase _].
    inv Hcase; cycle 1.

    { (* event from ctx *)
      rename itr into itr_c.
      ides itr_c.
      { (* ret *)
        congruence.
      }
      { (* tau *)
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        zprogress.
        gbase. eapply CIH; eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            ides t; try by eapply help_rel_eq; eauto.
            by rewrite ?SBRed.ret; ired.
          }
        }
      }
      (* events *)
      rewrite SBRed.vis in Htid; destruct msk eqn : Hmsk; cycle 1.
      { eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|ss]. }
      destruct e as [e|[e|[e|e]]]; rewrite vis_trigger in Htid.
      { (* agE *)
        destruct e as [P|x|Q].
        { (* Assume *)
          eapply gsim_Assume_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros r_s2 Hr_s2.
          eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists r_s2; splits; try by des.
          zprogress.
          gbase. eapply (CIH r_s2); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* AssumeRes *)
          eapply gsim_AssumeRes_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros Hx.
          eapply gsim_AssumeRes_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            split; first done.
          zprogress.
          gbase. eapply (CIH (x ⋅ rs)); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* Guarantee *)
          eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros res2 Hres2.
          eapply gsim_Guarantee_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            esplits; try by des.
          zprogress.
          gbase. eapply (CIH (res2)); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
      }
      { (* callE *)
        destruct e as [fn args| | | ].
        { (* call *)
          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          zprogress.
          hexploit (prog_s_prog_t fn ctx rs); eauto; intros [[-> ->]|Hprog].
          { s; giter_l. ired. rewrite list_lookup_insert /=. gstep_l; done.
            rewrite length_fmap //.
          }
          gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; auto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              destruct Hprog as [Hprog|Hprog].
              { eapply help_rel_call; eauto.
                { des; clarify; rewrite elem_of_union; left; set_unfold; [left|right]; done. }
                { i; ired; rewrite -?bind_tau -?SBRed.tau. eapply help_rel_eq; auto. }
              }
              destruct Hprog as [Hprog|Hprog].
              { eapply help_rel_call; eauto.
                { des; clarify; rewrite elem_of_union; right; done. }
                { i; ired; rewrite -?bind_tau -?SBRed.tau. eapply help_rel_eq; auto. }
              }
              destruct Hprog as [? [-> [msk1 [bd1 [-> ?]]]]]; s; unfold_trans; ired.
              rewrite -?interpV_bind.
              ides (bd1 args).
              { rewrite ?SBRed.ret; ired. rewrite -?bind_tau -?SBRed.tau.
                eapply help_rel_eq; eauto.
              }
              { eapply help_rel_eq; eauto.
                ss. grind. rewrite -?bind_tau -!SBRed.tau; eapply help_rel_eq; eauto.
              }
              { eapply help_rel_eq; eauto.
                ss. grind. rewrite -?bind_tau -!SBRed.tau; eapply help_rel_eq; eauto.
              }
            }
          }
        }
        { (* spawn *)
          eapply gsim_Spawn_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_Spawn_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          hexploit (prog_s_prog_t fn ctx rs); eauto; intros [[-> ?]|Hprog]; s.
          { s. gstep_l; done. }
          assert (Htemp : ∃ bds bdt, prog_s ctx rs fn = Some (λ x, ⇓cris (bds x)) ∧
            prog_t ctx rs fn = Some (λ x, ⇓cris (bdt x))).
          { des; esplits; eauto; rewrite ?Hprog1 ?Hprog0 //. }
          destruct Htemp as [bds [bdt [Hprog1 Hprog2]]]; rewrite Hprog1 Hprog2; s; ired.
          zprogress. gbase.
          eapply (CIH rs); try by des.
          eexists ((<[stid := (_, _, None)]> tl) ++ [(_, _, None)]); ss.
          esplits; eauto.
          { rewrite ?fmap_app list_fmap_insert //=. }
          { rewrite ?fmap_app list_fmap_insert //=. }
          { eapply reqmap_rel_append; eauto.
            eapply reqmap_rel_id; eauto.
          }
          { intros i; destruct (decide (i = length tl)); subst.
            { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
              rewrite Nat.sub_diag /=; intros Heq; inv Heq.
              split; ss.
              destruct Hprog as [Hprog|Hprog].
              { eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a) ctx rs fn args); eauto.
                { rewrite elem_of_union; left; des; subst; set_unfold; auto. }
                { rewrite Hprog1 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { rewrite Hprog2 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { i; rewrite ?interpV_ret; econs; auto. }
              }
              destruct Hprog as [[? Hprog]|Hprog].
              { eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a) ctx rs fn args); eauto.
                { rewrite elem_of_union; right; set_unfold; auto. }
                { rewrite Hprog1 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { rewrite Hprog2 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { i; rewrite ?interpV_ret; econs; auto. }
              }
              revert Hprog1 Hprog2.
              destruct Hprog as [? [-> [? [bd1 [-> ?]]]]]; unfold_trans.
              intros temp1%Some_inj; rewrite -(func_ext_rev args temp1).
              intros temp2%Some_inj; rewrite -(func_ext_rev args temp2).
              ides (bd1 args).
              { rewrite !SBRed.ret !interpV_ret; econs; eauto. }
              { eapply (help_rel_eq); try by grind.
                i; s; rewrite ?interpV_ret; econs; eauto.
              }
              { eapply (help_rel_eq); try by grind.
                i; s; rewrite ?interpV_ret; econs; eauto.
              }
            }
            destruct (decide (i = stid)); subst.
            { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
              intros EQ; clarify.
              split; ss.
              rewrite ?length_fmap.
              ides (k (length tl)).
              { rewrite ?SBRed.ret ?interpV_ret; ired; auto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
            rewrite -insert_app_l // list_lookup_insert_ne //.
            intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
            apply Hlookup; eauto.
          }
        }
        { (* yield *)
          eapply gsim_Yield_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply GSimAux.gsim_Yield_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          ghnorm_l; ghnorm_r.
          zprogress.
          gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. ired. split; ss.
              ides (k ()).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
        { (* gettid *)
          eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.

          zprogress.
          gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              ides (k stid).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
      }
      { (* pgE *)
        destruct e as [key val|key].
        { (* sPut *)
          eapply gsim_SPut_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          eapply gsim_SPut_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.

          match goal with | A : msk_ctx ?a |- _ => rename A into Hmskctx end.
          apply Hmskctx in Hmsk; set_unfold in Hmsk.
          rewrite !insert_union_with_r; cycle 1.
          { rewrite lookup_union_with ?lookup_insert_ne //; ii; clarify; ss; eauto. }
          { rewrite ?lookup_insert_ne //; ii; clarify; ss; eauto. }

          ghnorm_l; ghnorm_r.
          zprogress. gbase.
          eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              ides (k ()).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
          { eapply map_Forall_union_with; cycle 1.
            { split.
              { eapply map_Forall_union_with_inv in Hst1 as ?; des; eauto. }
              { eapply map_Forall_insert_2; ss.
                eapply map_Forall_union_with_inv in Hst1 as ?; des; eauto.
              }
            }
            eapply map_Forall_union_with_inv_gen in Hst1.
            set_solver+Hmsk Hst1.
          }
          { eapply map_Forall_union_with; cycle 1.
            { split.
              { eapply map_Forall_union_with_inv in Hst2 as ?; des; eauto. }
              { eapply map_Forall_insert_2; ss.
                eapply map_Forall_union_with_inv in Hst2 as ?; des; eauto.
              }
            }
            eapply map_Forall_union_with_inv_gen in Hst2; revert Hst2.
            rewrite ?dom_union_with ?dom_insert ?dom_empty; i.
            set_solver+Hmsk Hst2.
          }
        }
        { (* sGet *)
          eapply gsim_SGet_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply gsim_SGet_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          ghnorm_l; ghnorm_r.
          match goal with | A : msk_ctx ?a |- _ => rename A into Hmskctx end.
          apply Hmskctx in Hmsk; set_unfold in Hmsk.
          rewrite ?lookup_union_with ?lookup_insert_ne //; ii; clarify; ss; eauto.
          rewrite ?lookup_empty /=; ired.
          zprogress. gbase.
          eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              set (temp := default _ _); ides (k temp).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
      }
      { (* coreE *)
        destruct e as [X|X|? ? fn args].
        { (* Choose *)
          eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros x.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists x.
          zprogress.
          gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k x); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* Take *)
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros x.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists x.
          zprogress.
          gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k x); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* IO *)
          eapply gsim_IO; (try by lookup_tac; s; do 2 f_equal; hnorm_itr). intros ret; s.
          ghnorm_l; ghnorm_r.
          zprogress. gbase. eapply (CIH rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ret); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
      }
    }
    { (* helper is done *)
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_HoareCall_epilogue_both;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
      intros res1 vret1 Hres1; rewrite !list_insert_insert.

      eapply gsim_Yield_tgt; (eauto using wf_src);
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
      { (* Done helping *)
        rewrite !list_insert_insert.
        rewrite {1}yield_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
        rewrite list_insert_insert. ghnorm_l. ghnorm_r.

        zprogress. gbase. eapply (CIH res1); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
      (* Yield-coinduction *)
      intros ?; split; first done.
      intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
      intros x2 res2 Hres2.
      rewrite !list_insert_insert. ghnorm_l; ghnorm_r.

      eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
      intros Hst1'.
      eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
      intros Hst2'.

      zprogress. gbase. eapply (CIH res2); try by des.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; ss.
          eapply (help_rel_loop); eauto.
          { f_equal.
            do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          { f_equal.
            do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
        }
      }
    }
    { (* call case *)
      match goal with | A : _ ∈ _ |- _ => rename A into Hfn end.
      set_unfold in Hfn; des; clarify.
      { (* Helping.run *)
        revert Htid; rewrite prog_s_run ?prog_t_run; eauto using wf_src; s; ired.
        rewrite /run_s /run_t -!interpV_bind; intros Htid.
        revert Htid; rewrite /HelpingOff.run /HelpingOn.run; intros Htid.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        destruct (arg ↓) as [j|];
          [|eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss]; s.
        ghnorm_l. ghnorm_r.

        eapply gsim_SGet_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_r.
        eapply map_Forall_insert_union_with in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2'.

        eapply gsim_Yield_tgt; (eauto using wf_src);
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
        { (* self-help *)
          rewrite ?list_insert_insert.
          rewrite /HelpingOn.try_run. ghnorm_r.

          eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2' end.
          ghnorm_r. hss. ghnorm_r.
          rewrite lookup_insert. ghnorm_r.

          rewrite {1}yield_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghnorm_l.

          zprogress with smj_bot smj_bot _ _.
          eapply gsim_jobs_both; try by rewrite ?length_fmap.
          intros res1 ret1 Hres1.
          ghnorm_r.

          eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_r.
          eapply map_Forall_insert_union_with in Hst2' as Hst2''; revert Hst2''.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 H
          end.
          intros Hst2''.

          eapply gsim_Yield_tgt; (eauto using wf_src);
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
          { (* immediate return of helpee *)
            rewrite ?list_insert_insert. ghnorm_r.

            rewrite {1}yield_unfold. ghnorm_l.
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            rewrite list_insert_insert.
            eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (None). rewrite list_insert_insert. ghnorm_l.

            zprogress.
            gbase. eapply (CIH res1); try by des; eauto.
            eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { rewrite insert_insert.
              eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto.
            }
            { intros i; destruct (decide (i = stid)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. }
            }
          }

          intros; split; first done.
          intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
          intros x res2 Hres2; ss.
          rewrite !list_insert_insert !insert_insert.
          rewrite insert_insert in Hst2''.

          zprogress.
          gbase. eapply (CIH res2); eauto.
          eexists (<[stid := (_, _, None)]> tl).
          esplits; [refl|refl|idtac|..].
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              eapply help_rel_loop with (x:=x)(ret:=ret1↑); eauto.
              { f_equal. grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              { f_equal. grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
          }
          { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as temp; revert temp.
            repeat match goal with
            | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
              state_insert_simpl k1 v1 Hst1
            end.
            i; eauto.
          }
          { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst2'' as temp; revert temp.
            repeat match goal with
            | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
              state_insert_simpl k1 v1 Hst2''
            end.
            i; eauto.
          }
        }

        intros Hmtid; split; first done.
        intros mtid_t1 stid_t1 Hmtid_t1; exists mtid_t1, stid_t1; split; first done.
        intros x res2 Hres2; rewrite !list_insert_insert.

        zprogress.
        gbase. eapply (CIH res2); eauto.
        set (rid_fresh := fresh _).
        eexists (<[stid := (_, _, Some (rid_fresh, (_, j)))]> tl); esplits; try refl.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_insert_true; eauto; first apply is_fresh. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          {
            rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply help_rel_helpee_pend with (x_fsp:=x); eauto.
              { rewrite /helpee_pend_s. f_equal. grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              { rewrite /helpee_pend_t. f_equal. grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
            apply list_lookup_fmap_Some in Hmtid as [[? ?] [? ?]]; clarify.
            esplits; eauto.
          }
        }
        { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as temp; revert temp.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 Hst1
          end.
          i; eauto.
        }
        { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst2' as temp; revert temp.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 Hst2'
          end.
          i; eauto.
        }
      }

      { (* Helping.help *)
        revert Htid; rewrite prog_s_help ?prog_t_help; eauto using wf_src; s; ired.
        rewrite /help_s /help_t -!interpV_bind /HelpingOff.help /HelpingOn.help; intros Htid.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros rid.
        rewrite list_insert_insert.

        (* Source-helper goes to yield *)
        rewrite yield_unfold. ghnorm_l.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert. ghnorm_l.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (Some true). rewrite list_insert_insert. ired.
        rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold !HoareCall_prologue_sred.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.

        (* Handling yield *)
        eapply gsim_HoareCall_prologue_both;
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
        intros res3 x Hres3. rewrite ?list_insert_insert. ghnorm_l; ghnorm_r.
        eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].

        rewrite prog_s_yield; auto using wf_src.
        rewrite /yield /SchI.yield /cfunU /fbody_trivial HoareFun_prologue_sred; ired.
        rewrite -interpV_bind.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
        destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        destruct (_ !! mtid) as [[? ?]|] eqn : Hmtid; ss; cycle 1.
        { ghnorm_l.
          destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        case_decide; subst; cycle 1.
        { ghnorm_l.
          destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghnorm_l.

        set (caseb :=
          match reqmap !! rid with
          | None => false
          | Some (None, _) => true
          | Some (Some _, _) => false
          end
        ).
        (* Choose the helpee! *)
        destruct caseb eqn : Hcase; cycle 1.
        { (* No Helpee *)
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          unshelve eexists.
          { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ghnorm_l.

          eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.
          eapply map_Forall_insert_union_with in Hst1 as Hst1'; revert Hst1'.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 H
          end.
          intros Hst1'.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.

          case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
          eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.

          (* No helping here *)
          rewrite /HelpingOn.try_run; ired.
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
          intros res4 vret Hres4; rewrite !list_insert_insert.
          ghnorm_l; ghnorm_r.
          ghnorm_r.

          eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
          ghnorm_r. hss. ghnorm_r.

          destruct (reqmap !! rid) as [[[ret|]]|] eqn : Hridreqmap; cycle 1.
          { subst; clarify. }
          { eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|ss]. }
          clear dependent caseb. ghnorm_r.

          (* get out of the helping zone *)
          rewrite yield_unfold; ghnorm_l.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.

          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists (Some true).
          rewrite list_insert_insert. ired.
          rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.

          rewrite HoareFun_epilogue_sred.
          eapply gsim_HoareCall_prologue_HoareFun_epilogue;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
          intros res5 x5 Hres5. rewrite ?list_insert_insert.
          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].

          rewrite prog_s_yield; auto using wf_src.
          rewrite /yield /help_yield_t /SchI.yield /cfunU /fbody_trivial; ired; rewrite -interpV_bind.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
          { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
            eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          }

          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|eauto|]; s.
          rewrite !list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1' end.
          ghnorm_l. hss.

          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
          case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
          eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
          ghnorm_l. hss. ghnorm_l.

          rewrite Hmtid; des_ifs_safe; ss. clear e. ghnorm_l.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          unshelve eexists.
          { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ghnorm_l.

          eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.
          eapply map_Forall_insert_union_with in Hst1' as Hst1''; revert Hst1''.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 H
          end.
          intros Hst1''.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
          eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          rewrite HoareCall_epilogue_sred.
          eapply gsim_HoareCall_epilogue_both;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
          intros res6 vret6 Hres6; rewrite !list_insert_insert.

          rewrite yield_unfold.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists (None).
          rewrite list_insert_insert.
          ghnorm_l; ghnorm_r.

          zprogress.
          gbase. eapply (CIH res6); eauto; try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }

        (* Going to helpee *)
        destruct (reqmap !! rid) as [[[|] jid]|] eqn : Hrid; ss.
        pose proof Hrid as Hrid'.
        eapply reqmap_rel_Some_2 in Hrid' as [stid_helpee [i_s [i_t Hhelpee]]]; eauto.

        eapply Hlookup in Hhelpee as Hhelpee'.
        destruct Hhelpee' as [Hhelpee' [mtid_helpee Hthshelpee]].
        inv Hhelpee'; des; clarify.
        eapply lookup_lt_Some in Hhelpee as Hhelpeelen.
        assert (Hneq : stid_helpee ≠ stid) by (ii; clarify).

        ghnorm_l.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        unshelve eexists.
        { exists (mtid_helpee, stid_helpee). rewrite /= list_lookup_fmap Hthshelpee //. }
        rewrite list_insert_insert. ghnorm_l.

        eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.
        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.
        eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.

        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.

        eapply gsim_tau_src; auto.
        { rewrite list_lookup_insert_ne //=.
          rewrite list_lookup_fmap Hhelpee /=.
          rewrite /helpee_pend_s; hnorm_itr.
        }

        eapply gsim_HoareCall_epilogue_HoareFun_prologue;
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
        intros res4 ret Hres4.
        rewrite !list_insert_insert.

        rewrite {1}yield_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.

        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists None. rewrite list_insert_insert.

        (* target proceed for helping *)
        rewrite /HelpingOn.try_run /cgetU.
        ghnorm_r.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r. rewrite Hrid; ghnorm_r; ghnorm_l.

        zprogress with smj_bot smj_bot _ _.
        eapply gsim_jobs_both; try by rewrite ?length_insert ?length_fmap.
        intros res5 ret5 Hres5.

        ghnorm_r.
        eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_r.
        eapply map_Forall_insert_union_with in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2'.

        rewrite {1}yield_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert. ghnorm_l.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (Some true).
        rewrite list_insert_insert. ired.
        rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold.
        eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.

        rewrite HoareFun_epilogue_sred.
        eapply gsim_HoareCall_prologue_HoareFun_epilogue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss|].
        intros res6 ret6 Hres6.
        rewrite !list_insert_insert.

        eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
        rewrite prog_s_yield; auto using wf_src.
        rewrite /yield /help_yield_t /SchI.yield /cfunU /fbody_trivial; ired; rewrite -interpV_bind.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
        destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|apply Hst1'|]; s.
        rewrite !list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1' end.
        ghnorm_l. hss.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        rewrite Hthshelpee; des_ifs_safe; ss. clear e. ghnorm_l.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        unshelve eexists.
        { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
        rewrite list_insert_insert.

        eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.
        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1' as Hst1''; revert Hst1''.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1''.
        eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l. rewrite list_insert_commute //.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.

        rewrite HoareCall_epilogue_sred.
        eapply gsim_HoareCall_epilogue_both;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
        intros res7 vret7 Hres7; rewrite !list_insert_insert.

        rewrite {1}yield_unfold.
        eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (None).
        rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.

        zprogress.
        gbase. eapply (CIH res7); eauto.
        set (i_helpee := ⇓cris (tau;; _)).
        eexists (<[stid := (⇓cris (ktr_s () ↑), ⇓cris (ktr_t () ↑), None)]>
          (<[stid_helpee := (i_helpee, _, Some (rid, (_, jid)))]> tl)).
        esplits; try match goal with | |- context[map_Forall _] => fail | |- _ => eauto end.
        { rewrite ?list_fmap_insert //=. }
        { rewrite ?list_fmap_insert //=.
          do 2 f_equal. rewrite list_insert_id //. rewrite list_lookup_fmap Hhelpee //.
        }
        { rewrite list_insert_commute //.
          eapply reqmap_rel_delete_true_2; eauto.
          { rewrite list_lookup_insert_ne //. }
          eapply reqmap_rel_id; eauto.
        }
        { intros i; destruct (decide (i = stid)).
          { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify.
            rewrite length_insert //.
          }
          destruct (decide (i = stid_helpee)).
          { subst; intros ??? Hin; rewrite list_lookup_insert_ne // list_lookup_insert // in Hin.
            clarify; split; last eauto.
            eapply help_rel_helpee_done; eauto.
            subst i_helpee.
            f_equal. grind.
            do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
        }
      }

      { (* SchI.inner_spawn *)
        revert Htid; rewrite prog_s_inner_spawn; auto using wf_src; rewrite prog_t_inner_spawn //.
        rewrite /inner_spawn; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU.
        destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
        rewrite !lookup_empty.

        ghnorm_l; ghnorm_r.
        case_bool_decide as Hs; ghnorm_l;
          [|eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss].

        eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          rewrite list_insert_insert.
        eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          rewrite list_insert_insert.
        hexploit (prog_s_prog_t s ctx rs); eauto; intros [[-> ->]|Hprog].
        { s; giter_l. ired. rewrite list_lookup_insert /=. gstep_l; done.
          rewrite length_fmap //.
        }
        zprogress.
        gbase.
        eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            destruct Hprog as [Hprog|Hprog].
            { exfalso; des; subst s; apply Hs; clear; set_solver. }
            destruct Hprog as [Hprog|Hprog].
            { eapply help_rel_call with (ctx:=ctx); eauto.
              { des; clarify; rewrite elem_of_union; right; done. }
              { i; ired; rewrite -?bind_tau -?SBRed.tau.
                eapply help_rel_inner_spawn; eauto.
                { rewrite /inner_spawn_pend; f_equal.
                  instantiate (1:=ret); grind.
                  repeat f_equal; extensionalities a; grind.
                }
                { rewrite /inner_spawn_pend.
                  repeat f_equal; extensionalities a; grind.
                }
              }
            }
            destruct Hprog as [? [-> [msk1 [bd1 [-> ?]]]]]; s; unfold_trans; ired.
            rewrite -?interpV_bind.
            ides (bd1 t↑).
            { rewrite ?SBRed.ret; ired. rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply help_rel_eq; eauto.
              i; s.
              rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply help_rel_eq; eauto.
              i; s.
              rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
          }
        }
      }

      { (* SchI.spawn *)
        revert Htid; rewrite prog_s_spawn; auto using wf_src; rewrite prog_t_spawn //.
        rewrite /spawn; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.spawn.
        destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghnorm_r.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        rewrite lookup_empty.
        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.
        eapply gsim_Spawn_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_Spawn_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.
        rewrite prog_s_inner_spawn; auto using wf_src; rewrite prog_t_inner_spawn //=.
        ired.
        ghnorm_l; ghnorm_r.

        eapply gsim_SPut_src; auto.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        rewrite insert_app_l // ?length_insert ?length_fmap // list_insert_insert.
        eapply map_Forall_insert_union_with in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.
        ghnorm_l.

        eapply gsim_SPut_tgt; auto.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        rewrite insert_app_l // ?length_insert ?length_fmap // list_insert_insert.
        eapply map_Forall_insert_union_with with (k := SchI.v_ths) in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2'.
        ghnorm_r.

        zprogress. gbase.
        eapply (CIH rs); eauto.
        eexists ((<[stid := (_, _, None)]> tl) ++ [(inner_spawn (s, t)↑, inner_spawn (s, t)↑, None)]); ss.
        esplits; eauto.
        { rewrite ?fmap_app list_fmap_insert //=. }
        { rewrite ?fmap_app list_fmap_insert //=. }
        { eapply reqmap_rel_append; eauto.
          eapply reqmap_rel_id; eauto.
        }
        { intros i1; destruct (decide (i1 = length tl)); subst.
          { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
            rewrite Nat.sub_diag /=; intros Heq; inv Heq.
            split; ss.
            eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a) ctx rs SchHdr._spawn); eauto.
            { rewrite /HelpingOn.t /SchI.t; ss; set_solver-. }
            { rewrite prog_s_inner_spawn; auto using wf_src; s; ired; rewrite -!interpV_bind. grind. }
            { rewrite prog_t_inner_spawn; auto; s; ired; rewrite -!interpV_bind. grind. }
            i; rewrite !interpV_ret; eapply help_rel_ret; eauto.
          }
          destruct (decide (i1 = stid)); subst.
          { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
            intros EQ; clarify.
          }
          rewrite -insert_app_l // list_lookup_insert_ne //.
          intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
          eapply Hlookup in Hi; des; split; eauto.
          destruct no; eauto. des; eexists _, _; rewrite lookup_app_l //.
          eapply lookup_lt_Some; eauto.
        }
      }

      { (* SchI.yield *)
        revert Htid; rewrite prog_s_yield; auto using wf_src; rewrite prog_t_yield //.
        rewrite /yield; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.yield.
        destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghnorm_r.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.
        eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        destruct (_ !! mtid) as [[? ?]|]; ghnorm_l; cycle 1.
        { ghnorm_l.
          destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        case_decide; ghnorm_l; subst; cycle 1.
        { ghnorm_l.
          destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }

        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros [[mtid_t1 stid_t1] Hmtid_t1]; rewrite list_insert_insert. ghnorm_l; ss.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (exist _ (mtid_t1, stid_t1) Hmtid_t1); rewrite list_insert_insert. ghnorm_l; ss.

        eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.
        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.

        eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_r.
        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst2 as Hst2'; revert Hst2'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst2'.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
        eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_l.
        eapply GSimAux.gsim_Yield_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghnorm_r. ired.

        zprogress. gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }

      { (* SchI.join *)
        revert Htid; rewrite prog_s_join; auto using wf_src; rewrite prog_t_join //.
        rewrite /join; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.join.
        destruct Any.downcast as [n|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghnorm_r.

        rewrite unfold_iterC; ired.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        destruct (ths !! n) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ghnorm_l; ghnorm_r.
        { (* Join-return *)
          zprogress; gbase. eapply (CIH rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }
        { (* Join-loop *)
          rewrite /ccallU !lookup_empty.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite !list_insert_insert.

          ghnorm_l. ghnorm_r.
          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert; ghnorm_l.
          eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert. ghnorm_r.

          zprogress.
          gbase. eapply (CIH rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify.
              split; ss. eapply (help_rel_call _ _ _ _ ctx rs (SchHdr.yield)); eauto.
              { set_solver-. }
              intros ret; ss.
              eapply (help_rel_join _ _ ret _ _ n); eauto.
              { rewrite /join_pend /ccallU. f_equal.
                do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
                repeat f_equal; extensionalities a; destruct a; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /join_pend /ccallU. f_equal.
                do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
                repeat f_equal; extensionalities a; destruct a; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
          }
        }

        (* join-None *)
        zprogress.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }

      { (* SchI.get_tid *)
        revert Htid; rewrite prog_s_get_tid; auto using wf_src; rewrite prog_t_get_tid //.
        rewrite /get_tid /SchI.get_tid /cfunU; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        destruct Any.downcast as [n|]; s; ghnorm_l; cycle 1.
        { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghnorm_r.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghnorm_l. hss. ghnorm_l.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
        ghnorm_r. hss. ghnorm_r.

        zprogress. gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
    }
    { (* inner spawn - continuation *)
      rewrite /inner_spawn_pend in Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      destruct Any.downcast as [n|]; s; ghnorm_l; cycle 1.
      { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
        eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghnorm_r.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
      ghnorm_l. hss. ghnorm_l.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
      ghnorm_l. hss. ghnorm_l.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
      ghnorm_r. hss. ghnorm_r.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
      ghnorm_r. hss. ghnorm_r.

      des_ifs; ghnorm_l; cycle 1.
      { ghnorm_l.
        destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
        eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }

      eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghnorm_l.
      eapply map_Forall_insert_union_with in Hst1 as Hst1'; revert Hst1'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hst1'.

      eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghnorm_l.
      eapply map_Forall_insert_union_with with (k:=SchI.v_ths) in Hst2 as Hst2'; revert Hst2'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hst2'.

      zprogress. gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros stid2; destruct (decide (stid2 = stid)); subst; cycle 1.
        { intros itr_s2 itr_t2 no2; rewrite list_lookup_insert_ne //=.
          intros Hi; pose proof Hi as Hi'; revert Hi'; intros [Hi1 Hi2]%Hlookup; split; eauto.
          destruct no2 as [[tid2 [b2 jid2]]|]; ss.
          destruct Hi2 as [mtid2 [ro2 Hi2]]; apply lookup_lt_Some in Hi2 as Hlen2.
          destruct (decide (mtid2 = mtid)); subst.
          { rewrite Hi2 in Heq; clarify. eexists mtid, (Some _); rewrite list_lookup_insert //. }
          exists mtid2, ro2; rewrite list_lookup_insert_ne //.
        }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_terminate; eauto.
          { f_equal; symmetry; hnorm_itr. }
          { f_equal; etrans; first hnorm_itr; symmetry; hnorm_itr. }
        }
      }
    }
    { (* join - continuation *)
      rewrite /join_pend in Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      destruct Any.downcast as [n|]; s; ghnorm_l; cycle 1.
      { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
        eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghnorm_r.

      rewrite unfold_iterC; ired.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite !list_insert_insert.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
      ghnorm_l. hss. ghnorm_l.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
      ghnorm_r. hss. ghnorm_r.

      destruct (ths !! tid) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=.
      { (* Join-return *)
        ghnorm_l; ghnorm_r.
        zprogress. gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
      { (* Join-loop *)
        rewrite /ccallU. ghnorm_l; ghnorm_r.
        rewrite !lookup_empty.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        ghnorm_l; ghnorm_r.
        eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert. ghnorm_l.
        eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert. ghnorm_r.

        zprogress. gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. eapply (help_rel_call _ _ _ _ ctx rs (SchHdr.yield)); eauto.
            { set_solver-. }
            intros ret; ss; eapply (help_rel_join _ _ ret _ _ tid); eauto.
            { rewrite /join_pend /ccallU. f_equal.
              do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              repeat f_equal; extensionalities a; destruct a; grind.
              repeat f_equal; extensionalities a; grind.
            }
            { rewrite /join_pend /ccallU. f_equal.
              do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              repeat f_equal; extensionalities a; destruct a; grind.
              repeat f_equal; extensionalities a; grind.
            }
          }
        }
      }

      (* join-None *)
      ghnorm_l; ghnorm_r.
      zprogress. gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }
    { (* inner_spawn - continuation*)
      revert Htid; rewrite /Sch.terminate; unseal SCH; rewrite unfold_iterC; intros Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      ghnorm_l; ghnorm_r.
      rewrite !lookup_empty.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite !list_insert_insert.

      ghnorm_l; ghnorm_r.
      eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert. ghnorm_l.
      eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert. ghnorm_r.

      zprogress. gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; last ss.
          eapply (help_rel_call _ _ _ _ ctx rs (SchHdr.yield)); eauto.
          { set_solver-. }
          i; s.
          eapply help_rel_eq with (itr := tau;; Ret ()↑).
          { f_equal; symmetry; etrans; first hnorm_itr; do 2 f_equal; etrans; first hnorm_itr.
            instantiate (1:=λ _, _); s; refl.
          }
          { f_equal; symmetry; etrans; first hnorm_itr; do 2 f_equal; etrans; first hnorm_itr.
            instantiate (1:=λ _, _); s; refl.
          }
          { instantiate (1:=msk_scp ∅ msk_true); split; ii; ss. }
          { ii; clarify. }
          i; ss.
          eapply help_rel_terminate; eauto; rewrite /Sch.terminate; unseal SCH.
          { f_equal; etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr.
            repeat f_equal; extensionalities a; destruct a; grind.
          }
          { f_equal; etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr.
            repeat f_equal; extensionalities a; destruct a; grind.
          }
        }
      }
    }

    { (* Return case *)
      giter_l; giter_r; rewrite /= ?list_lookup_fmap Htid /=.
      gstep_l; gstep_r; gnorm_l; gnorm_r.
      des_ifs; ss.
      { rewrite /LModTr.interp_stateE ?interp_state_ret; ired.
        gstep; econs; econs; ss.
      }
      rewrite /triggerUB; ss; gstep_l; ss.
    }
  (*SLOW*)Qed.
End HelpingOnOff.

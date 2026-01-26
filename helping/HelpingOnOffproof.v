Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
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
        { rewrite /HelpingOff.fnsems /= ?fmap_insert fmap_empty. mod_tac scope_solver. }
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
      ((SMod.to_mod (HelpingOn.sp mn sp) (HelpingOn.Mod mn jobs)
      ★ CFilter.filter (Helping.exports mn) (SMod.to_mod ∅ SchI.smod)) ★ ctx) rs)).

  Definition run_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOff.run jobs x)))).
  Definition run_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
      ((tau;; ⇓smod(HelpingOn.sp mn sp) (HelpingOn.run mn jobs x)))).

  Definition help_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(sp) (HelpingOff.help x)))).
  Definition help_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(HelpingOn.sp mn sp) (HelpingOn.help mn jobs x)))).

  Definition help_yield_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      (tau;; ⇓smod(sp) (fbody_trivial x))).
  Definition help_yield_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
      (tau;; ⇓smod(HelpingOn.sp mn sp) (Ret ()↑))).

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

  Lemma prog_s_help_yield ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs (Helping.yield mn) = Some help_yield_s.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOff.fnsems; simpl_map; s; eauto.
  Qed.

  Lemma prog_t_help_yield ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs (Helping.yield mn) = Some help_yield_t.
  Proof.
    intros ?.
    rewrite /LMod.prog Mod.to_lmod_fnsems.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1. { rewrite Mod.dom_fnsems_add; set_solver. }
    eapply Mod.add_wf_inv in H1; des.
    rewrite Mod.lookup_fnsems_l_2 //; cycle 1.
    { set_solver. }
    rewrite /= /HelpingOn.fnsems; simpl_map; s; eauto.
  Qed.
  (* Lemma no_help_prog fn ctx rs :
    fn ∉ Helping.exports mn →
    prog_s ctx rs fn = prog_t ctx rs fn.
  Proof using.
    intros ?.
    rewrite /LMod.prog /Mod.to_lmod /=.
    etrans;
      rewrite ?lookup_fmap lookup_omap ?lookup_union_with; simpl_map;
      do 2 (try rewrite lookup_insert_ne); try set_solver.
  Qed. *)
  
  (* Local Definition filters_state (msk : emask) : Prop :=
    ∀ k, msk _ (subevent _ (SGet ())) *)
  Lemma prog_s_prog_t fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter (Helping.exports mn) SchI.t) ★ ctx) →
    (prog_s ctx rs fn = None ∧ prog_t ctx rs fn = None) ∨
    ((fn = Helping.run mn ∧ prog_s ctx rs fn = Some run_s ∧ prog_t ctx rs fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs fn = Some help_s ∧ prog_t ctx rs fn = Some help_t) ∨
    (fn = Helping.yield mn ∧ prog_s ctx rs fn = Some help_yield_s ∧ prog_t ctx rs fn = Some help_yield_t)) ∨
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
      des; clarify; [left|right; left|right; right]; split; auto; split;
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

  Lemma yield_unfold :
    @Sch.yield crisE _ _ =
    tau;; b <- trigger (Choose (option bool));;
    match b with
    | None => Ret tt
    | Some false => Sch.yield
    | Some true => trigger (Call SchHdr.yield tt↑);;; Sch.yield
    end.
  Proof using.
    rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
    repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
    { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. done. }
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
    tau;;
    x <- ⇓cris (⇓sb(msk_real (msk_scp SchI.scopes msk_true))
      (⇓smod(∅) (
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
        Ret (r↑))));;
    ktr x.

  Definition join_pend (arg : Any.t) jtid ktr : itree lmodE Any.t :=
    tau;;
    x <- ⇓cris (⇓sb(msk_real (msk_scp SchI.scopes msk_true))
      (⇓smod(∅) (
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
        Ret (x_3↑))));;
    ktr x.

  Definition helpee_pend_s
      (j : jobID) k
      (fspo : option fspec) x_fsp
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
      (fspo : option fspec) x_fsp k
      : itree lmodE Any.t :=
    ⇓cris (tau;; x_ <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      x <- ⇓smod(HelpingOn.sp mn sp) (𝒴;;; r <- HelpingOn.try_run mn jobs tid_stid_cur;; 𝒴;;; Ret r↑);;
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
            ⇓smod(HelpingOn.sp mn sp) (𝒴);;;
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
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_join itr_s itr_t (arg : Any.t) ktr_s ktr_t tid :
      itr_t = join_pend arg tid ktr_t →
      itr_s = join_pend arg tid ktr_s →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_terminate itr_s itr_t ktr_s ktr_t :
      itr_s =
        (x <- ⇓cris (⇓sb(msk_real (msk_scp SchI.scopes msk_true))
          (⇓smod(sp) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_s x) →
      itr_t =
        (x <- ⇓cris (⇓sb(msk_real (msk_scp SchI.scopes msk_true))
          (⇓smod(sp) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_t x) →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
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
    tp_t !! tid_t = Some (⇓cris ((⇓sb(msk_scp scp msk_true) (⇓smod(HelpingOn.sp mn sp) (𝒴)));;; k_t)) →
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
                 ⇓smod(HelpingOn.sp mn sp) 𝒴);;; k_t)]> tp_t))
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
    rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold HelpingOn.sp_helping_yield.
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
    eapply gpaco7_mon; eauto.
    replace_l; [|replace_r]; cycle 2.
    { eapply (Hk2 x.1 res1); eauto. }
    { repeat f_equal; ss. extensionality a. hnorm_itr. }
    { repeat f_equal; ss. extensionality a. hnorm_itr. }
  (*SLOW*)Qed.

  Lemma helping_onoff_correct :
    ctx_refines (mod_src, emp%I) (mod_tgt, emp%I).
  Proof.
    rewrite /mod_src /mod_tgt.
    intros [ctx ctxP] WF; ss; split; first by apply wf_src.

    (* simulation proof *)
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].
    intro arg; eapply (gsim_adequacy); repeat (instantiate (1:=smj_bot)).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    rewrite -> !lookup_fmap.
    simpl_map; rewrite -> !lookup_union_with; simpl_map.
    rewrite ?lookup_insert_ne; ii; clarify; rewrite ?lookup_empty /=.
    destruct (_ ctx !! None) as [[[msk bd]|]|] eqn : FIND; s; cycle 1.
    { s. ired. ginit. gstep_l. ss. }
    { s. ired. ginit. gstep_l. ss. }
    ired.

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
    destruct no as [[n [[retid|] j]]|]; cycle 2.

    { (* Non-helpee case *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _].
      inv Hcase; cycle 1.

      admit.
(*       
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
          { (* Guarantee *) admit. }
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
                  { des; clarify; rewrite elem_of_union; left; set_unfold; [left|right;left|right;right]; done. }
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
            eapply HelpingAux.gsim_Yield_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
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
              set_solver.
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
              set_solver.
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
            giter_l; giter_r.
            rewrite /= ?list_lookup_fmap Htid /=.
            gsteps_l. gsteps_r. intros ? x_tgt ->.
            gsteps_l; gsteps_r.
            ired.
            zprogress. gbase. eapply (CIH rs); try by des.
            eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { eapply reqmap_rel_id; eauto. }
            { intros i; destruct (decide (i = stid)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. split; ss.
                ired; ides (k x_tgt); try by eapply help_rel_eq; eauto.
                by rewrite ?SBRed.ret; ired.
              }
            }
          }
        }
      }  *)
      { (* helper is done *)
        admit.
      }
      { (* call case *)
        match goal with | A : _ ∈ _ |- _ => rename A into Hfn end.
        set_unfold in Hfn; des; clarify.
        { (* Helping.run *)
          revert Htid; rewrite prog_s_run ?prog_t_run; eauto using wf_src; s; ired.
          rewrite /run_s /run_t -!interpV_bind; intros Htid.
          (* eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros [N stid2]. ghnorm_l.
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros []. ghnorm_l. rewrite list_insert_insert.
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros varg. ghnorm_l. rewrite list_insert_insert.
          eapply gsim_Assume_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros rs2 Hrs2. ghnorm_l. rewrite list_insert_insert.

          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (N, stid2). ghnorm_r.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (). ghnorm_r. rewrite list_insert_insert.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists varg. ghnorm_r. rewrite list_insert_insert.
          eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists rs2; splits; try by des. ghnorm_r. rewrite list_insert_insert. *)
          revert Htid; rewrite /HelpingOff.run /HelpingOn.run; intros Htid.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          destruct (arg ↓) as [j|];
            [|eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss]; s. 
          ghnorm_l.
          ghnorm_r. case_bool_decide as Htemp; [|set_solver +Htemp]; clear Htemp. ghnorm_r.

          eapply gsim_SGet_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
          ghnorm_r. hss.
          ghnorm_r. case_bool_decide as Htemp; [|set_solver +Htemp]; clear Htemp. ghnorm_r.

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
            rewrite /HelpingOn.try_run.
            ghnorm_r. case_bool_decide as Htemp; [|set_solver +Htemp]; clear Htemp. ghnorm_r.

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

            ghnorm_r. case_bool_decide as Htemp; [|set_solver +Htemp]; clear Htemp. ghnorm_r.
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

              (* eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              intros vret; rewrite list_insert_insert. ghnorm_r; ss.
              eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              intros res2 Hres2; rewrite list_insert_insert. ghnorm_r; ss. *)

              rewrite {1}yield_unfold. ghnorm_l.
              eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              rewrite list_insert_insert.
              eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              exists (None). rewrite list_insert_insert. ghnorm_l.
              (* eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              exists vret; rewrite list_insert_insert. ghnorm_l; ss.
              eapply gsim_Guarantee_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              exists res2; splits; (try by des); rewrite list_insert_insert. ghnorm_l. *)

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
          (* eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros [N stid2]. ghnorm_l.
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros []. ghnorm_l. rewrite list_insert_insert.
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros varg. ghnorm_l. rewrite list_insert_insert.
          eapply gsim_Assume_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros rs2 Hrs2. ghnorm_l. rewrite list_insert_insert.

          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (N, stid2). ghnorm_r.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (). ghnorm_r. rewrite list_insert_insert.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists varg. ghnorm_r. rewrite list_insert_insert.
          eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists rs2; splits; try by des. ghnorm_r. rewrite list_insert_insert. *)
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
          rewrite /ccallU. ired.
          rewrite !SRed.bind !SRed.vis_call !HoareCall_unfold HelpingOn.sp_yield. ghnorm_l.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert. ghnorm_l.
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert. ghnorm_r.

          (* Handling yield *)
          eapply gsim_HoareCall_prologue_both;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
          intros res3 x Hres3. rewrite ?list_insert_insert. ghnorm_l; ghnorm_r.
          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].

          rewrite prog_s_yield; auto using wf_src.
          rewrite prog_t_help_yield //=.
          rewrite /yield /help_yield_t /SchI.yield /cfunU /fbody_trivial; ired.
          do 2 rewrite -interpV_bind.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
          { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
            eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          }

          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
          ghnorm_l. hss. ghnorm_l.

          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert. ghnorm_l.
          case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
          ghnorm_l; ghnorm_r.
          eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_l.

          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
          ghnorm_l. hss. ghnorm_l.

          (* TODO : make try_run into a function... or maybe help's spec becomes yield's? *)
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

            eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_r.

            (* No helping here *)
            rewrite /HelpingOn.try_run; ired.
            eapply gsim_HoareCall_epilogue_both;
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
            intros res4 vret Hres4; rewrite !list_insert_insert.
            ghnorm_l; ghnorm_r.
            ghnorm_r. case_bool_decide as Htemp; [|set_solver +Htemp]; clear Htemp. ghnorm_r.

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
            eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert.

            eapply gsim_HoareCall_prologue_both;
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
            intros res5 x5 Hres5. rewrite ?list_insert_insert. ghnorm_l; ghnorm_r.
            eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
            eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].

            rewrite prog_s_yield; auto using wf_src.
            rewrite prog_t_help_yield //=.
            rewrite /yield /help_yield_t /SchI.yield /cfunU /fbody_trivial; ired; rewrite -?interpV_bind.
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
            eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
            destruct Any.downcast as [[]|]; s; ghnorm_l; cycle 1.
            { destruct excluded_middle_informative as [|temp]; [|exfalso; apply temp; eauto].
              eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
            }

            eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|eauto|]; s.
            rewrite !list_insert_insert.
            match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1' end.
            ghnorm_l. hss. ghnorm_l.

            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            rewrite list_insert_insert. ghnorm_l.
            case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
            ghnorm_l; ghnorm_r.
            eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_l.

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
            rewrite list_insert_insert. ghnorm_l.

            case_decide as Htemp; [set_solver +Htemp|]; s; clear Htemp.
            eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_l.
            eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_l.

            eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_r.

            rewrite /HelpingOn.try_run; ired.
            eapply gsim_HoareCall_epilogue_both;
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
            intros res6 vret6 Hres6; rewrite !list_insert_insert.
            ghnorm_l; ghnorm_r.

            rewrite yield_unfold; ghnorm_l.
            eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert. ghnorm_l.

            eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists (None).
            rewrite list_insert_insert. ghnorm_l.
            (* eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros vret7.
            rewrite list_insert_insert.
            eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists vret7.
            rewrite list_insert_insert.

            eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros res8 Hres8.
            rewrite list_insert_insert.
            eapply gsim_Guarantee_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            unshelve eexists; eauto using Hres8.
            splits; try by des.
            rewrite list_insert_insert.
            ghnorm_l; ghnorm_r. *)

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

          eapply gsim_tau_src; auto.
          { rewrite list_lookup_insert_ne //=.
            rewrite list_lookup_fmap Hhelpee /=.
            rewrite /helpee_pend_s; hnorm_itr.
          }
          eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghnorm_r.

          eapply gsim_HoareCall_epilogue_both;
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); try by des.
          { rewrite list_lookup_insert //.
            { do 2 f_equal; etrans; first hnorm_itr. }
          }
              
              {  }

          replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|].
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_lookup_insert // length_fmap; repeat f_equal; grind
            |ss
            |].
          clear dependent res1.
          intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.

          rewrite {1}yield_unfold. ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_insert length_fmap //|rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |exists None; rewrite list_insert_insert].
          ired. rewrite interpV_ret. ired.

          (* target proceed for helping *)
          rewrite /HelpingOn.try_run /cgetU; ired.
          replace_r; [rewrite interpV_bind interpV_vis //|]; ired.
          eapply gsim_SGet_tgt; [rewrite list_lookup_insert // length_fmap //| ss |].
          { rewrite String.eqb_refl //. }
          esplits; ss; [destruct (dec _ _); ss; clarify|].
          rewrite list_insert_insert. ired. rewrite ?interpV_ret; ired. hss. ired.

          rewrite Hrid. ired.
          eapply gsim_jobs_both;
            [rewrite length_insert length_fmap //
            |rewrite length_fmap //
            |ss
            |].
          clear dependent res1; intros res1 ret1 Hres1.

          ired; replace_r; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.
          rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |exists (Some true); rewrite list_insert_insert].
          ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l; rewrite list_insert_insert.

          rewrite HoareCall_unfold; ired.
          replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
          eapply gsim_HoareCall_prologue_HoareFun_epilogue;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss|].
          clear dependent res1. intros res1 ret Hres1.
          rewrite ?list_insert_insert. ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l; rewrite {1}/LMod.prog /=.
          destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
          clear e'.
          destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
          norm_l. rewrite list_insert_insert.

          unfold_trans.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_insert_insert].
          rewrite /SchI.yield /cfunU.
          destruct (ret ↓) as [[]|] eqn : Hret; cycle 1.
          { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_insert length_fmap //].
            ss; destruct (excluded_middle_informative _); step_l; ss.
          }
          ired. clear Hret.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l. rewrite list_insert_insert; ired.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.

          rewrite Hthshelpee; case_decide as H'; ss; clear H'. ired.

          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_insert length_fmap //
            |unshelve eexists].
          { exists (mtid, stid); ss; rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ired.

          ired. replace_l; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_insert length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          rewrite ?interpV_ret; ired.

          iter_l; rewrite list_lookup_insert_ne //=.
          rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_l; norm_l.
          rewrite list_insert_commute //.
          rewrite list_insert_insert.
          rewrite list_insert_commute //.

          replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
          eapply gsim_HoareCall_epilogue_both;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss
            |].
          clear dependent res1 x1.
          intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
          rewrite ?interpV_ret. ired.

          replace_l; [rewrite interpV_tau //|]; ired.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.

          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_insert length_fmap //
            |exists None; rewrite list_insert_insert].
          ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.

          rewrite /alist_upd /=; destruct (dec _ _); ss; clear e.
          apply gsim_flag.
          gbase. eapply (CIH res1); eauto.
          set (i_helpee := tau;; _).
          eexists (<[stid := (ktr_s1 () ↑, ktr_t1 () ↑, None)]>
            (<[stid_helpee := (i_helpee, _, Some (rid, (_, jid)))]> tl)).
          esplits; eauto.
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
              clarify; split; ss.
              eapply help_rel_helpee_done; eauto.
              esplits; eauto.
            }
            intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
          }
        }
        }

End Helping.
  (* 

  

  Lemma gsim_Yield_both r g RR p_s p_t tid_s tid_t tp_s tp_t
      img_c img_c' msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) ctx rs
      (ths : list (nat * option SAny.t)) (tid_cur_s tid_cur_t : nat) st_ctx (res : Σ) reqs :
    ✓ res →
    tid_s < length tp_s →
    tid_t < length tp_t →
    gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) k_s));; k_s1 x]>
            tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) k_t));; k_t1 x]>
            tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))) →
    ((∃ ro_s, ths !! tid_cur_s = Some (tid_s, ro_s)) →
      ∃ ro_t, ths !! tid_cur_t = Some (tid_t, ro_t) ∧
      (∀ mtidn_t stidn_t, ths.*1 !! mtidn_t = Some stidn_t →
        ∃ mtidn_s stidn_s, ths.*1 !! mtidn_s = Some stidn_s ∧
          ∀ (res1 : Σ) x, ✓ res1 →
          gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_s ctx rs))
                (stidn_s, <[tid_s := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_s))));; k_s1 x_]> tp_s))
              (Any.pair
                (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_s ↑)) :: st_ctx))
                (res1 ↑)))
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_t ctx rs))
                (stidn_t, <[tid_t := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_t))));; k_t1 x_]> tp_t))
              (Any.pair
                (ModTr.alist_encode
                  ((HelpingOn.v_reqs mn, reqs)
                  :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_t ↑)) :: st_ctx))
                (res1 ↑))))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp)(𝒴;;; k_s)));;
            k_s1 x]> tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (𝒴;;; k_t)));;
            k_t1 x]> tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))).
  Proof using.
    intros Hres Hlen_s Hlen_t Hk1 Hk2.
    eapply gsim_Yield_tgt; eauto.
    rewrite {1}yield_unfold. ired.
    replace_l; [rewrite interpV_tau //|]; ired.
    eapply gsim_tau_src; [rewrite list_lookup_insert //|]. rewrite list_insert_insert.

    replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
    exists (None); rewrite list_insert_insert. ired.

    eapply Hk1.
  Qed.

  Theorem helping_onoff_correct :
    ctx_refines (mod_off, emp%I) (mod_on, emp%I).
  Proof using.
    rewrite /mod_off /mod_on.
    intros [ctx ctxP] WF; ss; split.
    { inv WF. econs.
      { revert wf_fns. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
      { revert wf_scopes. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
    }
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].

    intro arg; eapply (@gsim_adequacy smj_bot smj_bot).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    rewrite !alist_find_map_snd.
    set (fnsems := (Mod.fnsems _ ++ _) ++ _).
    destruct (alist_find None fnsems) eqn: FIND; s; cycle 1.
    { s. ired. ginit. step_l. ss. }
    rewrite alist_find_app_o; des_ifs.
    { rewrite alist_find_app_o /HelpingOn.t /SchI.t in Heq; revert Heq; unseal CRIS; intros Heq.
      des_ifs; ss.
    }
    subst fnsems; rewrite alist_find_app_o in FIND; des_ifs.
    { rewrite /HelpingOff.t /SchI.t in Heq0; revert Heq0; unseal CRIS; ss. }
    rewrite FIND /ModTr.trans_ktree; ired.

    destruct f as [[[imgf mskf] scpf] f].
    assert (Hscp : scpf ## (SchI.scopes ++ HelpingOn.scopes mn)).
    { hexploit (Mod.well_scoped_fns ctx None); ss.
      rewrite /fnsems_scopes FIND /=; intros Hin.
      apply elem_of_disjoint; intros x Hinctx%elem_of_list_In%Hin%elem_of_list_In Hinsch.
      hexploit (Mod.wf_scopes WF); rewrite /Mod.scopes /=.
      intros Hnodup; eapply (NoDup_app_disjoint _ _ Hnodup x); eauto.
      { eapply elem_of_list_In. rewrite /Mod.scopes /SchI.t /HelpingOn.t; unseal CRIS; ss.
        revert Hinsch; rewrite /HelpingOn.scopes /SchI.scopes; ss.
        set_solver.
      }
      { eapply elem_of_list_In, Hinctx; eauto. }
    }

    clear Heq Heq0.
    rewrite /SB.sandbox_body /=.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }
    unfold_trans.
    (* Start coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    set (st_src := (_, _) :: _) at 1.
    set (st_tgt := (_, _) :: _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (option retID * jobID))))
        (mtid stid : nat) (ths : list (nat * option SAny.t)) st_ctx
        (reqmap : gmap nat (option retID * jobID)),
          st_src = [(SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, mtid↑)] ++ st_ctx ∧
          st_tgt = [(HelpingOn.v_reqs mn, reqmap↑);
            (SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, mtid↑)] ++ st_ctx ∧
          tp_src = (stid, (fst ∘ fst <$> tl)) ∧ tp_tgt = (stid, (snd ∘ fst <$> tl)) ∧
          reqmap_rel tl reqmap ∧
          ∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) →
            help_rel itr_s itr_t no ∧
            match no with
            | Some _ => ∃ stid_i ro_i, ths !! stid_i = Some (i, ro_i)
            | None => True
            end); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { rr; ss; split; first econs.
        split; [intros ????; rewrite ?list_lookup_singleton_Some; i; des; clarify|].
        intros ??; rewrite lookup_empty; i; clarify.
      }
      intros ???? [-> In]%list_lookup_singleton_Some; clarify.
      split; ss.
      ides (f arg).
      { rewrite ?interpV_ret; eapply help_rel_ret. }
      { eapply help_rel_eq; eauto.
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { ii; clarify. }
        apply help_rel_ret.
      }
      { eapply help_rel_eq; eauto.
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { ii; clarify. }
        apply help_rel_ret.
      }
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    clear st_src st_tgt tp_src tp_tgt f imgf mskf scpf FIND arg Hscp.
    revert_until WF.
    gcofix CIH.
    intros rs Hrs st_s st_t tp_s tp_t.
    intros [tl [mtid [stid [ths [st_ctx [reqmap [-> [-> [-> [-> [Hreqmap Hlookup]]]]]]]]]]].

    destruct ((fst ∘ fst <$> tl) !! stid) as [i|] eqn : Htid; cycle 1.
    { iter_l. rewrite Htid. step_l. norm_l. step_l. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    destruct no as [[n [[retid|] j]]|].

    { (* Done Helpee *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.

      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res1 x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_tgt; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res1. intros res2 x2 Hres2.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); try by des.

        eexists (<[stid := (_, _, (Some (n, (Some _, j))))]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_helpee_done; eauto.
            { rewrite /helpee_pend_t; repeat f_equal; grind. extensionalities a; grind. }
            { esplits; eauto. }
          }
        }
      }

      (* no job *)
      rewrite ?interpV_ret; ired.
      rewrite /HelpingOn.try_run; ired.

      replace_r; [rewrite interpV_bind //|]; ired.
      eapply gsim_s_cgetU_tgt;
        [rewrite list_lookup_insert // length_fmap //
        |ss; rewrite String.eqb_refl //
        |].
      esplits; eauto.
      { rewrite /alist_find ?eq_rel_dec_correct; des_ifs. }
      rewrite list_insert_insert.

      eapply reqmap_rel_Some in Hreqmap as Hsome; eauto. rewrite Hsome; clear Hsome.
      ired.

      eapply gsim_Yield_tgt; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res1. intros res2 x2 Hres2.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); try by des.

        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_false; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_loop; eauto.
          }
        }
      }

      (* Done helped *)
      rewrite yield_unfold; ired.
      replace_l; [rewrite interpV_tau //|].
      eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
      rewrite list_insert_insert.

      replace_l; [rewrite interpV_bind interpV_vis //|]; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|].
      exists None; rewrite list_insert_insert.
      ired. rewrite ?interpV_ret; ired. rewrite ?interpV_ret; ired.

      eapply gsim_flag.

      gbase. eapply (CIH res1); eauto.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_delete_false; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    { (* Pending helpee *)
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.
      revert Htid; rewrite /helpee_pend_s /helpee_pend_t; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x Hres1; rewrite ?list_insert_insert.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x. intros res x Hres.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, Some (n, (_, j)))]> tl); esplits; eauto.
        { rewrite list_fmap_insert //. }
        { rewrite list_fmap_insert //. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend n j); eauto.
              { rewrite /helpee_pend_s. grind.
                instantiate (1:=x). repeat f_equal. extensionality a; grind.
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal. extensionality a; grind. }
            }
            esplits; eauto.
          }
        }
      }

      (* tired of waiting *)
      rewrite /HelpingOn.try_run; ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto. { destruct (dec _ _); clarify. }
      rewrite ?list_insert_insert. ired.

      eapply reqmap_rel_Some in Hreqmap as Hsome; eauto.
      rewrite Hsome; clear Hsome.

      ired.
      eapply gsim_jobs_both; try by rewrite ?length_fmap.
      clear dependent res x. hss.
      intros res ret Hres.

      ired. replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert.
      rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res. intros res x Hres.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_true; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply help_rel_loop; eauto; ss.
          }
        }
      }

      rewrite ?interpV_ret; ired.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH res); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_delete_true; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    (* Non-helpee case *)
    apply lookup_lt_Some in Htid as Hstid_cur_length.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [Hcase _].
    inv Hcase; cycle 2.
    { (* Done helper case *)
      eapply lookup_lt_Some in Htid as Htidlen.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x1. intros res x1 Hres.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply (help_rel_loop); eauto.
          }
        }
      }

      (* Done helping *)
      rewrite ?interpV_ret; ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH res); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    { (* call case *)
      eapply lookup_lt_Some in Htid as Htidlen.
      revert H3 H4.
      destruct (decide (fn = Helping.run mn)); subst.
      { (* Helping.run *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; [ss|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /HelpingOff.run /HelpingOn.run.
        intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid //=|].
        destruct (arg↓) as [j|] eqn:Hargs ; cycle 1.
        { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. ss. }
        ss. ired.

        (* call for help *)
        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        { des_ifs; destruct (dec _ _); clarify. }
        rewrite list_insert_insert.

        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite list_insert_insert.

        rewrite /alist_upd /_alist_upd /=.
        destruct (dec _ _) as [Heq|Heq]; ss; clear Heq.

        eapply gsim_Yield_both; eauto.
        { rewrite length_fmap //. }
        { rewrite length_fmap //. }
        { (* Self-help *)
          rewrite /HelpingOn.try_run.
          ired. replace_r; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert //| |]; s.
          { rewrite ?length_fmap //. }
          { rewrite String.eqb_refl //. }
          esplits; eauto.
          { destruct (dec _ _); clarify. }
          rewrite list_insert_insert. ired. rewrite lookup_insert. ired.

          eapply gsim_jobs_both; try by rewrite ?length_fmap.
          intros res1 ret1 Hres1.

          ired. replace_r; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_tgt; [rewrite list_lookup_insert //| |]; s.
          { rewrite ?length_fmap //. }
          { rewrite String.eqb_refl //. }
          rewrite list_insert_insert.
          rewrite /alist_upd /_alist_upd eq_rel_dec_correct; des_ifs.
          rewrite insert_insert.

          eapply gsim_Yield_both; eauto.
          { rewrite length_fmap //. }
          { rewrite length_fmap //. }
          { (* immediate return of helpee *)
            rewrite ?interpV_ret; ired.

            gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.

            gbase. eapply (CIH res1); eauto.
            eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
            { intros i; destruct (decide (i = stid)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. }
            }
          }

          (* appeal to coinduction *)
          intros [ro_s Htid_cur]; exists ro_s; split; first done.
          intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
          intros res2 x Hres2; ss.

          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH res2); eauto.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              eapply (help_rel_loop _ _ _ _ x); eauto.
            }
          }
        }

        (* Appeal to coinduction *)
        intros [ro_s Htid_cur]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
        intros res2 x Hres2; ss.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); eauto.

        set (rid_fresh := fresh _).
        eexists (<[stid := (_, _, Some (rid_fresh, (_, j)))]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_insert_true; eauto; first apply is_fresh. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          {
            rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend rid_fresh j); eauto.
              { rewrite /helpee_pend_s. grind.
                instantiate (1:=x).
                repeat f_equal. extensionality a; grind.
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal.
                extensionality a; grind.
              }
            }
            esplits; eauto.
          }
        }
      }

      destruct (decide (fn = Helping.help mn)); subst.
      { (* Helping.help *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; clear e.
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /HelpingOff.help /HelpingOn.help.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        (* Helper chooses tid *)
        replace_r; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|intros rid].
        rewrite list_insert_insert.

        (* Source-helper goes to yield *)
        rewrite yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].
        replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|exists (Some true)].
        rewrite list_insert_insert. ired.

        (* Handling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        step_l. norm_l. rewrite list_insert_insert.
        rewrite HoareCall_unfold. ired.
        replace_r; [rewrite interpV_bind HoareCall_prologue_sred //|].
        eapply gsim_HoareCall_prologue_both; eauto.
        { rewrite list_lookup_insert // length_fmap //. }
        { rewrite list_lookup_insert // length_fmap //. }
        intros res1 [fsp_yield varg] Hres1; rewrite ?list_insert_insert. ired.

        (* Calling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //]. step_l; norm_l.
        rewrite {1}/LMod.prog /=; destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_run_neq; eauto. }
        clear e.
        destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_help_neq; eauto. }
        norm_l. rewrite list_insert_insert.
        unfold_trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].

        (* Yield entrance *)
        rewrite /cfunU /SchI.yield.
        destruct (varg↓) as [[]|] eqn : Hvarg; cycle 1.
        { ired. iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //=].
          destruct (excluded_middle_informative _); ss; step_l; ss.
        }

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        destruct (_ !! mtid) as [[stid2 ?]|] eqn : Hmtid; ss; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        case_decide; subst; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ired.

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
          ired.
          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ired.

          ired. replace_l; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.
          rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e e2.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

          (* No helping here *)
          rewrite /HelpingOn.try_run; ired.
          replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|]. ired.
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //|ss|].
          intros res2 x Hres2. rewrite ?list_insert_insert /=. ired.

          ired. replace_r; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_tgt;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto. { ss; destruct (dec _ _); clarify. }
          rewrite list_insert_insert.

          destruct (reqmap !! rid) as [[[ret|]]|] eqn : Hridreqmap; cycle 1.
          { subst; clarify. }
          { ired. replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
            eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|ss].
          }
          clear dependent caseb. ired.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists (Some true); rewrite list_insert_insert].
          ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite list_insert_insert.

          rewrite HoareCall_unfold; ired.
          replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
          eapply gsim_HoareCall_prologue_HoareFun_epilogue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss|].
          clear dependent res2 x. intros res2 ret2 Hres2.
          rewrite ?list_insert_insert. ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite {1}/LMod.prog /=.
          destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
          clear e'.
          destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
          norm_l. rewrite list_insert_insert.

          rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite /SchI.yield /cfunU.
          destruct (ret2 ↓) as [[]|] eqn : Hret; cycle 1.
          { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_fmap //].
            ss; destruct (excluded_middle_informative _); step_l; ss.
          }
          ired. clear Hret.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert; ired.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.
          rewrite Hmtid; des_ifs_safe; ss. clear e. ired.

          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (mtid, stid); ss; rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ired.

          ired. replace_l; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.
          rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e2.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.

          rewrite ?interpV_ret; ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.

          replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
          eapply gsim_HoareCall_epilogue_both;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss
            |].
          clear dependent res1 res2.
          intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
          rewrite ?interpV_ret. ired.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists None; rewrite list_insert_insert].
          ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.

          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH res1); eauto.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
          Unshelve. all: try exact smj_bot; eauto.
        }

        (* Going to helpee *)
        destruct (reqmap !! rid) as [[[|] jid]|] eqn : Hrid; ss. hss.
        pose proof Hrid as Hrid'.
        eapply reqmap_rel_Some_2 in Hrid' as [stid_helpee [i_s [i_t Hhelpee]]]; eauto.

        eapply Hlookup in Hhelpee as Hhelpee'.
        destruct Hhelpee' as [Hhelpee' [mtid_helpee Hthshelpee]].
        inv Hhelpee'; des; clarify.
        eapply lookup_lt_Some in Hhelpee as Hhelpeelen.
        assert (Hneq : stid_helpee ≠ stid) by (ii; clarify).

        ired.
        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_fmap //
          |unshelve eexists].
        { exists (mtid_helpee, stid_helpee). rewrite /= list_lookup_fmap Hthshelpee //. }
        rewrite list_insert_insert; ired.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e e2.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

        iter_l. rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_fmap Hhelpee /=.
        step_l; norm_l.

        replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|].
        eapply gsim_HoareCall_epilogue_HoareFun_prologue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap; repeat f_equal; grind
          |ss
          |].
        clear dependent res1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.

        rewrite {1}yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //|rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired.

        (* target proceed for helping *)
        rewrite /HelpingOn.try_run /cgetU; ired.
        replace_r; [rewrite interpV_bind interpV_vis //|]; ired.
        eapply gsim_SGet_tgt; [rewrite list_lookup_insert // length_fmap //| ss |].
        { rewrite String.eqb_refl //. }
        esplits; ss; [destruct (dec _ _); ss; clarify|].
        rewrite list_insert_insert. ired. rewrite ?interpV_ret; ired. hss. ired.

        rewrite Hrid. ired.
        eapply gsim_jobs_both;
          [rewrite length_insert length_fmap //
          |rewrite length_fmap //
          |ss
          |].
        clear dependent res1; intros res1 ret1 Hres1.

        ired; replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        rewrite yield_unfold; ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists (Some true); rewrite list_insert_insert].
        ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite list_insert_insert.

        rewrite HoareCall_unfold; ired.
        replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
        eapply gsim_HoareCall_prologue_HoareFun_epilogue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss|].
        clear dependent res1. intros res1 ret Hres1.
        rewrite ?list_insert_insert. ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite {1}/LMod.prog /=.
        destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
        clear e'.
        destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
        norm_l. rewrite list_insert_insert.

        unfold_trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite /SchI.yield /cfunU.
        destruct (ret ↓) as [[]|] eqn : Hret; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_insert length_fmap //].
          ss; destruct (excluded_middle_informative _); step_l; ss.
        }
        ired. clear Hret.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert; ired.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        rewrite Hthshelpee; case_decide as H'; ss; clear H'. ired.

        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_insert length_fmap //
          |unshelve eexists].
        { exists (mtid, stid); ss; rewrite list_lookup_fmap Hmtid //=. }
        rewrite list_insert_insert. ired.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_insert length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        rewrite ?interpV_ret; ired.

        iter_l; rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_l; norm_l.
        rewrite list_insert_commute //.
        rewrite list_insert_insert.
        rewrite list_insert_commute //.

        replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
        eapply gsim_HoareCall_epilogue_both;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss
          |].
        clear dependent res1 x1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
        rewrite ?interpV_ret. ired.

        replace_l; [rewrite interpV_tau //|]; ired.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.

        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.

        rewrite /alist_upd /=; destruct (dec _ _); ss; clear e.
        apply gsim_flag.
        gbase. eapply (CIH res1); eauto.
        set (i_helpee := tau;; _).
        eexists (<[stid := (ktr_s1 () ↑, ktr_t1 () ↑, None)]>
          (<[stid_helpee := (i_helpee, _, Some (rid, (_, jid)))]> tl)).
        esplits; eauto.
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
            clarify; split; ss.
            eapply help_rel_helpee_done; eauto.
            esplits; eauto.
          }
          intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
        }
      }

      destruct (decide (fn = SchHdr._spawn)); subst.
      { (* SchI.inner_spawn *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.inner_spawn.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [[fn args]|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite /ccallU. ired.

        iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap; ss.
        step_l; step_r. norm_l; norm_r.
        rewrite ?list_insert_insert.

        destruct ((wmask_and msk wmask_all) fn) eqn : Hfn; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs fn) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs fn) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase.
        eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            destruct (decide (Some fn ∈
              List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
            { eapply (help_rel_call _ _ _ _ _ _ ctx); eauto. intros ret; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            hexploit (prog_fn_ctx fn ctx rs); eauto.
            intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht Hs]]]]]]; des; clarify.
            rewrite Ht Hs in Hfn_t; inv Hfn_t; ss.
            ides (itr_ctx args ↑).
            { rewrite ?interpV_ret; ired.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply (help_rel_eq); eauto.
              i; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply (help_rel_eq); eauto.
              i; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
          }
        }
      }

      destruct (decide (fn = SchHdr.spawn)); subst.
      { (* SchI.spawn *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.spawn.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [[fn args]|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite /ccallU.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        ired. replace_r; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_tgt;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert. ired.
        rewrite /SModTr.NativeSpawn; ired.

        destruct ((wmask_and msk wmask_all) SchHdr._spawn) eqn : Hfn; cycle 1.
        {
          iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs SchHdr._spawn) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs SchHdr._spawn) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert. ired.

        ired. replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; s.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { ss. }
        rewrite insert_app_l // ?length_insert ?length_fmap //.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; s.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { ss. }
        rewrite insert_app_l // ?length_insert ?length_fmap //.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.
        rewrite ?list_insert_insert.
        rewrite ?interpV_ret. ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase.
        eapply (CIH rs); eauto.
        eexists ((<[stid := (_, _, None)]> tl) ++ [(i (fn, args)↑, i0 (fn, args)↑, None)]); ss.
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
            eapply (help_rel_call _ _ _ _ (λ a, Ret a) (λ a, Ret a) ctx rs SchHdr._spawn); eauto.
            { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss; set_solver. }
            { grind. }
            { grind. }
            intros res; eapply help_rel_ret; eauto.
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

      destruct (decide (fn = SchHdr.join)); subst.
      { (* SchI.join *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.join.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [?|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite unfold_iterC; ired.
        rewrite {1 2}interpV_tau.
        eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
        eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
        rewrite !list_insert_insert.

        replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        rewrite ?list_insert_insert. ired.

        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        rewrite ?list_insert_insert. ired.

        destruct (ths !! n3) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ired.
        { (* Join-return *)
          rewrite ?interpV_ret; ired.
          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
        { (* Join-loop *)
          rewrite /ccallU.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert. ired.

          destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
          { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
            step_l; ss.
          }

          iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
          iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
          step_l; step_r. norm_l; norm_r.
          destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
          { step_l; ss. }
          destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
          { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
          norm_l; norm_r.
          rewrite !list_insert_insert. ired.
          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify.
              split; ss. eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
              { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
                do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
              }
              intros ret; ss; eapply (help_rel_join _ _ ret _ _ n3); eauto.
              { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
                extensionalities a; destruct a; grind.
              }
              { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
                extensionalities a; destruct a; grind.
              }
            }
          }
        }
        (* join-None *)
        rewrite ?interpV_ret; ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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

      destruct (decide (fn = SchHdr.yield)); subst.
      { (* SchI.yield *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.yield.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) eqn : Harg; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ss. ired. rewrite /cgetU /=. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //; step_r; norm_r.
        rewrite list_insert_insert.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //; step_r; norm_r.
        rewrite list_insert_insert. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

        destruct (ths !! mtid) as [[smtid reto_s]|] eqn : Hmtid; cycle 1.
        { rewrite Hmtid /=.
          ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        rewrite Hmtid //=.
        destruct (decide (smtid = stid)); subst; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }

        ired.

        replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
        eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|].
        intros [[mtidn stidn] Hmtidn]; rewrite list_insert_insert; ired; ss.

        replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
        eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|].
        unshelve eexists (exist _ (mtidn, stidn) _); ss; eauto.
        rewrite list_insert_insert; ired; ss.

        ired. replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert. hss.
        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert. hss. ired. rewrite ?interpV_ret. ired.

        iter_r; rewrite list_lookup_insert //= ?length_fmap //. step_r; norm_r.
        rewrite list_insert_insert. hss.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //. step_r; norm_r.
        rewrite list_insert_insert. hss. ired. rewrite ?interpV_ret. ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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

      destruct (decide (fn = SchHdr.get_tid)); subst.
      { (* SchI.get_tid *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.get_tid.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) eqn : Harg; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ss. ired. rewrite /cgetU /=. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_SGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.
        rewrite ?interpV_ret; ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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

      exfalso; revert H1; rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
      set_solver.
    }

    { (* inner spawn - continuation *)
      rewrite /inner_spawn_pend in Htid.
      iter_l; rewrite list_lookup_fmap Htid /=. step_l; norm_l.
      iter_r; rewrite list_lookup_fmap Htid /=. step_r; norm_r.

      destruct (arg ↓) eqn : Harg; ss; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      des_ifs; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert. ired.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); eauto.
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
          { rewrite Hi2 in Heq; clarify. exists mtid, (Some t); rewrite list_lookup_insert //. }
          exists mtid2, ro2; rewrite list_lookup_insert_ne //.
        }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_terminate; eauto.
        }
      }
    }

    { (* join - continuation*)
      rewrite /join_pend in Htid.
      iter_l; rewrite list_lookup_fmap Htid /=. step_l; norm_l.
      iter_r; rewrite list_lookup_fmap Htid /=. step_r; norm_r.

      destruct (arg ↓) eqn : Harg; ss; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      rewrite unfold_iterC; ired.
      rewrite {1 2}interpV_tau.
      eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
      eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
      rewrite !list_insert_insert.

      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      destruct (ths !! tid) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ired.
      { (* Join-return *)
        rewrite ?interpV_ret; ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
      { (* Join-loop *)
        rewrite /ccallU.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert. ired.

        destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert. ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
            { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
              do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
            }
            intros ret; ss; eapply (help_rel_join _ _ ret _ _ tid); eauto.
            { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
              extensionalities a; destruct a; grind.
            }
            { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
              extensionalities a; destruct a; grind.
            }
          }
        }
      }
      (* join-None *)
      rewrite ?interpV_ret; ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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

    { (* inner_spawn - continuation*)
      revert Htid; rewrite /Sch.terminate; unseal SCH; rewrite unfold_iterC. ired.
      rewrite {1 2}interpV_tau; intros Htid.
      eapply gsim_tau_src; [rewrite list_lookup_fmap Htid //|].
      eapply gsim_tau_tgt; [rewrite list_lookup_fmap Htid //|].

      iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
      rewrite list_insert_insert.
      iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
      rewrite list_insert_insert. ired.

      destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
      { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
        step_l; ss.
      }

      iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
      iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
      step_l; step_r. norm_l; norm_r.
      destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
      { step_l; ss. }
      destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
      { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
      norm_l; norm_r.
      rewrite !list_insert_insert. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; ss.
          eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
          { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
            do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
          }
          i; ss.
          eapply (help_rel_eq _ _ _ _ (tau;; Ret ret)).
          { unfold_trans; rewrite ?interpV_tau ?interpV_ret.
            instantiate (1:= λ x : Any.t,
              x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none)
                (x <- Sch.terminate;; Ret x↑)));;
              ktr_t x).
            rewrite /Sch.terminate; unseal SCH. grind.
          }
          { unfold_trans; rewrite ?interpV_tau ?interpV_ret.
            instantiate (1:= λ x : Any.t,
              x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none)
                (x <- Sch.terminate;; Ret x↑)));;
              ktr_s x).
            rewrite /Sch.terminate; unseal SCH. grind.
          }
          { instantiate (1:=[]); set_solver. }
          { ii; clarify. }
          i; ss.
          eapply help_rel_terminate; eauto.
        }
      }
    }

    { (* Return case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      des_ifs; ss.
      { rewrite /LModTr.interp_stateE ?interp_state_ret; ired.
        gstep; econs; econs; ss.
      }
      rewrite /triggerUB; ss; step_l; ss.
    }

    rename itr into itr_c.
    rename H5 into Hscp.
    destruct (case_itrH itr_c) as [[v ->]|Hf].
    { (* return case *)
      exfalso; eapply H4; eauto.
    }
    destruct Hf as [[f' ->]|Hf].
    { (* tau case *)
      eapply gsim_tau_src; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      eapply gsim_tau_tgt; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply CIH; eauto.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides f'.
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Assume *)
      eapply gsim_Assume_src; [rewrite list_lookup_fmap Htid //=|].
      intros r_s2 -> Hr_s2.
      eapply gsim_Assume_tgt; [rewrite list_lookup_fmap Htid //=|].
      exists r_s2; esplits; try by des.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH r_s2); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides f'.
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[res [f' ->]]|Hf].
    { (* AssumeRes *)
      eapply gsim_AssumeRes_src; [rewrite list_lookup_fmap Htid //=|].
      { unfold_trans. instantiate (1:=k_s). repeat f_equal. extensionalities a; destruct a; ss. }
      intros Hval.
      eapply gsim_AssumeRes_tgt; [rewrite list_lookup_fmap Htid //=|].
      { unfold_trans. instantiate (1:=k_t). repeat f_equal. extensionalities a; destruct a; ss. }
      split; first done.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH (res ⋅ rs)); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides (f' ()).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Guarantee *)
      eapply gsim_Guarantee_tgt; [rewrite list_lookup_fmap Htid //=|].
      intros r2 ?.
      eapply gsim_Guarantee_src; [rewrite list_lookup_fmap Htid //=|].
      esplits; try by des.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH r2); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides (f').
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[R [[fn args|fn args|tid_yield|] [k ->]]]|Hf].
    { (* call case *)
      rename msk0 into msk_c, img into img_c, scp into scp_c.
      revert Htid; unfold_trans; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      ss; destruct (msk_c fn); cycle 1.
      { norm_l. step_l. ss. }
      ss.
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          destruct (decide (Some fn ∈
            List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
          { eapply (help_rel_call _ _ _ _ _ _ ctx); eauto. intros ret; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret)); eauto.
            { grind. unfold_trans. rewrite ?interpV_tau; grind. }
            { grind. unfold_trans. rewrite ?interpV_tau; grind. }
          }
          hexploit (prog_fn_ctx fn ctx rs); eauto.
          intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht [Hs ?]]]]]]]; clarify.
          rewrite Ht Hs in H_prog_t'; inv H_prog_t'.
          ides (itr_ctx args).
          { rewrite ?interpV_ret; ired.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k r0) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
          { eapply (help_rel_eq _ _ _ _ (tau;; t)); eauto.
            ii; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
          { eapply (help_rel_eq _ _ _ _ (Vis e k0)); eauto.
            ii; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
        }
      }
      eauto.
    }
    { (* Spawn case *)
      rename img into img_c, msk0 into msk_c, scp into scp_c.
      revert Htid; rewrite /ModTr.trans /SB.sandbox; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      destruct (msk_c fn); ss; cycle 1.
      { step_l; ss. }
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists ((<[stid := (_, _, None)]> tl) ++ [(fn_s args, fn_t args, None)]); ss.
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
          destruct (decide (Some fn ∈
            List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
          { eapply (help_rel_call _ _ _ _ (λ a, Ret a) (λ a, Ret a) ctx); eauto.
            { grind. }
            { grind. }
            intros ret; ss. apply help_rel_ret.
          }
          hexploit (prog_fn_ctx fn ctx rs); eauto.
          intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht [Hs ?]]]]]]]; clarify.
          rewrite Ht Hs in H_prog_t'; inv H_prog_t'.
          ides (itr_ctx args).
          { rewrite ?interpV_ret; ired.
            apply help_rel_ret.
          }
          { eapply (help_rel_eq _ _ (λ a, Ret a) (λ a, Ret a) (tau;; t)); eauto.
            { grind. }
            { grind. }
            ii; apply help_rel_ret.
          }
          { eapply (help_rel_eq _ _ (λ a, Ret a) (λ a, Ret a) (Vis e k0)); eauto.
            { grind. }
            { grind. }
            ii; apply help_rel_ret.
          }
        }
        destruct (decide (i = stid)); subst.
        { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
          intros EQ; clarify.
          split; ss.
          rewrite ?length_fmap.
          ides (k (length tl)).
          { rewrite ?interpV_ret; ired. eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
        rewrite -insert_app_l // list_lookup_insert_ne //.
        intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
        apply Hlookup; eauto.
      }
      eauto.
    }

    { (* Yield case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. ired. split; ss.
          ides (k ()).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
      }
    }

    { (* GetTid case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (k stid).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
      }
    }

    destruct Hf as [[R [s [f' ->]]]|[R [e [f' ->]]]].
    { (* sput sget *)
      destruct s as [k v|k].
      { (* sput *)
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode.
        iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap //.
        step_l; step_r; norm_l; norm_r. ired.
        rewrite ?list_insert_insert.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
            ides (f' ()).
            { rewrite ?interpV_ret; ired; eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
          }
        }
      }
      { (* sget *)
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode. ired.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
            ides (f' (or_else (alist_find k st_ctx) ()↑)).
            { rewrite ?interpV_ret; ired; eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
          }
        }
      }
    }

    destruct e as [X | X | fn args].
    { (* Choose case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      eapply gsim_Choose_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x].
      eapply gsim_Choose_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
    { (* Take case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      eapply gsim_Take_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x ?].
      eapply gsim_Take_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x; split; ss].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
    { (* IO case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      norm_l; norm_r. guclo gsim_indC_spec. econs; intros ?? ->.
      instantiate (1:=smj_top). instantiate (1:=smj_top).
      norm_l. norm_r. step_l. step_r. norm_l; norm_r. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x_tgt).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
  Unshelve. all: eauto.
  (*SLOW*)Qed. *)

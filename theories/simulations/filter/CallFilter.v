Require Import Common ISim WSim Tactics TacticsCommon WSimNotations TacticsInit Tactics.
Require Import GSim GSimFacts GSimTactics.
Require Export ConcRA LMod Mod SMod.
Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
(* From iris.proofmode Require Export proofmode.
Require Import LMod LSim GSim GSimFacts GSimTactics Mod ISim ISimFacts.
Require Import TacticsInit Tactics. *)

Module CFilter. Section CFilter.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition msk_filter (s : gset string) (msk : emask) : emask := λ X e,
    match e with
    | inr1 (inl1 (Call fn _)) => bool_decide (fn ∉ s ∧ msk X e)
    | _ => msk X e
    end.

  (* filters module m with mask, which means function call fn ∉ mask are undefined behaviors *)
  Program Definition filter (mask : gset string) (m : Mod.t) : Mod.t := {|
    Mod.scopes := m.(Mod.scopes);
    Mod.fnsems :=
      (λ (x : option _), map_fst (msk_filter mask) <$> x) <$> m.(Mod.fnsems);
    Mod.initial_st := m.(Mod.initial_st)
  |}.
  Next Obligation.
    intros ? ? i [msk x]; rewrite lookup_omap ?lookup_fmap => ?.
    destruct m; ss.
    destruct (fnsems !! i) as [[[??]|]|] eqn : ?; ss; clarify; ss.
    eapply (well_scoped_fns i (_, _)); rewrite lookup_omap Heqo //=.
  Qed.
  Next Obligation. intros ? m; destruct m; ss. Qed.
  Next Obligation. intros ? m; destruct m; ss. Qed.

  (* Lemmas *)
  Lemma filter_app m1 m2 msk :
    CFilter.filter msk (m1 ★ m2) = CFilter.filter msk m1 ★ CFilter.filter msk m2.
  Proof using.
    destruct m1, m2. eapply Mod.t_eq; ss.
    eapply map_eq; intros i; rewrite ?lookup_fmap ?lookup_union_with ?lookup_fmap.
    do 2 destruct (_ !! i); ss.
  Qed.

  (* Key theorems *)
  Lemma sim_filter_intro (mask : gset string) (m : Mod.t) :
    ISim.t open (filter mask m) m emp%I IstEq.
  Proof using.
    econs; ss; i; eauto.
    rewrite /ISim.sim_fun ?lookup_fmap.
    destruct (_ !! _) as [[[msk bd]|]|]; ss; intros ??; eexists; split; [refl|].
    iIntros (arg st_src st_tgt) "->"; iApply wsim_isim. iStopProof.
    rewrite {3 4}/SB.sandbox_body /=.
    generalize (bd arg) as itr.
    combine_quant st_tgt.
    generalize false at 1 as ps. intros ps; combine_quant ps.
    generalize false at 1 as pt. intros pt; combine_quant pt.
    combine_quant msk.
    clear bd arg.
    eapply wsim_coind; intros g0 _ CIH [msk [pt [ps [st itr]]]].
    s; destruct_quant CIH.
    iIntros "_".
    assert (CASE:= case_itrH itr). des; subst; s.
    - step; et.
    - steps_l. steps_r. by_coind CIH; et.
    - steps_l; ss.
      case_match; steps_l; ss.
      steps_r; case_match; ss; force_r; iFrame; steps_r.
      by_coind CIH. iFrame.
    - steps_l; ss.
      case_match; steps_l; ss.
      steps_r; case_match; ss; force_r; iFrame; steps_r.
      by_coind CIH. iFrame.
    - steps_l; ss.
      case_match; steps_l; ss.
      steps_r. case_match; steps_r; ss.
      force_l; iFrame; steps_l.
      by_coind CIH. iFrame.
    - destruct c; s; steps_l; case_match; try case_bool_decide; steps_l; ss.
      + steps_r; case_match; des; ss.
        steps_r. call "".
        iIntros (ret ??) "->"; steps_l; steps_r.
        by_coind CIH. iFrame.
      + steps_r; case_match; des; ss.
        steps_r. iApply (wsim_spawn).
        iIntros (tid); steps_l; steps_r; by_coind CIH; iFrame.
      + steps_r; case_match; des; ss.
        steps_r. iApply (wsim_yield); iSplit; [eauto|].
        iIntros (??) "->"; steps_l; steps_r; by_coind CIH; iFrame.
      + steps_r; case_match; des; ss.
        steps_r. iApply (wsim_gettid); eauto.
        iIntros (?); steps_l; steps_r; by_coind CIH; iFrame.
    - destruct s; steps_l; steps_r; case_match; steps_l; ss; steps_r.
      { iApply wsim_sput_src; iApply wsim_sput_tgt; norm_l; norm_r; by_coind CIH; iFrame. }
      { iApply wsim_sget_src; iApply wsim_sget_tgt; norm_l; norm_r; by_coind CIH; iFrame. }
    - destruct e; steps_l; steps_r; case_match; steps_l; ss; steps_r.
      { forces_l; steps_l; by_coind CIH; iFrame. }
      { forces_r; steps_r; by_coind CIH; iFrame. }
      { step; steps_l; steps_r; by_coind CIH; iFrame. }
  Qed.

  Lemma sim_filter_elim (mask : gset string) (m : Mod.t)
      (SUB : (set_omap id (dom (m.(Mod.fnsems)))) ## mask) :
    ISim.t closed m (filter mask m) emp%I IstEq.
  Proof using.
    econs; ii; et.
    rewrite /ISim.sim_fun ?lookup_fmap.
    destruct (_ !! _) as [[[msk bd]|]|]; ss; intros ??; eexists; split; [refl|].
    iIntros (arg st_src st_tgt) "-> _". iStopProof.
    rewrite {3 4}/SB.sandbox_body /=.
    generalize (bd arg) as itr.
    combine_quant st_tgt.
    generalize false at 1 as ps. intros ps; combine_quant ps.
    generalize false at 1 as pt. intros pt; combine_quant pt.
    combine_quant msk.
    clear bd arg.
    eapply isim_coind; intros g0 _ CIH [msk [pt [ps [st itr]]]].
    s; destruct_quant CIH.
    iIntros "_".
    assert (CASE:= case_itrH itr). des; subst; s.
    { step; eauto. }
    { step_l; steps_r. by_coind CIH. done. }
    { step_l.
      case_match; step_l; ss.
      steps_r; case_match; ss; force_r; iFrame; norm_l; norm_r; by_coind CIH. done.
    }
    { step_l.
      case_match; step_l; ss.
      steps_r; case_match; ss; force_r; iFrame; norm_l; norm_r; by_coind CIH. done.
    }
    { step_l.
      case_match; step_l; ss.
      steps_r; case_match; ss; steps_r; force_l; iFrame. norm_l; norm_r; by_coind CIH. done.
    }
    { destruct c; s; steps_l; case_match; try case_bool_decide; steps_l; ss.
      { steps_r; case_bool_decide; des; ss.
        { steps_r. iApply isim_call. iSplit; first done.
          iIntros (ret ??) "->"; steps_l; steps_r. by_coind CIH; iFrame; done.
        }
        { iApply isim_call_none; ss.
          rewrite ?lookup_fmap; destruct (_ !! _) eqn : Heq; ss.
          eapply elem_of_dom_2 in Heq.
          exfalso; eapply (SUB fn0); set_solver.
        }
      }
      { steps_r; case_match; des; ss.
        steps_r.
        iApply isim_spawn; iIntros (tid). norm_l; norm_r. by_coind CIH. done.
      }
      { steps_r; case_match; des; ss. steps_r.
        iApply isim_yield; iSplit; [done|]; iIntros (??) "->".
        norm_l; norm_r. by_coind CIH. done.
      }
      { steps_r; case_match; des; ss. steps_r.
        iApply isim_gettid; iIntros (tid).
        norm_l; norm_r. by_coind CIH. done.
      }
    }
    { destruct s; steps_l; steps_r; case_match; steps_l; ss; steps_r.
      { iApply isim_sput_src; iApply isim_sput_tgt; norm_l; norm_r; by_coind CIH; by iFrame. }
      { iApply isim_sget_src; iApply isim_sget_tgt; norm_l; norm_r; by_coind CIH; by iFrame. }
    }
    { destruct e; steps_l; steps_r; case_match; steps_l; ss; steps_r.
      { forces_l; steps_l; by_coind CIH; by iFrame. }
      { forces_r; steps_r; by_coind CIH; by iFrame. }
      { step; steps_l; steps_r; by_coind CIH; by iFrame. }
    }
  Qed.

  (*** introduction of a module ***)
  Lemma intro_filter fns (m : Mod.t) P :
    ctx_refines (filter fns m, P)%I (m, P)%I.
  Proof using.
    rewrite !(mod_addc_empty_r _ P).
    eapply ctxr_cond_frameL.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_filter (mask : gset string) (m : Mod.t) P
      (SUB : (set_omap id (dom (m.(Mod.fnsems)))) ## mask) :
    refines (m, P)%I (filter mask m, P)%I.
  Proof using. eapply closed_adequacy_emp, sim_filter_elim. eauto. Qed.

  (*** elimination of a module ***)
  Theorem elim_module mc P : ctx_refines (⌽, P) (mc, P).
  Proof using.
    do 2 rewrite (mod_addc_empty_l _ P).
    eapply ctxr_cond_frameR.
    eapply main_adequacy with (Ist := λ _ _, emp%I).
    init_sim; ii; et.
  Qed.

  (* TODO : move to GSimTactics.v *)
  Ltac giter_l :=
    replace_l; [rewrite unfold_iterV /itreeV_itree //|]; s;
    try match goal with
    | |- context [(<[?i := _]> _ )!! ?i] =>
        rewrite list_lookup_insert //=
    | |- context [<[?i := _]> (<[?i := _]> _ )] =>
        rewrite list_insert_insert //
    end;
    gnorm_l.

  (*** introduction of a module ***)
  Theorem intro_module (mask : gset string) m mc P
      (WF: Mod.wf mc)
      (DISJ: (m.(Mod.scopes) ## mc.(Mod.scopes)))
      (EXCL: set_omap id (dom (Mod.fnsems m)) ## mask)
      (EXCL2: set_omap id (dom (Mod.fnsems mc)) ⊆ mask)
      (EXCL3: None ∉ dom (Mod.fnsems mc))
      (* (SUB: ∀ fn, In (Some fn) (m.(Mod.fnsems).*1) → mask fn)
      (FRESH: ∀ fn, In (Some fn) (mc.(Mod.fnsems).*1) → (~ mask fn))
      (FRESHI: ~ In None (mc.(Mod.fnsems)).*1)
       *)
      :
    refines ((filter mask m) ★ mc, P)%I (filter mask m, P)%I.
  Proof using.
    ii; ss.
    split.
    (* Well-formedness proof - TODO : make a lemma *)
    { econs; ss.
      { rewrite map_Forall_lookup; intros i x; rewrite lookup_union_with ?lookup_fmap /=.
        destruct (_ m !! i) as [o|] eqn : Hm; ss.
        { destruct (_ mc !! i) as [oc|] eqn : Hmc; ss.
          { exfalso.
            destruct i as [i|].
            { eapply (EXCL i).
              { eapply elem_of_set_omap; esplits; eauto; eapply elem_of_dom; eauto. }
              { eapply EXCL2, elem_of_set_omap; esplits; eauto; eapply elem_of_dom; eauto. }
            }
            { eapply EXCL3; eapply elem_of_dom_2 in Hmc; eauto. }
          }
          { destruct o; ss; i; clarify.
            inv WFM; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns i None); ss.
            rewrite ?lookup_fmap Hm //=.
          }
        }
        { destruct (_ mc !! i) as [[?|]|] eqn : Hmc; ss; i; clarify.
          inv WF; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns i None); ss.
        }
      }
      { intros x; rewrite multiplicity_disj_union.
        destruct (decide (x ∈ Mod.scopes m)) as [e|e]; [rewrite elem_of_multiplicity in e|].
        { destruct (decide (x ∈ Mod.scopes mc)) as [e2|e2]; first multiset_solver.
          rewrite elem_of_multiplicity in e2; inv WFM; hexploit (wf_scopes x); ss; nia.
        }
        destruct (decide (x ∈ Mod.scopes mc)) as [e2|e2]; last multiset_solver.
        rewrite elem_of_multiplicity in e2; inv WF; hexploit (wf_scopes x); ss; multiset_solver.
      }
    }
    (* Simulation proof *)
    intros rs ? Hrs; exists rs; splits; eauto.
    cut (∀ ps pt arg,
         gsim eq ps pt (LMod.compile (Mod.to_lmod (filter mask m ★ mc) rs) arg)
           (LMod.compile (Mod.to_lmod (filter mask m) rs) arg)).
    { ii. eapply gsim_adequacy; et. }

    i. ginit. rewrite /LMod.compile. s.
    rewrite ?lookup_fmap ?lookup_omap ?lookup_union_with ?lookup_fmap.
    destruct (_ mc !! None) eqn : Hmc; [eapply elem_of_dom_2 in Hmc; set_solver|ss; clear Hmc].
    destruct (_ m !! None) as [[[msk bd]|]|] eqn : Hm; ss; [|gstep_l; ss|gstep_l; ss].

    rewrite /LModTr.trans /LModTr.interp_callE /ModTr.trans_fnsem /SB.sandbox_body /ITree.map. ired.
    guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }
    
    match goal with
      [|-context [ModTr.trans ?t]] => remember [ModTr.trans t] as ths
    end.
    (* destruct p as [[[img msk] sc] bd]. *)
    assert (WFTHS:
      ∀ tid t (IN: ths !! tid = Some t),
      ∃ ht, t = ModTr.trans (SB.sandbox (msk_filter mask msk) ht)).
    { i. subst. destruct tid; ss. inv IN. esplits; eauto. }
    clear Heqths.
    generalize 0 as cid.
    rename rs into rs0.
    generalize rs0 at 2 4 as rs.
    assert (SCP := m.(Mod.well_scoped_init)). revert SCP.
    generalize (Mod.initial_st m) as st.
    assert (SCPc := mc.(Mod.well_scoped_init)). revert SCPc.
    generalize (Mod.initial_st mc) as stc.
    generalize (eq_refl ths) as Heqths.
    generalize ths at 1 3 as ths0.
    revert_until WFM.
    gcofix CIH. i. subst.
  Admitted.
    (* TODO : Admitted first and see if CallFilter.v and HelpingOnOff can share the same lemma *)
    (* giter_l. giter_r.
    (* ziter_l. ziter_r. *)
    destruct (ths !! cid) eqn: EQ; cycle 1.
    { unfold triggerUB. gstep_l. gstep_l. ss. }
    assert (WFLEN := lookup_lt_Some _ _ _ EQ).

    eapply WFTHS in EQ. des. subst.
    ides ht.
    {
      des_ifs; cycle 1.
      { unfold triggerUB. do 2 gstep_l. ss. }
      gstep_l. gnorm_l. gstep_r. gnorm_r. gstep. econs; econs; eauto.
    }
    {
      gstep_l. gstep_r. gnorm_l; gnorm_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }

    rewrite ?SBRed.vis; destruct (msk_filter) eqn : Hmsk; cycle 1.
    { gnorm_l. gstep_l. ss. }
    destruct e; [destruct a | destruct s;
                              [destruct c|destruct s; [destruct p|destruct c]]].
    { (* Assume *)
      gnorm_l. gsteps_l. gsteps_r. hss. ired. hss. ired.
      giter_l. gstep_l; intros x; gsteps_l.
      replace_l; [rewrite unfold_iterV /itreeV_itree //|]; s;
      try match goal with
      | |- context [(<[?i := _]> _ )!! ?i] =>
          rewrite list_lookup_insert //= ?length_insert //
      | |- context [<[?i := _]> (<[?i := _]> _ )] =>
          rewrite list_insert_insert; [rewrite length_insert //|]
      end;
      gnorm_l.
      giter_l. gstep_l; intros x; gsteps_l.
      gsteps_l. intros x; gsteps_l.
      gstep_l.
      ziter_l. zstep_l. zstep_l.
      ziter_l. zstep_l. zstep_l. 
      ziter_l. zstep_l.
      ziter_l. zstep_l.

      zstep_r.
      ziter_r. zstep_r. exists x. zstep_r.
      ziter_r. zstep_r. exists x0. zstep_r.
      ziter_r. zstep_r.
      ziter_r. zstep_r.

      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* AssumeRes  *)

      zstep_l.
      ziter_l. zstep_l. zstep_l.
      ziter_l. zstep_l.
      ziter_l. zstep_l.

      zstep_r. ziter_r. zstep_r. exists x.
      zstep_r. ziter_r; zstep_r.
      ziter_r; zstep_r.

      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Guarantee *)
      zstep_r.
      ziter_r. zstep_r. zstep_r.
      ziter_r. zstep_r. zstep_r. 
      ziter_r. zstep_r.
      ziter_r. zstep_r.
      
      zstep_l.
      ziter_l. zstep_l. exists x. zstep_l.
      ziter_l. zstep_l. exists x0. zstep_l.
      ziter_l. zstep_l.
      ziter_l. zstep_l.

      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Call *)
      s. destruct (mask fn) eqn: Hmask; cycle 1.
      { zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { unfold triggerUB. do 2 zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { exfalso. rewrite !List.map_app alist_find_app_o Heq0 in Heq.
        eapply alist_find_some, (in_map fst) in Heq.
        rewrite List.map_map fst_map_snd in Heq. ss.
        eapply FRESH; et.
      }
      zstep_l. zstep_r.

      rewrite !List.map_app alist_find_app_o Heq0 in Heq. depdes Heq.

      zprogress.
      gbase. eapply CIH; et.

      i. eapply list_lookup_insert_Some in IN. des; subst; et.

      rewrite alist_find_map_snd /o_map in Heq0. des_ifs.
      rewrite alist_find_map_snd /o_map in Heq. des_ifs.
      destruct p as [[[img1 msk1] sc1] bd1]. s.

      esplits. rewrite /SB.sandbox_body /ModTr.trans_ktree.
      erewrite SBRed.bind, Red.bind, sandbox_sandbox; s.
      - f_equal. extensionalities.
        erewrite SBRed.tau, Red.tau.
        do 2 f_equal. ired. erewrite sandbox_sandbox; ii; et; try refl.
      - et.
      - ii. eapply andb_prop in H. des; et.
      - s. etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. instantiate (1:=Some fn). rewrite Heq0. refl.
    }
    { (* Spawn *)
      s. destruct (mask fn) eqn: Hmask; cycle 1.
      { zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { unfold triggerUB. do 2 zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { exfalso. rewrite !List.map_app alist_find_app_o Heq0 in Heq.
        eapply alist_find_some, (in_map fst) in Heq.
        rewrite List.map_map fst_map_snd in Heq. ss.
        eapply FRESH; et.
      }
      zstep_l. zstep_r.

      rewrite !List.map_app alist_find_app_o Heq0 in Heq. depdes Heq.

      zprogress.
      gbase. eapply CIH; et.

      i. eapply lookup_snoc_Some in IN. des.
      { eapply list_lookup_insert_Some in IN0. des; subst; et. }
      
      subst. rewrite !alist_find_map /o_map in Heq0. des_ifs.
      destruct p as [[[img1 msk1] sc1] bd1]. s.
      esplits. unfold SB.sandbox_body, ModTr.trans_ktree. s.
      erewrite <-sandbox_sandbox; try refl.
      - ii. apply andb_prop in H. des; et.
      - etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. instantiate (1:=Some fn). rewrite Heq0. refl.
    }
    { (* Yield *)
      zstep_l. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* GetTid *)
      zstep_l. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Put *)
      destruct k0 as [key var]. s.
      destruct (existsb (String.eqb key) (Mod.scopes m)) eqn: Heq; cycle 1.
      { zstep_l. }
      zstep_l. zstep_r.
      ziter_l. zstep_l.
      ziter_r. zstep_r.
      rewrite !ModTr.alist_encode_decode.
      rewrite alist_upd_not_tail; cycle 1.
      { eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0; subst.
        ii. eapply NoDup_app_disjoint; et.
        eapply SCPc. eapply (List.in_map fst) in H. ss.
        rewrite List.map_map in H. et.
      }

      zprogress.
      gbase. eapply CIH; et.
      - i. eapply list_lookup_insert_Some in IN. des; subst; et.
      - unfold state_scopes. ii.
        rewrite -List.map_map alist_upd_keys List.map_map in H. et.
    }
    { (* Get *)
      destruct k0 as [key var]. s.
      destruct (existsb (String.eqb key) (Mod.scopes m)) eqn: Heq; cycle 1.
      { zstep_l. }
      zstep_l. zstep_r. s. ired.   
      rewrite !ModTr.alist_encode_decode.
      rewrite alist_find_app_o (alist_find_fst_notin _ stc); cycle 1.
      { eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0; subst.
        ii. eapply (List.in_map fst) in H. ss.
        rewrite List.map_map in H. eapply SCPc in H.
        eapply NoDup_app_disjoint; et.
      }
      zprogress.
      gbase. eapply CIH; et.
      - i. eapply list_lookup_insert_Some in IN. des; subst; et.
      - do 5 f_equal. des_ifs.
    }
    { (* Choose *)
      zstep_r. zstep_r.
      zstep_l. exists x. zstep_l.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Take *)
      zstep_l. zstep_l.
      zstep_r. exists x. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* IO *)
      zstep. subst.
      zstep_l. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
  Unshelve. all: exact smj_top.
  (*SLOW*)Qed. *)

End CFilter. End CFilter.

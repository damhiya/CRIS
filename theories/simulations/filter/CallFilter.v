Require Import Common ISim WSim Tactics TacticsCommon SimNotations TacticsInit Tactics.
Require Import GSim GSimFacts GSimTactics GSimAux.
Require Export ConcRA LMod Mod SMod.
Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
From stdpp Require Import base list.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Module CFilter. Section CFilter.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition msk_filter (s : gset string) (msk : emask) : emask := λ X e,
    match e with
    | inr1 (inl1 (Call fn _)) => bool_decide (fn ∉ s ∧ msk X e)
    | inr1 (inl1 (Spawn fn _)) => bool_decide (fn ∉ s ∧ msk X e)
    | _ => msk X e
    end.

  (* filters module m with mask, which means function cCall fn ∉ mask are undefined behaviors *)
  Program Definition filter (mask : gset string) (m : Mod.t) : Mod.t := {|
    Mod.scopes := m.(Mod.scopes);
    Mod.fnsems :=
      (λ (x : option _), map_fst (msk_filter mask) <$> x) <$> m.(Mod.fnsems);
    Mod.initial_st := m.(Mod.initial_st)
  |}.
  Next Obligation. i; eapply Mod.sorted_scopes. Qed.
  Next Obligation.
    intros ? ? i [msk x]; rewrite lookup_omap ?lookup_fmap /Mod.fnsems => ?.
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

  Lemma filter_empty m : CFilter.filter ∅ m = m.
  Proof.
    apply Mod.t_eq; ss.
    rewrite /filter /Mod.fnsems; destruct m as [? fnsems ?]; clear.
    generalize fnsems; eapply map_ind; ss.
    intros i [[msk ?]|] m; rewrite fmap_insert /=; intros ? ->; ss.
    repeat f_equal.
    extensionalities X e; destruct e as [|[|[|]]]; auto.
    destruct c; ss; case_bool_decide as H2; destruct msk; ss; des; ss; exfalso; apply H2; split; ss.
  Qed.

  (* Key theorems *)
  Lemma sim_filter_intro (mask : gset string) (m : Mod.t) :
    ISim.t open (filter mask m) m emp%I IstEq.
  Proof using.
    cStartModSim; et.
    { ii. rr. destruct x; et.
      exfalso. rewrite lookup_fmap in H. destruct (_ !! _) eqn: mi; ss.
      eapply Hwf in mi. rr in mi. des; subst. ss.
    }

    rewrite /ISim.sim_fun ?lookup_fmap.
    destruct (_ !! _) as [[[msk bd]|]|] eqn : Ht; ss; cycle 1; last clear Ht.
    intros; eexists; split; [refl|].
    iIntros (arg st_src st_tgt) "->". iApply wsim_isim.
    generalize false at 1 as ps; i. generalize false at 1 as pt; i.
    rewrite /SB.sandbox_body /=. generalize (bd arg) as itr; i. clear bd arg.
    cCoind CIH g0 __ with itr ps pt st_tgt msk. iIntros "_".

    assert (CASE:= case_itrH itr). des; subst; s.
    - cStep; et.
    - cStepsS. cStepsT. cByCoind CIH; et.
    - cStepsS; ss.
      case_match; cStepsS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cStepsT.
      cByCoind CIH. iFrame.
    - cStepsS; ss.
      case_match; cStepsS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cStepsT.
      cByCoind CIH. iFrame.
    - cStepsS; ss.
      case_match; cStepsS; ss.
      cStepsT. case_match; cStepsT; ss.
      cForceS; iFrame; cStepsS.
      cByCoind CIH. iFrame.
    - destruct c; s; cStepsS; case_match; try case_bool_decide; cStepsS; ss.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. cCall "".
        iIntros (ret ??) "->"; cStepsS; cStepsT.
        cByCoind CIH. iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_spawn).
        iIntros (tid); cStepsS; cStepsT; cByCoind CIH; iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_yield); iSplit; [eauto|].
        iIntros (??) "->"; cStepsS; cStepsT; cByCoind CIH; iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_gettid); eauto.
        iIntros (?); cStepsS; cStepsT; cByCoind CIH; iFrame.
    - destruct s; cStepsS; cStepsT; case_match; cStepsS; ss; cStepsT.
      { iApply wsim_sput_src; iApply wsim_sput_tgt; cNormS; cNormT; cByCoind CIH; iFrame. }
      { iApply wsim_sget_src; iApply wsim_sget_tgt; cNormS; cNormT; cByCoind CIH; iFrame. }
    - destruct e; cStepsS; cStepsT; case_match; cStepsS; ss; cStepsT.
      { cForcesS; cStepsS; cByCoind CIH; iFrame. }
      { cForcesT; cStepsT; cByCoind CIH; iFrame. }
      { cStep; cStepsS; cStepsT; cByCoind CIH; iFrame. }
  Qed.

  Lemma sim_filter_elim (mask : gset string) (m : Mod.t)
      (SUB : (set_omap (λ a, match a with fid fn => Some fn | _ => None end)
        (dom (m.(Mod.fnsems)))) ## mask) :
    ISim.t closed m (filter mask m) emp%I IstEq.
  Proof using.
    econs; ii; et.
    { rr. destruct x; et. exfalso. destruct H.
      exploit (wf_fns i None); [|intros []; ss].
      rewrite lookup_fmap H0. et.
    }
    rewrite /ISim.sim_fun ?lookup_fmap.
    destruct (_ !! _) as [[[msk bd]|]|] eqn : Ht; ss; cycle 1; last clear Ht.
    esplits; [refl|].
    iIntros (arg st_src st_tgt) "-> _".
    generalize false at 1 as ps. generalize false at 1 as pt. i.
    rewrite /SB.sandbox_body /=. generalize (bd arg) as itr. i. clear bd arg.
    cCoind CIH g0 __ with ps pt itr st_tgt msk. iIntros "_".

    assert (CASE:= case_itrH itr). des; subst; s.
    { cStep; eauto. }
    { cStepS; cStepsT. cByCoind CIH. done. }
    { cStepS.
      case_match; cStepS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cNormS; cNormT; cByCoind CIH. done.
    }
    { cStepS.
      case_match; cStepS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cNormS; cNormT; cByCoind CIH. done.
    }
    { cStepS.
      case_match; cStepS; ss.
      cStepsT; case_match; ss; cStepsT; cForceS; iFrame. cNormS; cNormT; cByCoind CIH. done.
    }
    { destruct c; s; cStepsS; case_match; try case_bool_decide; cStepsS; ss.
      { cStepsT; bsimpl; des; case_bool_decide; des; ss.
        { cStepsT. iApply isim_call. iSplit; first done.
          iIntros (ret ??) "->"; cStepsS; cStepsT. cByCoind CIH; iFrame; done.
        }
        { iApply isim_call_none; ss.
          rewrite ?lookup_fmap; destruct (_ !! _) eqn : Heq; ss.
          eapply elem_of_dom_2 in Heq.
          exfalso; eapply (SUB fn0).
          { rewrite elem_of_set_omap; esplits; eauto. }
          set_solver.
        }
      }
      { cStepsT; bsimpl; des; case_bool_decide; des; ss.
        { cStepsT.
          iApply isim_spawn; iIntros (tid). cNormS; cNormT. cByCoind CIH. done.
        }
        { iApply isim_spawn_none; ss.
          rewrite ?lookup_fmap; destruct (_ !! _) eqn : Heq; ss.
          eapply elem_of_dom_2 in Heq.
          exfalso; eapply (SUB fn0).
          { rewrite elem_of_set_omap; esplits; eauto. }
          set_solver.
        }
      }
      { cStepsT; bsimpl; des; case_match; des; ss. cStepsT.
        iApply isim_yield; iSplit; [done|]; iIntros (??) "->".
        cNormS; cNormT. cByCoind CIH. done.
      }
      { cStepsT; bsimpl; des; case_match; des; ss. cStepsT.
        iApply isim_gettid; iIntros (tid).
        cNormS; cNormT. cByCoind CIH. done.
      }
    }
    { destruct s; cStepsS; cStepsT; case_match; cStepsS; ss; cStepsT.
      { iApply isim_sput_src; iApply isim_sput_tgt; cNormS; cNormT; cByCoind CIH; by iFrame. }
      { iApply isim_sget_src; iApply isim_sget_tgt; cNormS; cNormT; cByCoind CIH; by iFrame. }
    }
    { destruct e; cStepsS; cStepsT; case_match; cStepsS; ss; cStepsT.
      { cForcesS; cStepsS; cByCoind CIH; by iFrame. }
      { cForcesT; cStepsT; cByCoind CIH; by iFrame. }
      { cStep; cStepsS; cStepsT; cByCoind CIH; by iFrame. }
    }
  Qed.

  (*** introduction of a module ***)
  Lemma intro_filter fns (m : Mod.t) P :
    ctx_refines (filter fns m, P)%I (m, P)%I.
  Proof using.
    rewrite -!(mod_addc_empty_r _ P).
    eapply ctxr_cond_frameL.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_filter (mask : gset string) (m : Mod.t) P
      (SUB : (set_omap (λ a, match a with fid fn => Some fn | _ => None end)
        (dom (m.(Mod.fnsems)))) ## mask) :
    refines (m, P)%I (filter mask m, P)%I.
  Proof using. eapply closed_adequacy_emp, sim_filter_elim. eauto. Qed.

  (*** introduction of a module ***)
  Theorem intro_module (mask : gset string) m mc P
      (WF: Mod.wf mc)
      (DISJ: (m.(Mod.scopes) ## mc.(Mod.scopes)))
      (EXCL: (set_omap (λ a, match a with fid fn => Some fn | _ => None end)
        (dom (m.(Mod.fnsems)))) ## mask)
      (EXCL2: (set_omap (λ a, match a with fid fn => Some fn | _ => None end)
        (dom (mc.(Mod.fnsems)))) ⊆ mask)
      (EXCL3: entry ∉ dom (Mod.fnsems mc))
      (* (SUB: ∀ fn, In (Some fn) (m.(Mod.fnsems).*1) → mask fn)
      (FRESH: ∀ fn, In (Some fn) (mc.(Mod.fnsems).*1) → (~ mask fn))
      (FRESHI: ~ In None (mc.(Mod.fnsems)).*1)
       *)
      :
    refines ((filter mask m) ★ mc, P)%I (filter mask m, P)%I.
  Proof using.
    ii; ss.
    assert (Hwfadd : Mod.wf (filter mask m ★ mc)).
    { apply Mod.add_wf; eauto.
      { intros [i|] Hi1 Hi2; last set_solver.
        apply (EXCL i).
        { apply elem_of_set_omap; exists (fid i); split; ss.
          rewrite /filter /= dom_fmap // in Hi1.
        }
        apply EXCL2.
        apply elem_of_set_omap; eexists; split; done.
      }
      inv WF; inv WFM; eapply NoDup_app; splits; eauto.
    }
    split; first done.

    (* Simulation proof *)
    intros rs Hrs temp; exists rs; splits; eauto. clear temp.
    cut (∀ ps pt arg,
         gsim eq ps pt (LMod.compile (Mod.to_lmod (filter mask m ★ mc) rs) arg)
           (LMod.compile (Mod.to_lmod (filter mask m) rs) arg)).
    { ii. eapply gsim_adequacy; et. }

    i. ginit. rewrite /LMod.compile. s.
    rewrite ?lookup_fmap ?lookup_omap ?lookup_union_with ?lookup_fmap.
    destruct (_ mc !! entry) eqn : Hmc; [eapply elem_of_dom_2 in Hmc; set_solver|ss; clear Hmc].
    destruct (_ m !! entry) as [[[msk bd]|]|] eqn : Hm; ss; [|gstep_l; ss|gstep_l; ss].

    rewrite /LModTr.trans /LModTr.interp_callE /ModTr.trans_fnsem /SB.sandbox_body /ITree.map. ired.
    guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }
    rewrite -(sandbox_sandbox (bd arg) _ (msk_filter mask (msk_scp (Mod.scopes m) msk_true))); cycle 1.
    { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
      { exfalso; naive_solver. }
      { exfalso; naive_solver. }
      { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ entry (msk, bd)).
        rewrite lookup_omap Hm /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
      }
      { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ entry (msk, bd)).
        rewrite lookup_omap Hm /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
      }
    }
    
    match goal with
      [|-context [ModTr.trans ?t]] => remember [ModTr.trans t] as ths
    end.
    (* destruct p as [[[img msk] sc] bd]. *)
    assert (WFTHS:
      ∀ tid t (IN: ths !! tid = Some t),
      ∃ ht, t = ModTr.trans (SB.sandbox (msk_filter mask (msk_scp (Mod.scopes m) msk_true)) ht)).
    { i. subst. destruct tid; ss. inv IN. esplits; eauto. }
    clear Heqths.
    generalize 0 as cid.
    (* rename rs into rs0.
    generalize rs0 at 2 4 as rs. *)
    assert (SCP := m.(Mod.well_scoped_init)). revert SCP.
    assert (Hsts : map_Forall (const is_Some) (Mod.initial_st m)).
    { apply Mod.nodup_init; inv WFM; auto. }
    revert Hsts.
    assert (SCPc := mc.(Mod.well_scoped_init)). revert SCPc.
    set (st := Mod.initial_st m).
    assert (Hsts : map_Forall (const is_Some) (union_with uwnd st (Mod.initial_st mc))).
    { subst st. hexploit (Mod.nodup_init (filter mask m ★ mc)); ss. inv Hwfadd; auto. }
    revert Hsts.
    generalize st.
    generalize (Mod.initial_st mc) as stc; clear st.
    (* generalize (eq_refl ths) as Heqths. *)
    (* generalize ths at 1 3 as ths0. *)
    generalize dependent ths.
    clear dependent arg bd msk.
    revert_until Hwfadd.
    gcofix CIH. i.
    (* ziter_l. ziter_r. *)
    destruct (ths !! cid) eqn: EQ; cycle 1.
    { giter_l. rewrite /= EQ /triggerUB. gstep_l. gstep_l. ss. }
    assert (WFLEN := lookup_lt_Some _ _ _ EQ).

    eapply WFTHS in EQ as ?. des. subst.
    rewrite /ModTr.trans in EQ.
    ides ht.
    {
      giter_l; giter_r; rewrite /= EQ /=.
      des_ifs; cycle 1.
      { unfold triggerUB. do 2 gstep_l. ss. }
      gstep_l. gcNormS. gstep_r. gcNormT. gstep. econs; econs; eauto.
    }
    {
      revert EQ; gnorm_itr; i.
      eapply gsim_tau_src; eauto.
      eapply gsim_tau_tgt; eauto.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }

    rewrite ?SBRed.vis in EQ. des_ifs; cycle 1.
    { bsimpl; des. revert EQ; gnorm_itr; intros EQ. eapply gsim_Take_src; [eapply EQ|ss]. }
    destruct e; [destruct a | destruct s;
                              [destruct c|destruct s; [destruct p|destruct c]]];
    rewrite vis_trigger in EQ.
    { (* Assume *)
      eapply gsim_Assume_src; [apply EQ|]. intros rs2 Hrs2.
      eapply gsim_Assume_tgt; [apply EQ|]. exists rs2; splits; try by des.
      zprogress. gbase. eapply (CIH rs2); try by des.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* AssumeRes *)
      eapply gsim_AssumeRes_src; [apply EQ|]. intros rs2.
      eapply gsim_AssumeRes_tgt; [apply EQ|]. splits; try by des.
      zprogress. gbase. eapply (CIH (r0 ⋅ rs)); try by des.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Guarantee *)
      eapply gsim_Guarantee_tgt; [apply EQ|]. intros rs2 Hrs2.
      eapply gsim_Guarantee_src; [apply EQ|]. exists rs2; splits; try by des.
      zprogress. gbase. eapply (CIH rs2); try by des.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Call *)
      bsimpl. simpl in Heq. case_bool_decide as Hfn; ss.
      eapply gsim_Call_src; [apply EQ|].
      eapply gsim_Call_tgt; [apply EQ|].
      rewrite {2 4}/LMod.prog !Mod.to_lmod_fnsems lookup_fnsems_None_r //; cycle 1.
      { rewrite -not_elem_of_dom; intros ?; apply Hfn, EXCL2.
        rewrite elem_of_set_omap; exists (fid fn); split; ss; auto.
      }
      rewrite /unwrapU; destruct (_ !! fid fn) as [[[cmsk cbd]|]|] eqn : Hfn'; cycle 1.
      { ired. giter_l. rewrite /= list_lookup_insert //=. gstep_l; ss. }
      { ired. giter_l. rewrite /= list_lookup_insert //=. gstep_l; ss. }
      ired.
      rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body -!interpV_bind /=.
      simpl; rewrite !lookup_fmap in Hfn'.
      destruct (_ !! fid fn) as [[[cmsk2 bd2]|]|] eqn : Hfn2; ss; clarify.

      zprogress. gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
      rewrite /ModTr.trans; esplits.
      f_equal; erewrite SBRed.bind, sandbox_sandbox.
      { f_equal. extensionalities a. rewrite -SBRed.tau //. }
      { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
        { exfalso; naive_solver. }
        { exfalso; naive_solver. }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (fid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
        }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (fid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
        }
      }
    }
    { (* Spawn *)
      bsimpl. simpl in Heq. case_bool_decide as Hfn; ss.
      eapply gsim_Spawn_src; [apply EQ|].
      eapply gsim_Spawn_tgt; [apply EQ|].
      rewrite {1 3}/LMod.prog !Mod.to_lmod_fnsems lookup_fnsems_None_r //; cycle 1.
      { rewrite -not_elem_of_dom; intros ?; apply Hfn, EXCL2.
        rewrite elem_of_set_omap; eexists (fid _); split; ss; auto.
      }
      rewrite /unwrapU; destruct (_ !! fid fn) as [[[cmsk cbd]|]|] eqn : Hfn'; cycle 1.
      { ired. gstep_l; ss. }
      { ired. gstep_l; ss. }
      ired.
      rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body /=.
      simpl; rewrite !lookup_fmap in Hfn'.
      destruct (_ !! fid fn) as [[[cmsk2 bd2]|]|] eqn : Hfn2; ss; clarify.

      zprogress. gbase. eapply CIH; et.
      i. eapply lookup_snoc_Some in IN. des.
      { eapply list_lookup_insert_Some in IN0. des; subst; et. }
      rewrite /ModTr.trans; esplits; subst.
      f_equal; erewrite <-sandbox_sandbox; try refl.
      { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
        { exfalso; naive_solver. }
        { exfalso; naive_solver. }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (fid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
        }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (fid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
        }
      }
    }
    { (* Yield *)
      eapply gsim_Yield_src; [apply EQ|].
      eapply gsim_Yield_tgt; [apply EQ|].
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* GetTid *)
      eapply gsim_GetTid_src; [apply EQ|].
      eapply gsim_GetTid_tgt; [apply EQ|].
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Put *)
      destruct k0 as [scp0 key0]; ss; case_bool_decide; ss.
      assert ((scp0, key0) ∉ (dom stc)).
      { intros Hscp0; eapply (DISJ scp0); auto.
        rewrite elem_of_subseteq in SCPc; specialize (SCPc scp0);
          rewrite elem_of_list_to_set in SCPc; eapply SCPc.
        rewrite elem_of_map; eexists (_, _); eauto.
      }
      eapply gsim_SPut_src; [apply EQ|auto|].
      rewrite insert_union_with_l; [|rewrite -not_elem_of_dom //].
      eapply gsim_SPut_tgt; [apply EQ|auto|].
      zprogress.
      gbase. eapply (CIH rs); et.
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
      { eapply map_Forall_union_with; cycle 1.
        { split.
          { eapply map_Forall_insert_2; ss. }
          { eapply map_Forall_union_with_inv in Hsts as ?; des; eauto. }
        }
        eapply map_Forall_union_with_inv_gen in Hsts as ?.
        set_solver.
      }
      { eapply map_Forall_insert_2; ss. }
      { set_solver. }
    }
    { (* Get *)
      destruct k0 as [scp0 key0]. ss; case_bool_decide; ss.
      assert ((scp0, key0) ∉ (dom stc)).
      { intros Hscp0; eapply (DISJ scp0); auto.
        rewrite elem_of_subseteq in SCPc; specialize (SCPc scp0);
          rewrite elem_of_list_to_set in SCPc; eapply SCPc.
        rewrite elem_of_map; eexists (_, _); eauto.
      }
      eapply gsim_SGet_src; [apply EQ|auto|]; s.
      eapply gsim_SGet_tgt; [apply EQ|auto|]; s.
      rewrite lookup_union_with (not_elem_of_dom_1 stc); eauto.
      zprogress. gbase.
      destruct (st !! _); ss; eapply (CIH rs); et.
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
    }
    { (* Choose *)
      eapply gsim_Choose_tgt; [apply EQ|]; intros x.
      eapply gsim_Choose_src; [apply EQ|]; exists x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Take *)
      eapply gsim_Take_src; [apply EQ|]; intros x.
      eapply gsim_Take_tgt; [apply EQ|]; exists x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* IO *)
      eapply gsim_IO; [apply EQ|apply EQ|]; intros x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
  Unshelve. all: exact smj_top.
  (*SLOW*)Qed.
End CFilter. End CFilter.

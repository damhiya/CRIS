Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import Mod ModSim ModTactics HMod ISim ISimInit.
Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
Require Import TacticsInit.
Require Import SimGlobal SimGlobalFacts.

Module CFilter. Section CFilter.
  Context `{Σ: GRA}.

  Program Definition filter mask (m: HMod.t) : HMod.t :=
    {|HMod.scopes := m.(HMod.scopes)
    ; HMod.fnsems := List.map (map_snd (map_fst (map_fst (mask_and mask)))) m.(HMod.fnsems)
    ; HMod.initial_st := m.(HMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(HMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. des_ifs; eauto.
  Qed.
  Next Obligation. ii. eapply (m.(HMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(HMod.nodup_fns)). eauto. Qed.

  (* Key theorems *)

  Lemma sim_filter_intro mask (m: HMod.t):
    HSim.t open (filter mask m) m emp%I IstEq.
  Proof.
    econs; s; et; try rewrite List.map_map fst_map_snd; try refl.
    ii. unfold filter in FIND. ss.
    rewrite alist_find_map_snd in FIND. unfold o_map in FIND.
    destruct (alist_find fn _); ss. inv FIND. destruct p as [[msk sc] bd].
    esplits; eauto.

    r. r. i. subst y. unfold HModTr.sandbox_body. s.
    generalize (bd x) as itr. clear bd x NODS NODD.
    combine_quant st_src; combine_quant st_tgt; combine_quant nths.
    eapply isim_coind.
    iIntros (g' [nths [st_tgt [st_src itr]]] MON) "[IST #CIH]".
    
    assert (CASE:= case_itrH itr). des; subst; s.
    - step; et.
    - steps_l. steps_r. by_coind "CIH"; et.
    - steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
    - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - destruct c; s.
      + destruct (mask_and mask msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.call EQ. steps_l. ss. }
        call "IST"; et.
        { unfold mask_and in EQ. destruct (msk fn0) eqn: EQ'; ss.
          destruct (mask fn0); ss. }
        steps_l. steps_r. by_coind "CIH"; et.
      + destruct (mask_and mask msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.spawn EQ. steps_l. ss. }
        spawn; et.
        { unfold mask_and in EQ. destruct (msk fn0) eqn: EQ'; ss.
          destruct (mask fn0); ss. }
        steps_l. steps_r. by_coind "CIH"; et.
      + yield "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
    - destruct s.
      + ired. rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_l. by_coind "CIH"; et.
        iPoseProof "IST" as "%"; subst. et.
      + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_l. steps_r. iPoseProof "IST" as "%"; subst.
        by_coind "CIH"; et.
    - destruct e.
      + steps_r. force_l q. steps_l. by_coind "CIH"; et.
      + steps_l. force_r q. steps_r. by_coind "CIH"; et.
      + step. steps_l. steps_r. by_coind "CIH"; et.
  Qed.
  
  Lemma sim_filter_elim (mask:_→bool) (m: HMod.t)
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
    :
    HSim.t closed m (filter mask m) emp%I IstEq.
  Proof.
    econs; s; et; try rewrite List.map_map fst_map_snd; try refl.
    ii. unfold filter. s.
    rewrite alist_find_map_snd. unfold o_map. rewrite FIND.
    destruct fs as [[msk sc] bd]. esplits; eauto.

    r. r. i. subst y. unfold HModTr.sandbox_body. s.
    generalize (bd x) as itr. clear x NODS NODD.
    combine_quant st_src; combine_quant st_tgt; combine_quant nths.
    eapply isim_coind.
    iIntros (g' [nths [st_tgt [st_src itr]]] MON) "[IST #CIH]".

    assert (CASE:= case_itrH itr). des; subst; s.
    - step; et.
    - steps_l. steps_r. by_coind "CIH"; et.
    - steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
    - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - destruct c; s.
      + destruct (msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.call EQ. steps_l. ss. }
        destruct (mask fn0) eqn: EQ'; cycle 1.
        { rewrite SBRed.bind. iApply isim_call_none_sandbox; et.
          rewrite alist_find_map_snd.
          destruct (alist_find fn0 _) eqn: FIND'; ss.
          eapply alist_find_some, in_map, SUB in FIND'.
          rewrite EQ' in FIND'. ss.
        }
        call "IST"; et.
        { unfold mask_and. rewrite EQ EQ'. et. }
        steps_l. steps_r. by_coind "CIH"; et.
      + destruct (msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.spawn EQ. steps_l. ss. }
        destruct (mask fn0) eqn: EQ'; cycle 1.
        { rewrite SBRed.bind. iApply isim_spawn_none_sandbox; et.
          rewrite alist_find_map_snd.
          destruct (alist_find fn0 _) eqn: FIND'; ss.
          eapply alist_find_some, in_map, SUB in FIND'.
          rewrite EQ' in FIND'. ss.
        }
        spawn; et.
        { unfold mask_and. rewrite EQ EQ'. et. }
        steps_l. steps_r. by_coind "CIH"; et.
      + yield "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
    - destruct s.
      + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_r. by_coind "CIH"; et.
        iPoseProof "IST" as "%"; subst. et.
      + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_r. iPoseProof "IST" as "%"; subst.
        by_coind "CIH"; et.
    - destruct e.
      + steps_r. force_l q. steps_l. by_coind "CIH"; et.
      + steps_l. force_r q. steps_r. by_coind "CIH"; et.
      + step. steps_l. steps_r. by_coind "CIH"; et.
  Qed.

  Corollary intro_filter fns (m: HMod.t):
    ctx_refines (filter fns m, emp)%I (m, emp)%I.
  Proof.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  Corollary elim_filter (mask:_→bool) (m: HMod.t)
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
    :
    refines (m, emp)%I (filter mask m, emp)%I.
  Proof.
    eapply closed_adequacy2, sim_filter_elim. eauto.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_module m mc:
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
      + destruct (sc.1 fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.call EQ. step_l. ss. }
        call "IST". steps_l. steps_r. by_coind "CIH"; et.
      + destruct (sc.1 fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.spawn EQ. step_l. ss. }
        spawn; et. steps_l. steps_r. by_coind "CIH"; et.
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

(*  
  Import ModTac.

  (*** introduction of a module ***)
  Lemma intro_module (mask:_→bool) m mc
    (WF: HMod.wf mc)
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
    (FRESH: ∀fn, In fn (List.map fst mc.(HMod.fnsems)) → (~ mask fn) ∧ (fn ≠ Mod.init_fun))
    (DISJ: List.NoDup (m.(HMod.scopes) ++ mc.(HMod.scopes)))
    :
    refines ((filter mask m) ★ mc, emp)%I (filter mask m, emp)%I .
  Proof.
    ii. split.
    { depdes WFM. econs; s.
      - rewrite List.map_app. eapply List.NoDup_app; et; try apply WF.
        ii. rewrite List.map_map fst_map_snd in H.
        eapply SUB in H. eapply FRESH in H0. des. ss.
      - eapply List.NoDup_app; eauto using NoDup_app_disjoint; try apply WF.
    }

    s. i. exists rs. esplits; eauto.
    cut (∀ ps pt,
         simg eq ps pt (Mod.compile (HMod.to_mod (filter mask m ★ mc) rs))
           (Mod.compile (HMod.to_mod (filter mask m) rs))).
    { ii. eapply adequacy_global; et. }

    i. unfold Mod.compile. rewrite {1}/Mod.prog {1}/unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. ired. pstep. econs. econs. ss. }
    assert (NONE: alist_find Mod.init_fun
                    (map (map_snd (HModTr.trans_ktree ∘ HModTr.sandbox_body))
                       (HMod.fnsems mc)) = None).
    { destruct (alist_find _ (_ (_ mc))) eqn:EQ; ss.
      eapply alist_find_some, (List.in_map fst) in EQ.
      ss. rewrite List.map_map fst_map_snd in EQ.
      eapply FRESH in EQ. des. ss.
    }
    unfold unwrapU.
    des_ifs; cycle 1;
      ss; unfold Mod.prog in Heq0; rewrite !map_app alist_find_app_o NONE in Heq.
    { exfalso. rewrite Heq0 in Heq. ss. }
    ired. ss.
    des_ifs. rewrite !alist_find_map in Heq1. unfold o_map in Heq1. des_ifs.
    destruct p0 as [[msk sc] bd].
    unfold HModTr.sandbox_body, HModTr.trans_ktree. s.

    clear NONE.
    generalize (bd ()↑) as it.
    assert (SCP := m.(HMod.well_scoped_init)). revert SCP.
    generalize (HMod.initial_st m) as st.
    assert (SCPc := mc.(HMod.well_scoped_init)). revert SCPc.
    generalize (HMod.initial_st mc) as stc.
    revert_until WFM. unfold ModTr.trans, ModTr.interp_callE, ModTr.interp_stateE.
    ginit. gcofix CIH. i.

    assert (CASE:=case_itrH it). des; subst.
    - rewrite !unfold_iter_eq. s. grind.
      rewrite !(bisim_is_eq (map_ret _ _)).
      steps.
    - rewrite !unfold_iter_eq. s. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      gbase; et. 
    -
      rewrite !unfold_iter_eq. s. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.
      
      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_bind _ _ _)).
      gstep. do 2 econs. i. do 2 econs. esplits.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.

      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_bind _ _ _)).
      gstep. do 2 econs. i. do 2 econs. esplits.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.

      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.

      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.
      
      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 8 econs.
      do 2 econs; eauto using smj_lt_mid_top.
      hss. grind. hss. grind.

      gbase. move CIH at bottom.
      

      
      rewrite !unfold_iter_eq. s. grind.
      try unfold ModTr.pure_state. grind.
      rewrite !(bisim_is_eq (map_bind _ _ _)).
      hss.


      
      gstep. do 2 econs. i. do 2 econs. esplits.
      do 2 econs; eauto using smj_lt_mid_top.

      do 2 econs.
      hss. grind.
      rewrite !(bisim_is_eq (map_tau _ _)).
      gstep. do 10 econs.
      hss. grind. hss. grind.
      


      rewrite (map_vis _ _ _).

      

      

      rewrite SBRed.bind SBRed.ag HRed.bind HRed.Assume.
      unfold HModTr.handle_Assume.
      
      

      !unfold_iter_eq. s. ired.
      


      HRed.tau !unfold_iter_eq. s. ired.

    eapply alist_find_some, (in_map fst) in Heq1.
    
  Qed.
*)
  
End CFilter. End CFilter.

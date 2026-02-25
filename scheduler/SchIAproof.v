Require Import CRIS.
Require Import SchHeader SchI SchA.
From iris.algebra Require Import gmap_view frac_auth.

Module SchIA. Section sim.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.
  Import SchA.

  Context (sp sp_user : specmap).
  Context (SchInSp : SchA.sp sp_user ⊤ ⊆ sp).
  Context (FunInSp : sp_user ⊆ sp).
  Context (ConcInSp : sp.2).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      (∃ ths tid_cur stid_cur,
        ⌜st_src =
          {[SchA.v_ths #
              ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t))
                <$> ths : list (nat * option SAny.t))↑;
            SchA.v_tid # tid_cur↑]} ∧
         st_tgt =
           {[SchI.v_ths #
              ((λ '(n, rv, _), (n, snd <$> rv : option SAny.t))
                <$> ths : list (nat * option SAny.t))↑;
              SchI.v_tid # tid_cur↑]} ∧
         ∃ ro_cur post_cur, ths !! tid_cur = Some (stid_cur, ro_cur, post_cur)⌝ ∗
        JoinAuth (list_to_map (imap (λ i RR, (i, to_agree RR)) ths.*2)) ∗
        TidAuth (list_to_map (imap pair ths.*1.*1)) ∗
        ([∗ list] i ↦ e ∈ ths,
          match e.1.2 with
          | None => True
          | Some (vrv, rv) =>
              JoinFrag (3/4) i e.2 ∗ interp_cond (e.2 vrv rv) ∨
              JoinFrag 1 i e.2
          end) ∗
        ([∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = tid_cur) then emp else YIELD e))%I.

  Local Definition SchAMod := SchA.t sp_user sp.
  Local Definition SchIMod := SchI.t.

  Lemma simF_inner_spawn : ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr._spawn).
  Proof using FunInSp SchInSp.
    iStartSim. rewrite /inner_spawn /SchI.inner_spawn.
    step_l. destruct _q.
    steps_l.
    iDestruct "ASM" as "[%stid [%pre [%postS [%fvarg [%varg [%fn [%mtid [[-> ->] ASM]]]]]]]]".
    iDestruct "ASM" as "[Spawn [W [TidFrag [Pre JoinFrag]]]]".

    steps_l. steps_r.
    iDestruct "Spawn" as "[%fsp [%Hfind Spawn]]". simpl_sp.
    iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
    { iPureIntro; exists (stid, mtid, tt); split; done. }
    iPoseProof ("Hspawn" with "[-IST JoinFrag]") as "> [Pre Post]".
    { unfold_pre_post; iFrame; eauto. }
    force_l (FSpec_mk _ _ Hfsp); eauto. forces_l. iFrame.

    steps_l. call "IST".
    clear st_src st_tgt; iIntros (ret st_src st_tgt) "IST".

    (* after call - prepare for termination *)
    steps_l. rename _q into vret.
    iMod ("Post" $! vret with "[ASM]") as "[W [[TidF [TID YIELD]] [% [% [[-> ->] Q]]]]]"; iFrame.
    steps_l.

    steps_r.
    iDestruct "IST" as "[% [%tid_cur [%stid_cur [[-> [-> %Hmtid]] [JoinA [TidA [RET Ys]]]]]]]".
    steps_r. steps_l.

    destruct Hmtid as [? [? Hmtid]].

    rewrite ?list_lookup_fmap Hmtid /=.
    steps_l. steps_r.

    iCombine "TidA TidF"
      gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    rewrite lookup_fmap_Some ?imap_fmap in Hav'; destruct Hav' as [? [? Hav']].
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
    destruct Hav' as [mtid2 [[[stid2 ?] ?] [EQ Hmtid2]]]; symmetry in EQ; inv EQ.
    apply to_agree_included in Hincl; symmetry in Hincl; inv Hincl; ss; clarify.

    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]".
      { erewrite ?list_lookup_fmap, Hmtid2; ss. }
      des_ifs; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%".
    }
    rewrite Hmtid2 in Hmtid; inv Hmtid. rename stid_cur into stid.

    iCombine "JoinA JoinFrag"
      gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
    destruct Hav' as [mtid3 [postS' [EQ Hmtid3]]]; symmetry in EQ; inv EQ.
    apply to_agree_included in Hincl; symmetry in Hincl.
    rewrite list_lookup_fmap Hmtid2 in Hmtid3; ss. clarify.

    (* IST construction *)
    iIst "IST" with "[JoinFrag JoinA TidA RET Ys Q]".
    { iExists (<[mtid := (stid, Some (svret, sret), _)]> ths), mtid, stid.
      iSplit.
      { rewrite ?list_fmap_insert /= list_lookup_insert //.
        { iPureIntro; esplits; eauto. }
        eapply lookup_lt_is_Some; rewrite Hmtid2 //.
      }
      eapply elem_of_list_split_length in Hmtid2 as [ths1 [ths2 [-> Hlen]]].
      iSplitL "JoinA".
      { rewrite Hlen; rewrite insert_app_r_alt; last done.
        rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
      }
      iSplitL "TidA".
      { rewrite Hlen; rewrite insert_app_r_alt; last done.
        rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
      }
      iSplitL "RET Q JoinFrag".
      { rewrite Hlen insert_app_r_alt; last done.
        iPoseProof (big_sepL_insert_acc _ _ mtid with "RET") as "[_ RET]"; ss.
        { rewrite Hlen lookup_app_Some; right; split; ss; rewrite Nat.sub_diag //=. }
        iPoseProof ("RET" $! (stid, Some (svret, sret), postS) with "[Q JoinFrag]") as "RET".
        { rewrite /JoinFrag Hlen /=; iLeft; iFrame. }
        rewrite Nat.sub_diag insert_app_r_alt Hlen // Nat.sub_diag //=.
        assert (postS' = postS); last subst postS'; auto.
        { extensionalities t1 t2; rewrite (Hincl t1 t2) //. }
      }
      rewrite Hlen insert_app_r_alt // Nat.sub_diag /=.
      rewrite ?fmap_app ?fmap_cons /=. iFrame.
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal SCH.
    set (st_src := {[_ := _; _ := _]}); set (st_tgt := {[_ := _; _ := _]}). clearbody st_src st_tgt.
    iApply wsim_reset.
    iStopProof. revert st_src.
    combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (? _ CIH [st_s st_t]) "[W [TidF [TID [YIELD IST]]]] /=".
    destruct_quant CIH.
    unfold_iterC_l. unfold_iterC_r.

    steps_l. simpl_sp.
    force_l (stid, mtid, tt). force_l (tt↑). steps_l.
    iApply wsim_guarantee_src; iFrame "W TidF TID YIELD"; iSplit; eauto.

    steps_r. call "IST".
    clear ret st_s st_t; iIntros (ret st_s st_t) "IST". steps_l.
    iDestruct "ASM" as "[TidF [-> ->]]".
    steps_r.
    by_coind CIH; eauto.
    iPoseProof (winv_split_empty with "I") as "[I E]".
    iFrame; iDestruct "TidF" as "[$ [$ $]]".
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.spawn).
  Proof using FunInSp SchInSp ConcInSp.
    iStartSim. rewrite /spawn /SchI.spawn.

    (* preprocess source precondition *)
    step_l. destruct _q as [user_pre user_post]. steps_l.
    iDestruct "ASM" as "[% [% [% [[-> ->] [Spawn ASM]]]]]".
    steps_l. steps_r.

    iDestruct "IST" as "[% [% [% [[-> [-> %Hmtid]] [JoinA [TidA [RET Y]]]]]]]".
    steps_l. steps_r. simpl_sp.
    rewrite ConcInSp.

    (* System spawn precondition *)
    force_l (). steps_l. force_l ((fn, farg)↑). steps_l.
    steps_r.
    iApply wsim_spawn. iIntros (tid_new). steps_r.
    steps_l. rewrite ?length_fmap /=. set (mtid_new := length ths).

    iMod (own_update with "JoinA") as "[JoinA JoinF]".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree user_post)); ss.
      { rewrite -not_elem_of_list_to_map fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; rewrite length_fmap in Hcont; lia.
      }
      refl.
    }
    iMod (own_update with "TidA") as "[TidA TidF]".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree tid_new)); ss.
      { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom.
        rewrite -not_elem_of_list_to_map ?imap_fmap fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; lia.
      }
      refl.
    }
    rewrite -{3}Qp.three_quarter_quarter -dfrac_op_own -{2}(agree_idemp (to_agree _)).
    iDestruct "JoinF" as "[JoinF1 JoinF2]".
    force_l. iSplitL "ASM JoinF1 TidF Spawn".
    { iIntros "???"; iFrame "JoinF1 Spawn TidF".
      iExists _, _; iFrame; iPureIntro; esplits; eauto.
    }
    steps_l. force_l (mtid_new↑). steps_l.
    force_l. iSplitL "JoinF2".
    { iExists _; iSplit; eauto. }
    step_l. step. iSplit; eauto.

    iExists (ths ++ [(tid_new, None, user_post)]), _, _; iSplitR.
    { des. iPureIntro. rewrite ?fmap_app /=. esplits; eauto. rewrite lookup_app Hmtid //. }
    iSplitL "JoinA".
    { rewrite -list_to_map_snoc.
      { rewrite fmap_app imap_app /= Nat.add_0_r length_fmap; subst mtid_new; done. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite length_fmap in Hin; lia.
    }
    iSplitL "TidA".
    { rewrite /TidAuth ?fmap_app /= imap_app /= ?length_fmap Nat.add_0_r list_to_map_snoc.
      { rewrite fmap_insert //. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite ?length_fmap in Hin; lia.
    }
    iSplitL "RET".
    { rewrite big_sepL_app /=; iFrame; done. }
    by rewrite ?fmap_app big_sepL_app /=; des_ifs; iFrame.
  (*SLOW*)Qed.

  Lemma simF_yield : ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.yield).
  Proof using FunInSp SchInSp ConcInSp.
    iStartSim. rewrite /yield /SchI.yield.

    step_l. destruct _q as [[stid mtid] ?]. steps_l.
    iDestruct "ASM" as "[[Tid [TID YIELD]] [-> ->]]".
    iDestruct "IST" as "[% [%tid_cur [%stid_cur [[-> [-> %Htid_cur]] [JoinA [TidA [RET Ys]]]]]]]".
    destruct Htid_cur as [ro_cur [post_cur Htid_cur]].
    steps_r. steps_l.
    rewrite ConcInSp.

    (* GetTid reasoning *)
    force_l stid; force_l; iFrame "TID". steps_l. steps_r.
    step. steps_l. steps_r. iDestruct "ASM" as "[-> TID]".
    iPoseProof (Tid_Auth_Tid with "[TidA Tid]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    destruct Hmtid as [? [? [EQ Hmtid]]]; symmetry in EQ; inv EQ.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%".
    }
    rewrite ?list_lookup_fmap Htid_cur in Hmtid; inv Hmtid.

    rewrite ?list_lookup_fmap Htid_cur /=; case_decide; subst; clarify.

    (* Choose the next tid *)
    steps_r. steps_l.
    destruct _q as [[tidn stidn] Htidn]. unshelve force_l (exist _ (tidn, stidn) _); last step_l.
    { ss. revert Htidn; rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss. }
    steps_l. steps_r.

    (* HoareYield *)
    rewrite ConcInSp. steps_l.
    rewrite ?list_lookup_fmap /= in Htidn.
    iAssert (YIELD stidn ∗
        [∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = tidn) then emp else YIELD e)%I
      with "[YIELD Ys]" as "[YIELD Ys]".
    { destruct (decide (mtid = tidn)).
      { subst; destruct (ths !! tidn) as [[[? ?] ?]|]; ss; clarify. iFrame. }
      iPoseProof (big_sepL_delete _ ths.*1.*1 mtid with "[Ys YIELD]") as "Ys"; eauto.
      { rewrite ?list_lookup_fmap Htid_cur //. }
      { ss. instantiate (1:=λ _ i, YIELD i). iFrame. }
      rewrite big_sepL_delete; try iFrame.
      rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss.
    }
    iApply wsim_unfold; iIntros "W".
    forces_l. iFrame "W TID YIELD". steps_l.
    iApply wsim_yield; iFrame. iSplit.
    { destruct (ths !! tidn) as [[[? ?] ?]|] eqn : ?; ss; clarify.
      iExists _; iPureIntro; esplits; eauto.
    }
    iIntros (st_sr st_tgt) "IST".

    steps_l. iDestruct "ASM" as "[TID [YIELD WINV]]".
    forces_l. iFrame. iSplit; eauto.
    step. iFrame. done.
  (*SLOW*)Qed.

  Lemma simF_join : ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.join).
  Proof using FunInSp SchInSp.
    iStartSim. rewrite /join /SchI.join.

    step_l. destruct _q as [[stid mtid] post]. steps_l.
    iDestruct "ASM" as "[TID [%tid [[-> ->] JoinF]]]".

    steps_r. steps_l.
    iApply wsim_reset. iStopProof.
    revert st_tgt.
    combine_quant st_src.
    eapply wsim_coind. intros g' _ CIH a.
    destruct a as [st_src st_tgt]. s.
    destruct_quant CIH.
    iIntros "[IST [Tid JoinF]]".

    unfold_iterC_l; unfold_iterC_r.

    iDestruct "IST" as "[% [%tid_cur [%stid_cur [[-> [-> %Hmtid]] [JoinA [TidA [RET Ys]]]]]]]".
    steps_l. steps_r.

    rewrite ?list_lookup_fmap.
    destruct (ths !! tid) as [[[stid_join [[rv vrv]|]] post2]|] eqn : Htid.
    { steps_l. steps_r.
      iPoseProof (big_sepL_lookup_acc _ _ tid with "RET") as "[J RET]"; eauto; ss.
      iDestruct "J" as "[[JoinF2 Post] | JoinF2]"; cycle 1.
      { iExFalso; iCombine "JoinF" "JoinF2" gives %[WF _]%gmap_view_frag_op_valid.
        rewrite dfrac_op_own // in WF.
      }
      iCombine "JoinF" "JoinF2" gives %[_ WF%to_agree_op_valid]%gmap_view_frag_op_valid.
      iCombine "JoinF" "JoinF2" as "JoinF"; rewrite Qp.quarter_three_quarter.
      iEval (rewrite WF agree_idemp) in "JoinF".
      iPoseProof ("RET" with "[JoinF]") as "RET"; first (iRight; iFrame).
      forces_l. iEval (rewrite -WF) in "Post". iFrame "Tid Post".
      iSplit; eauto.
      step. iSplit; eauto.
      iFrame. des; iExists _; iPureIntro; esplits; eauto.
    }
    { steps_r. steps_l. simpl_sp.
      force_l (stid, mtid, tt). steps_l. force_l. force_l. iFrame "Tid". iSplit; eauto.
      steps_l. call "JoinA TidA RET Ys".
      { iFrame. des; iExists _; iPureIntro; esplits; eauto. }
      iIntros (ret st_src st_tgt) "IST". steps_l. steps_r.
      iDestruct "ASM" as "[Tid [-> ->]]".
      steps_r. steps_l.
      by_coind CIH. iFrame.
    }
    { iExFalso; iCombine "JoinA" "JoinF" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
      destruct WF as [? [_ [_ [[? [? [EQ Hcont]]]%elem_of_list_to_map_2%elem_of_lookup_imap _]]]].
      inv EQ. rewrite list_lookup_fmap Htid // in Hcont.
    }
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.get_tid).
  Proof using FunInSp SchInSp.
    iStartSim. rewrite /get_tid /SchI.get_tid.

    step_l. destruct _q as [mtid stid].
    steps_l. iDestruct "ASM" as "[[-> ->] Tid]".
    iDestruct "IST" as "[% [%tid_cur [%stid_cur [[-> [-> %Hmtid]] [JoinA [TidA [RET Ys]]]]]]]".
    iDestruct "Tid" as "[TidF [TID YIELD]]".
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hin"; iFrame.
    apply elem_of_list_to_map_2 in Hin; rewrite elem_of_lookup_imap in Hin.
    destruct Hin as [? [? [EQ Hin]]]; symmetry in EQ; inv EQ.

    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%".
    }

    steps_l. steps_r. forces_l. iFrame. iSplit; eauto. step.

    iSplit; eauto.
    iFrame. des; iExists _; iPureIntro; esplits; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open SchAMod SchIMod SchA.init_cond Ist.
  Proof using FunInSp SchInSp ConcInSp.
    init_sim.
    { rewrite /init_cond.
      iIntros "[TidA JoinA]". iExists [(0, None, λ _ _, existT 0 emp%SAT)], 0, 0.
      iFrame. ss. iSplit; eauto. iSplit; eauto.
    }
    { eapply simF_inner_spawn. }
    { eapply simF_spawn. }
    { eapply simF_yield. }
    { eapply simF_join. }
    { eapply simF_get_tid. }
  Qed.
End sim.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS}.

  Lemma ctxr sp sp_user
        (SchInGlobal : SchA.sp sp_user ⊤ ⊆ sp)
        (UserInGlobal : sp_user ⊆ sp)
        (ConcInGlobal : sp.2) :
    ctx_refines
      (SchA.t sp_user sp, SchA.init_cond)
      (SchI.t,            emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr.
End SchIA.

Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import Mod ModSim SimGTactics HMod ISim ISimInit.
Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
Require Import TacticsInit Tactics.
Require Import HModSim SimGlobal SimGlobalFacts.

Module CFilter. Section CFilter.
  Context `{Σ: GRA}.

  Program Definition filter mask (m: HMod.t) : HMod.t :=
    {|HMod.scopes := m.(HMod.scopes)
    ; HMod.fnsems := List.map (map_snd (map_fst (map_fst (map_snd (wmask_and mask))))) m.(HMod.fnsems)
    ; HMod.initial_st := m.(HMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(HMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H.
    destruct (alist_find _ ); ss. destruct p as [[[img msk] scp] bd]. et.
  Qed.
  Next Obligation. ii. eapply (m.(HMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(HMod.nodup_init)). eauto. Qed.

  (* Lemmas *)

  Lemma filter_app m1 m2 msk:
    CFilter.filter msk (m1 ★ m2) = CFilter.filter msk m1 ★ CFilter.filter msk m2.
  Proof.
    destruct m1, m2. eapply hmod_extensionality; s; et.
    rewrite /map_fst /map_snd !List.map_app. et.
  Qed.

  (* Key theorems *)

  Lemma sim_filter_intro mask (m: HMod.t):
    HSim.t open (filter mask m) m emp%I IstEq.
  Proof using.
    assert (SIM: ∀ my_tid img msk scp ps pt nths st (itr: itree hmodE Any.t),
    ⊢ isim open
      (map (map_snd SB.sandbox_body) (HMod.fnsems (filter mask m)))
      (map (map_snd SB.sandbox_body) (HMod.fnsems m)) IstEq my_tid ibot ibot
      (ist_with_eq IstEq) ps pt nths
      (st, SB.sandbox img (wmask_and mask msk) scp itr)
      (st, SB.sandbox img msk scp itr)).
    {
      i. revert itr. combine_quant st; combine_quant nths.
      combine_quant ps. combine_quant pt. combine_quant img.
      combine_quant scp. combine_quant msk.
      eapply isim_coind. i.
      destruct a as [msk [scp [img [pt [ps [nths [st itr]]]]]]]. s. destruct_quant.
      iIntros "[_ #CIH]".
      assert (CASE:= case_itrH itr). des; subst; s.
      - step; et.
      - steps_l. steps_r. by_coind "CIH"; et.
      - destruct img.
        + steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
        + rewrite SBRed.bind SBRed.Assume. steps_l. ss.
      - steps_l. steps_r. step. steps_l. steps_r. by_coind "CIH"; et.
      - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
      - destruct c; s.
        + destruct (wmask_and mask msk fn) eqn: EQ; cycle 1.
          { rewrite SBRed.bind SBRed.call EQ. steps_l. ss. }
          call ""; et.
          { unfold wmask_and in EQ. destruct (msk fn) eqn: EQ'; ss.
            destruct (mask fn); ss. }
          iDestruct "IST" as "%". subst.
          steps_l. steps_r. by_coind "CIH"; et.
        + destruct (wmask_and mask msk fn) eqn: EQ; cycle 1.
          { rewrite SBRed.bind SBRed.spawn EQ. steps_l. ss. }
          spawn; et.
          { unfold wmask_and in EQ. destruct (msk fn) eqn: EQ'; ss.
            destruct (mask fn); ss. }
          steps_l. steps_r. by_coind "CIH"; et.
        + yield ""; et. iDestruct "IST" as "%". subst.
          steps_l. steps_r. by_coind "CIH"; et.
      - destruct s.
        + ired. rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
          { steps_l. ss. }
          iApply isim_sput_src. iApply isim_sput_tgt.
          steps_l. by_coind "CIH"; et.
        + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
          { steps_l. ss. }
          iApply isim_sget_src. iApply isim_sget_tgt.
          by_coind "CIH"; et.
      - destruct e.
        + steps_r. force_l q. steps_l. by_coind "CIH"; et.
        + destruct img; s.
          { steps_l. force_r q. steps_r. by_coind "CIH"; et. }
          rewrite !SBRed.bind !SBRed.take; s. des_ifs.
          * steps_l. force_r q. by_coind "CIH"; et.
          * steps_l. ss.
        + step. steps_l. steps_r. by_coind "CIH"; et.
    }

    econs; ss; ii; et; try rewrite List.map_map fst_map_snd; try refl.
    { rewrite !alist_find_map_snd in H0 |- *.
      destruct (alist_find _ _); ss. split; et.
    }

    ss. rewrite !alist_find_map_snd in FIND.
    destruct (alist_find fn _) eqn: E; ss. inv FIND. esplits; et.
    destruct p as [[[img msk] scp] bd].
    ii. rewrite {3 4}/SB.sandbox_body. s.
    iIntros "H". iAssert (⌜st_src = st_tgt⌝%I) as "%"; subst.
    { destruct fn; et. iDestruct "H" as "%". des; subst. et. }
    iApply isim_mono; cycle 1.
    + iApply SIM; et.
    + i. iIntros "%". des; subst. iSplit; et. destruct fn; et.
  (*SLOW*)Qed.
  
  Lemma sim_filter_elim (mask:_→bool) (m: HMod.t)
    (SUB: ∀fn, In (Some fn) (List.map fst m.(HMod.fnsems)) → mask fn)
    :
    HSim.t closed m (filter mask m) emp%I IstEq.
  Proof using.
    assert (SIM: ∀ my_tid img msk scp ps pt nths st (itr: itree hmodE Any.t),
    ⊢ isim closed
      (map (map_snd SB.sandbox_body) (HMod.fnsems m))
      (map (map_snd SB.sandbox_body) (HMod.fnsems (filter mask m)))
      IstEq my_tid ibot ibot
      (ist_with_eq IstEq) ps pt nths
      (st, SB.sandbox img msk scp itr)
      (st, SB.sandbox img (wmask_and mask msk) scp itr)).
    {
    i. revert itr.
    combine_quant st. combine_quant nths. combine_quant ps. combine_quant pt.
    eapply isim_coind.
    iIntros (g' [pt [ps [nths [st itr]]]] MON) "[_ #CIH]". s. destruct_quant.
    assert (CASE:= case_itrH itr). des; subst; s.
    - step; et.
    - steps_l. steps_r. by_coind "CIH"; et.
    - destruct img.
      + steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
      + rewrite SBRed.bind SBRed.Assume. steps_l. ss.
    - steps_l. steps_r. step. steps_l. steps_r. by_coind "CIH"; et.
    - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - destruct c; s.
      + destruct (msk fn) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.call EQ. steps_l. ss. }
        destruct (mask fn) eqn: EQ'; cycle 1.
        { rewrite SBRed.bind. iApply isim_call_none_sandbox; et.
          rewrite alist_find_map_snd.
          destruct (alist_find (Some fn) _) eqn: FIND'; ss.
          eapply alist_find_some, (in_map fst), SUB in FIND'.
          rewrite EQ' in FIND'. ss.
        }
        call ""; et.
        { unfold wmask_and. rewrite EQ EQ'. et. }
        iDestruct "IST" as "%". subst.
        steps_l. steps_r. by_coind "CIH"; et.
      + destruct (msk fn) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.spawn EQ. steps_l. ss. }
        destruct (mask fn) eqn: EQ'; cycle 1.
        { rewrite SBRed.bind. iApply isim_spawn_none_sandbox; et.
          rewrite alist_find_map_snd.
          destruct (alist_find (Some fn) _) eqn: FIND'; ss.
          eapply alist_find_some, (in_map fst), SUB in FIND'.
          rewrite EQ' in FIND'. ss.
        }
        spawn; et.
        { unfold wmask_and. rewrite EQ EQ'. et. }
        steps_l. steps_r. by_coind "CIH"; et.
      + yield ""; et. iDestruct "IST" as "%". subst.
        steps_l. steps_r. by_coind "CIH"; et.
    - destruct s.
      + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_r. by_coind "CIH"; et.
      + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_r. by_coind "CIH"; et.
    - destruct e.
      + steps_r. force_l q. steps_l. by_coind "CIH"; et.
      + destruct img.
        * steps_l. force_r q. steps_r. by_coind "CIH"; et.
        * rewrite !SBRed.bind !SBRed.take. des_ifs.
          { steps_l. force_r q. steps_r. by_coind "CIH"; et. }
          steps_l. ss.
      + step. steps_l. steps_r. by_coind "CIH"; et.
    }

    econs; ii ; et.
    { exists []. s. refl. }
    { exists []. s. rewrite List.map_map fst_map_snd; try refl. }
    { rewrite !alist_find_map_snd in H0 |- *.
      destruct (alist_find _ _) eqn: E; ss. split; et. }

    s. rewrite !alist_find_map_snd FIND. esplits; et.
    ii. iIntros "H". destruct fs as [[[img msk] scp] bd].
    rewrite {3 4}/SB.sandbox_body. s.
    iAssert (⌜st_src = st_tgt⌝%I) as "%"; subst.
    { destruct fn; et. iDestruct "H" as "%". des; subst. et. }
    iApply isim_mono; cycle 1.
    - iApply SIM.
    - i. iIntros "%". des; subst. iSplit; et. destruct fn; et.
  (*SLOW*)Qed.

  (*** introduction of a module ***)
  Theorem intro_filter fns (m: HMod.t) P:
    ctx_refines (filter fns m, P)%I (m, P)%I.
  Proof.
    rewrite -!(hmod_addc_empty_r _ P).
    eapply ctxr_cond_frameL.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  (*** elimination of a module ***)
  Theorem elim_filter (mask:_→bool) (m: HMod.t) P
    (SUB: ∀fn, In (Some fn) (List.map fst m.(HMod.fnsems)) → mask fn)
    :
    refines (m, P)%I (filter mask m, P)%I.
  Proof.
    eapply closed_adequacy2, sim_filter_elim. eauto.
  Qed.

  (*** elimination of a module ***)
  Theorem elim_module mc P:
    ctx_refines (⌽, P) (mc, P).
  Proof using.
    do 2 rewrite -(hmod_addc_empty_l _ P).
    eapply ctxr_cond_frameR.
    eapply main_adequacy with (Ist := fun _ _ _ => emp%I).
    init_sim; ii; et.
  (*SLOW*)Qed.

  (*** introduction of a module ***)
  Theorem intro_module (mask:_→bool) m mc P
    (WF: HMod.wf mc)
    (SUB: ∀fn, In (Some fn) (List.map fst m.(HMod.fnsems)) → mask fn)
    (FRESH: ∀fn, In (Some fn) (List.map fst mc.(HMod.fnsems)) → (~ mask fn))
    (FRESHI: ~ In None (List.map fst mc.(HMod.fnsems)))
    (DISJ: List.NoDup (m.(HMod.scopes) ++ mc.(HMod.scopes)))
    :
    refines ((filter mask m) ★ mc, P)%I (filter mask m, P)%I .
  Proof using.
    ii. ss.
    split.
    { depdes WFM. econs; s.
      - rewrite List.map_app. eapply List.NoDup_app; et; try apply WF.
        ii. rewrite List.map_map fst_map_snd in H. destruct a.
        + eapply FRESH; et.
        + eapply FRESHI; et.
      - eapply List.NoDup_app; eauto using NoDup_app_disjoint; try apply WF.
    }

    s. i. exists rs. esplits; eauto.
    cut (∀ ps pt arg,
         simg eq ps pt (Mod.compile (HMod.to_mod (filter mask m ★ mc) rs) arg)
           (Mod.compile (HMod.to_mod (filter mask m) rs) arg)).
    { ii. eapply adequacy_global; et. }

    i. ginit. rewrite /Mod.compile. s.
    rewrite !map_app alist_find_app_o !alist_find_map_snd.
    destruct (alist_find _ _) eqn: E; cycle 1.
    { s. destruct (alist_find _ (_ mc)) eqn: E0.
      { exfalso. eapply alist_find_some, (in_map fst) in E0. et. }
      s. zstep_l.
    }

    s. ired.
    rewrite /ModTr.trans /ModTr.interp_callE /HModTr.trans_ktree /SB.sandbox_body.
    erewrite <-(bind_ret_r (ITree.map snd _)), (bisim_is_eq (bind_map _ _ _)).
    erewrite <-(bind_ret_r (ITree.map snd _)), (bisim_is_eq (bind_map _ _ _)).
    
    match goal with
      [|-context [HModTr.trans ?t]] => remember [HModTr.trans t] as ths
    end.
    destruct p as [[[img msk] sc] bd].
    assert(WFTHS:
      ∀ tid t (IN: ths !! tid = Some t),
      ∃ ht, t = HModTr.trans (SB.sandbox true mask m.(HMod.scopes) ht)).
    { i. subst. destruct tid; ss. inv IN.
      esplits. erewrite sandbox_sandbox; et; try refl.
      - ii. eapply andb_prop in H. des. et.
      - etrans; [|eapply HMod.well_scoped_fns; et].
        rewrite /fnsems_scopes. instantiate (1:= None). rewrite E. refl.
    }
    clear Heqths.
    generalize 0 as cid.
    rename rs into rs0.
    generalize rs0 at 2 4 as rs.
    assert (SCP := m.(HMod.well_scoped_init)). revert SCP.
    generalize (HMod.initial_st m) as st.
    assert (SCPc := mc.(HMod.well_scoped_init)). revert SCPc.
    generalize (HMod.initial_st mc) as stc.
    generalize (eq_refl ths) as Heqths.
    generalize ths at 1 3 as ths0.
    revert_until SRC.
    gcofix CIH. i. subst.

    ziter_l. ziter_r.
    destruct (ths !! cid) eqn: EQ; cycle 1.
    { unfold triggerUB. do 2 zstep_l. }
    assert (WFLEN := lookup_lt_Some _ _ _ EQ).

    eapply WFTHS in EQ. des. subst.
    ides ht.
    {
      des_ifs; cycle 1.
      { unfold triggerUB. do 2 zstep_l. }
      zstep_l. zstep_r. zstep.
    }
    {
      zstep_l. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }

    destruct e; [destruct a | destruct s;
                              [destruct c|destruct s; [destruct p|destruct c]]].
    { (* Assume *)
      rewrite SBRed.vis_Assume.
      zstep_l.
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
    { (* AssumePrecise  *)
      zstep_r.
      ziter_r. zstep_r. zstep_r.
      ziter_r. zstep_r. zstep_r. 
      ziter_r. zstep_r. zstep_r.

      zstep_l.
      ziter_l. zstep_l. exists x. zstep_l.
      ziter_l. zstep_l. exists x0. zstep_l.
      ziter_l. zstep_l. exists x1. zstep_l.

      ziter_l. zstep_l. zstep_l.
      ziter_l. zstep_l.
      ziter_l. zstep_l.
      
      ziter_r. zstep_r. exists x2. zstep_r.
      ziter_r. zstep_r.
      ziter_r. zstep_r.

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

      esplits. rewrite /SB.sandbox_body /HModTr.trans_ktree.
      erewrite SBRed.bind, HRed.bind, sandbox_sandbox; s.
      - f_equal. extensionalities.
        erewrite SBRed.tau, HRed.tau.
        do 2 f_equal. ired. erewrite sandbox_sandbox; ii; et; try refl.
      - et.
      - ii. eapply andb_prop in H. des; et.
      - s. etrans; [|eapply HMod.well_scoped_fns].
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
      esplits. unfold SB.sandbox_body, HModTr.trans_ktree. s.
      erewrite <-sandbox_sandbox; try refl.
      - ii. apply andb_prop in H. des; et.
      - etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. instantiate (1:=Some fn). rewrite Heq0. refl.
    }
    { (* Yield *)
      zstep_l. zstep_r.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Put *)
      destruct k0 as [key var]. s.
      destruct (existsb (String.eqb key) (HMod.scopes m)) eqn: Heq; cycle 1.
      { zstep_l. }
      zstep_l. zstep_r.
      ziter_l. zstep_l.
      ziter_r. zstep_r.
      rewrite !HModTr.alist_encode_decode.
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
      destruct (existsb (String.eqb key) (HMod.scopes m)) eqn: Heq; cycle 1.
      { zstep_l. }
      zstep_l. zstep_r. s. ired.   
      rewrite !HModTr.alist_encode_decode.
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
  (*SLOW*)Qed.

End CFilter. End CFilter.

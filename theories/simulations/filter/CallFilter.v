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
    ; HMod.fnsems := List.map (map_snd (map_fst (map_fst (wmask_and mask)))) m.(HMod.fnsems)
    ; HMod.initial_st := m.(HMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(HMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. des_ifs; eauto.
  Qed.
  Next Obligation. ii. eapply (m.(HMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(HMod.nodup_fns)). eauto. Qed.

  (* Lemmas *)

  Lemma filter_app m1 m2 msk:
    CFilter.filter msk (m1 ★ m2) = CFilter.filter msk m1 ★ CFilter.filter msk m2.
  Proof.
    destruct m1, m2. eapply hmod_extensionality; s; et.
    unfold map_fst, map_snd.
    rewrite !List.map_app. et.
  Qed.

  (* Key theorems *)

  Lemma sim_filter_intro mask (m: HMod.t):
    HSim.t open (filter mask m) m emp%I IstEq.
  Proof using.
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
    - steps_l. steps_r. step. steps_l. steps_r. by_coind "CIH"; et.
    - steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - destruct c; s.
      + destruct (wmask_and mask msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.call EQ. steps_l. ss. }
        call "IST"; et.
        { unfold wmask_and in EQ. destruct (msk fn0) eqn: EQ'; ss.
          destruct (mask fn0); ss. }
        steps_l. steps_r. by_coind "CIH"; et.
      + destruct (wmask_and mask msk fn0) eqn: EQ; cycle 1.
        { rewrite SBRed.bind SBRed.spawn EQ. steps_l. ss. }
        spawn; et.
        { unfold wmask_and in EQ. destruct (msk fn0) eqn: EQ'; ss.
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
  (*SLOW*)Qed.
  
  Lemma sim_filter_elim (mask:_→bool) (m: HMod.t)
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
    :
    HSim.t closed m (filter mask m) emp%I IstEq.
  Proof using.
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
    - steps_l. steps_r. step. steps_l. steps_r. by_coind "CIH"; et.
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
        { unfold wmask_and. rewrite EQ EQ'. et. }
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
        { unfold wmask_and. rewrite EQ EQ'. et. }
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
  (*SLOW*)Qed.

  Theorem intro_filter fns (m: HMod.t) P:
    ctx_refines (filter fns m, P)%I (m, P)%I.
  Proof.
    rewrite -!(hmod_addc_empty_r _ P).
    eapply ctxr_cond_frameL.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  Theorem elim_filter (mask:_→bool) (m: HMod.t) P
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
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
    init_sim; et.
  (*SLOW*)Qed.

  (*** introduction of a module ***)
  Theorem intro_module (mask:_→bool) m mc P
    (WF: HMod.wf mc)
    (SUB: ∀fn, In fn (List.map fst m.(HMod.fnsems)) → mask fn)
    (FRESH: ∀fn, In fn (List.map fst mc.(HMod.fnsems)) → (~ mask fn) ∧ (fn ≠ Mod.init_fun))
    (DISJ: List.NoDup (m.(HMod.scopes) ++ mc.(HMod.scopes)))
    :
    refines ((filter mask m) ★ mc, P)%I (filter mask m, P)%I .
  Proof using.
    ii. hdes.
    split.
    { depdes WFM. econs; s.
      - rewrite List.map_app. eapply List.NoDup_app; et; try apply WF.
        ii. rewrite List.map_map fst_map_snd in H.
        eapply SUB in H. eapply FRESH0 in H0. des. ss.
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
      eapply FRESH1 in EQ. des. ss.
    }
    unfold unwrapU.
    des_ifs; cycle 1;
      ss; unfold Mod.prog in Heq0; rewrite !map_app alist_find_app_o NONE in Heq.
    { exfalso. rewrite Heq0 in Heq. ss. }
    ired. ss.
    des_ifs. rewrite !alist_find_map in Heq1. unfold o_map in Heq1. des_ifs.
    unfold HModTr.sandbox_body, HModTr.trans_ktree. s.
    unfold ModTr.trans, ModTr.interp_callE, ITree.map.

    move NONE at top.

    match goal with
      [|-context [HModTr.trans ?t]] => remember [HModTr.trans t] as ths
    end.
    assert(WFTHS:
      ∀ tid t (IN: ths !! tid = Some t),
      ∃ ht, t = HModTr.trans (HModTr.sandbox mask m.(HMod.scopes) ht)).
    { i. subst. destruct tid; ss. inv IN. destruct p0 as [[] ?]. ss.
      esplits. erewrite sandbox_sandbox; et; try refl.
      - etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. erewrite Heq0. refl.
      - ii. eapply andb_prop in H. des. et. }
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
    ginit. gcofix CIH. i. subst.

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
      { exfalso. rewrite !List.map_app alist_find_app_o Heq1 in Heq.
        eapply alist_find_some, (in_map fst) in Heq.
        rewrite List.map_map fst_map_snd in Heq. ss.
        eapply FRESH0; et.
      }
      zstep_l. zstep_r.

      rewrite !List.map_app alist_find_app_o Heq1 in Heq. depdes Heq.

      zprogress.
      gbase. eapply CIH; et.

      i. eapply list_lookup_insert_Some in IN. des; subst; et.

      rewrite alist_find_map_snd /o_map in Heq1. des_ifs.
      rewrite alist_find_map_snd /o_map in Heq. des_ifs.
      destruct p1 as [[msk1 sc1] bd1]. s.

      esplits.
      erewrite SBRed.bind, HRed.bind, sandbox_sandbox.
      f_equal. extensionalities.
      erewrite SBRed.tau, HRed.tau.
      do 2 f_equal. ired. erewrite sandbox_sandbox. refl.
      - refl.
      - ii. et.
      - s. etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. erewrite Heq1. refl.
      - s. ii. eapply andb_prop in H. des; et.
    }
    { (* Spawn *)
      s. destruct (mask fn) eqn: Hmask; cycle 1.
      { zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { unfold triggerUB. do 2 zstep_l. }
      s. unfold unwrapU at 1. des_ifs; cycle 1.
      { exfalso. rewrite !List.map_app alist_find_app_o Heq1 in Heq.
        eapply alist_find_some, (in_map fst) in Heq.
        rewrite List.map_map fst_map_snd in Heq. ss.
        eapply FRESH0; et.
      }
      zstep_l. zstep_r.

      rewrite !List.map_app alist_find_app_o Heq1 in Heq. depdes Heq.

      zprogress.
      gbase. eapply CIH; et.

      i. eapply lookup_snoc_Some in IN. des.
      { eapply list_lookup_insert_Some in IN0. des; subst; et. }
      
      subst. rewrite !alist_find_map /o_map in Heq1. des_ifs.
      destruct p1 as [[msk1 sc1] bd1]. s.
      esplits. unfold HModTr.sandbox_body, HModTr.trans_ktree. s.
      erewrite <-sandbox_sandbox. refl.
      - etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. erewrite Heq1. refl.
      - ii. apply andb_prop in H. des; et.
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
      { eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq1; subst.
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
      { eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq1; subst.
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

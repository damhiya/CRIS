Require Import Common.

Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import ITactics SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import SModCancel HModInline ElimRel StRed.
Require Import CancelLib CancelCall CancelCallRev.
Require Import CancelHead CancelTail CancelSpawn CancelYield.

Set Implicit Arguments.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable md: SMod.t.

  Import CancelTAC.
  
  Lemma cancel_aux rs0 rt0
    ginv sk (SKINCL: incl (SMod.sk md) sk) (SKWF: Sk.wf sk)
    rs rt srcs tgts cid st ps pt
    (WF: ✓ rs)       
    (LEN: cid < List.length srcs)
    (REL: Forall2i (thread_rel md ginv sk cid) 0 srcs tgts)
    (UPD: Own rs ==∗ Own rt)
    :
    CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 bot7) ginv sk rs0 rt0 ps pt srcs tgts cid st rs rt.
  Proof.
    exploit Forall2i_nth; eauto. i. des.
    rename x into src, y into tgt.
    depdes x2.
    hexploit REL. i. eapply Forall2i_len in H. des.
    assert (cid < List.length tgts). { rewrite <- H. eauto. }
    assert (RELS: forall k x y (NEQ: cid ≠ k)
                    (LKX: srcs !! k = Some x)
                    (LKY: tgts !! k = Some y),
                      thread_rel md ginv sk cid k x y). 
    { i. eapply Forall2i_forall in REL; eauto. }
    clear REL. rename REL0 into REL. unfold elim_rel in REL.
    simpl plus in *. subst.
    destruct (Nat.eq_dec cid cid); ss. clear e.
    rename x0 into SRC, x1 into TGT.
    rewrite interp_hp_bind interp_hp_ret in TGT.
    revert_until SKWF. gcofix CIH. i.
    
    assert (✓ rt). { eapply Own_wand_valid with (a1:=rs); eauto. }
    punfold REL. depdes REL; subst.
    - _iter. _iter. rewrite SRC TGT. ired.
      hide_l. _coreA.
    - _iter. _iter. rewrite SRC TGT. ired.
      hide_r. des_ifs; cycle 1.
      { unfold triggerUB. ired. _coreA. }
      ired. reveal ITREE.
      _coreA. iterT 2.
      iterL. _supd. iterL. _coreA. ls.
      iterL. _coreA. ls. iterL. _supd. iterL. _supd.
      iterT 2. iterL. rewrite !StRed.ret. ired. st.
      hexploit Own_bupd_split; eauto. i. des.
      specialize (RET v x eq_refl).
      eapply Own_pure_soundness with (x := a1).
      + eapply Own_bupd_valid in H; eauto.
        eapply cmra_valid_op_l; eauto.
      + etrans; eauto.
    - _iter. _iter. rewrite SRC TGT. ired. tau 4.
      done_by_CIH CIH LKX LKY.
    - _iter. _iter. rewrite SRC TGT. ired.
      depdes e.
      + hide_l. _coreA. iterT 1. reveal ITREE.
        hide_r. _coreE x. iterT 1. reveal ITREE.
        done_by_CIH CIH LKX LKY.
      + hide_r. _coreA. iterT 1. reveal ITREE.
        hide_l. _coreE x. iterT 1. reveal ITREE.
        done_by_CIH CIH LKX LKY.
      + hide_l. _core. reveal ITREE.
        hide_r. _core. reveal ITREE.
        st. instantiate (1:= smj_top). i. subst.
        hide_l. st. ired. tau 1. iterT 1. reveal ITREE.
        hide_r. st. ired. tau 1. iterT 1. reveal ITREE.
        done_by_CIH CIH LKX LKY.
    - _iter. _iter. rewrite SRC TGT. ired.
      depdes e.
      + hide_l. grind. _supd. iterL. _supd. iterT 1. reveal ITREE.
        hide_r. grind. _supd. iterL. _supd. iterT 1. reveal ITREE.
        done_by_CIH CIH LKX LKY.
      + hide_l. grind. _supd. iterT 1. reveal ITREE.
        hide_r. grind. _supd. iterT 1. reveal ITREE.
        done_by_CIH CIH LKX LKY.
    - _iter. _iter. rewrite SRC TGT. ired.
      hide_r. _coreA. iterL. _supd. iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd. iterT 1. reveal ITREE.
      hide_l. _coreE x.
      assert (UPD': Own(x ⋅ rs) ==∗ Own (x ⋅ rt)).
      { iIntros "[H0 H1]". iSplitL "H0"; eauto.
        iApply UPD; eauto.
      }
      assert (VALID: ✓ (x ⋅ rt)). 
      { 
        hexploit Own_bupd_valid; eauto.
        iIntros "H". iPoseProof (UPD' with "H") as ">[H0 H1]".
        iModIntro. iFrame.
      }
      iterL. _supd. iterL. _coreE VALID. ls.
      iterL. _coreE x1. ls. 
      iterL. _supd. iterL. _supd.
      iterT 1. reveal ITREE.
      done_by_CIH CIH LKX LKY.
    - _iter. _iter. rewrite SRC TGT. ired.
      hide_l. _supd. iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd. iterT 1. reveal ITREE.
      hide_r. _supd.
      assert (SAT: Own rs ==∗ P ∗ Own x).
      {
        iIntros "H". iPoseProof (UPD with "H") as ">H". 
        iApply x0; eauto.
      }
      iterL. _coreE x. iterL. _coreE SAT.
      iterL. _supd. iterL. _supd. iterT 1. reveal ITREE.
      assert (VALID: ✓ x).
      { 
        hexploit Own_bupd_split; eauto. i. des.
        eapply Own_bupd_valid in H2; eauto.
        eapply Own_pure_soundness with (x:=a2).
        { eapply cmra_valid_op_r, Own_wand_valid; eauto. }
        iIntros "H". iApply Own_valid. iStopProof. eauto.
      }
      done_by_CIH CIH LKX LKY.
    - _iter. _iter. rewrite SRC TGT. ired.
      hide_l. tau 1. iterT 1. reveal ITREE.
      hide_r. tau 1. iterT 1. reveal ITREE.
      done_by_CIH CIH LKX LKY.
    - eapply cancel_aux_head; eauto. i; eapply CIH; eauto.
    - eapply cancel_aux_tail; eauto. i; eapply CIH; eauto.
    - eapply cancel_aux_spawn; eauto. i; eapply CIH; eauto.
    - eapply cancel_aux_yield; eauto. i; eapply CIH; eauto.
  Qed.

  Lemma cancel_main
      P ginv sk fsp meta rs rt r
      (EQV: Sk.equiv (SMod.sk md) sk) (SKWF: Sk.wf sk)
      (WF: HModSem.wf ((SModCancel.to_hmod md).(HMod.modsem) sk))
      (STB: stb_global md sk "CRIS_init" = Some fsp)
      (VALID: ✓ rs)
      (EQUIV: rs ≡ r ⋅ rt)
      (PRE: Own r ⊢ fsp.(precond) 0 meta tt↑ tt↑)
      (SAT: Own rt ⊢ P sk)
      (POST: ∀ vret ret, (fsp.(postcond) 0 meta vret ret) -∗ ⌜vret = ret⌝)
    :  
    refines_modsem
      (HModSem.to_mod ((HModInline.inline (SModCancel.to_hmod md)).(HMod.modsem) sk) rs)
      (HModSem.to_mod ((HModInline.inline (SMod.to_hmod ginv (stb_global md) md)).(HMod.modsem) sk) rt).
  Proof.
    r. eapply adequacy_global.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.compile. s. unfold ITree.map.
    destruct (alist_find "CRIS_init" (SModSem.fnsems (SMod.modsem md sk))) eqn:E; cycle 1.
    {
      rewrite !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite StRed.bind. grind.
      destruct (resum IFun False (Choose False)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite [interp_stateE _ _ _]StRed.core. grind.
      ginit. st. i. ss.
    }
    rewrite !alist_find_map/o_map E. s. 
    erewrite !wrap_elimI_well_scoped; cycle 1.
    { unfold SModSem.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    { unfold SModSemCancel.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    ired. destruct p. s.
    unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold inline_hp_fun, interp_sb_hp. s.
    unfold HoareFun.
    
    unfold interp_modE, interp_schE_callE. 
    destruct f.
    assert (SKINCL: incl (SMod.sk md) sk). { eapply Sk.equiv_incl. eauto. }
    assert (TMP:=STB). unfold stb_global in TMP. rewrite E in TMP. depdes TMP.
    hide_l.
    ginit.
    rewrite !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists meta. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists r. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    assert (V: ✓(r ⋅ rt)). { eapply valid_solve_eq; eauto. }
    exists V. ired. _tau. st. st. 
    _iter. _core. st. exists PRE. ired.
    _iter. _tau. st. st. _supd. _iter. _supd.
    _iter. _tau. st. st. rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CRIS_init's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto; cycle 1.
    { eapply Own_equiv in EQUIV. iIntros "H". iModIntro. iApply EQUIV. eauto. }
    econs; eauto using Forall2i.
    econs; s; eauto; try rewrite bind_ret_l; ss.
    { i. specialize (POST vret ret). auto. }
    { eapply elim_rel_refl; eauto. }
    rewrite HModSB.transl_bind HIRed.bind. 
    do 2 f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_ag. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed.
  
  (*** Final Theorem ***)
  Theorem cancellation ginv P fsp meta
    (STB: ∀ sk (EQV: Sk.equiv (SMod.sk md) sk) (SKWF: Sk.wf sk),
          stb_global md sk "CRIS_init" = Some (fsp sk))
    (POST: ∀ sk (EQV: Sk.equiv (SMod.sk md) sk) (SKWF: Sk.wf sk) vret ret,
           ((fsp sk).(postcond) 0 (meta sk) vret ret) -∗ ⌜vret = ret⌝)
    :
    refines (SModCancel.to_hmod md, P ∗∗ (fun sk => (fsp sk).(precond) 0 (meta sk) tt↑ tt↑))
            (SMod.to_hmod ginv (stb_global md) md, P).
  Proof. 
    etrans.
    { eapply cancel_call_rev. }
    etrans; cycle 1.
    { eapply cancel_call. }
    r. esplits; ss.
    ii. eapply Own_split in SRC; eauto. des.
    exists a1. esplits; eauto.
    { eapply cmra_valid_op_l, valid_solve_eq; eauto. }
    {
      inv WFM. econs; eauto. s.
      do 2 rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    }
    eapply cancel_main; eauto.
    - inv WFM. econs; eauto. s.
      rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    - etrans; eauto. r_solve.
  Qed.
    
End CANCEL.

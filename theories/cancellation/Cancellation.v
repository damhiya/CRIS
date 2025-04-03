From iris.proofmode Require Import proofmode.
Require Import Common.

Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import SModCancel HModInline ElimRel StRed.
Require Import CancelLib CancelCall CancelCallRev.
Require Import CancelHead CancelTail CancelSpawn CancelYield.

Set Implicit Arguments.

Import CancelTAC.

Lemma cancel_aux `{Σ: GRA} md rs0 rt0
  rs rt srcs tgts cid st ps pt
  (WF: ✓ rs)       
  (LEN: cid < List.length srcs)
  (REL: Forall2i (thread_rel md cid) 0 srcs tgts)
  (UPD: Own rs ==∗ Own rt)
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 bot7) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  exploit Forall2i_nth; eauto. i. des.
  rename x into src, y into tgt.
  depdes x2.
  hexploit REL. i. eapply Forall2i_len in H. des.
  assert (cid < List.length tgts). { rewrite <- H. eauto. }
  assert (RELS: forall k x y (NEQ: cid ≠ k)
                  (LKX: srcs !! k = Some x)
                  (LKY: tgts !! k = Some y),
                    thread_rel md cid k x y). 
  { i. eapply Forall2i_forall in REL; eauto. }
  clear REL. rename REL0 into REL. unfold elim_rel in REL.
  simpl plus in *. subst.
  destruct (Nat.eq_dec cid cid); ss. clear e.
  rename x0 into SRC, x1 into TGT.
  revert_until md. gcofix CIH. i.
  
  assert (RT: ✓ rt). { eapply Own_wand_valid with (a1:=rs); eauto. }
  punfold REL. depdes REL; subst.
  - _iter. _iter. rewrite SRC TGT. ired.
    hide_l. _coreA.
  - _iter. _iter. rewrite SRC TGT. ired.
    hide_r. des_ifs; cycle 1.
    { unfold triggerUB. ired. _coreA. }
    ired. reveal ITREE.
    _coreA. iterT 2.
    iterL. _supd. iterL. _coreA. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. rewrite !StRed.ret. ired. st. des.
    hexploit Own_bupd_split; eauto. i. des.
    specialize (RET v x eq_refl).
    eapply Own_pure_soundness with (a := a1).
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
    hide_r. _supd. iterL. _coreA. iterL. _coreA.
    iterL. _supd. iterL. _supd. iterT 1. reveal ITREE. des.
    eapply bi.wand_entails, Own_bupd_split in x1. des.
    hide_l. _supd. iterL. _coreE (a1 ⋅ rt).
    assert (UPD': Own (a1 ⋅ a2) ==∗ Own (a1 ⋅ rt)).
    { iIntros "[A1 A2]". iSplitL "A1"; eauto.
      iApply UPD. iApply x3. eauto.
    }
    assert (VALID: ✓ (a1 ⋅ rt) ∧ (Own (a1 ⋅ rt) ==∗ P ∗ Own rt)). 
    { split.
      - eapply bi.wand_entails in UPD'.
        eapply Own_wand_valid; eauto.
        eapply Own_wand_valid, x0.
        iIntros "X"; iMod (x1 with "X") as "[A1 A2]". iSplitL "A1"; eauto.
      - iIntros "[H0 H1]". iFrame. iApply x2. eauto.
    }
    iterL. _coreE VALID. ls.
    iterL. _supd. iterL. _supd.
    iterT 1. reveal ITREE.
    done_by_CIH CIH LKX LKY.
    + iIntros "X"; iMod (x1 with "X") as "[A1 A2]". 
      iApply UPD'. iSplitL "A1"; eauto.
    + eauto.
  - _iter. _iter. rewrite SRC TGT. ired.
    hide_l. _supd. iterL. _coreA. iterL. _coreA. ls. des.
    iterL. _supd. iterL. _supd. iterT 1. reveal ITREE.
    hide_r. _supd. iterL. _coreE x.
    assert (VALID: ✓ x ∧ (Own rs ==∗ P ∗ Own x)).
    { split; eauto. iIntros "H". iMod (UPD with "H") as "H". iApply x1; eauto. }
    iterL. _coreE VALID.
    iterL. _supd. iterL. _supd. iterT 1. reveal ITREE.
    done_by_CIH CIH LKX LKY.
  - eapply cancel_aux_head; eauto. i; eapply CIH; eauto.
  - eapply cancel_aux_tail; eauto. i; eapply CIH; eauto.
  - eapply cancel_aux_spawn; eauto. i; eapply CIH; eauto.
  - eapply cancel_aux_yield; eauto. i; eapply CIH; eauto.
(*FAST*)Qed.

Lemma cancel_main `{Σ: GRA} md
    P fsp meta rs rt r
    (WF: HMod.wf (SModCancel.to_hmod md))
    (SPC: sp_from md "CRIS_init" = Some fsp)
    (VALID: ✓ rs)
    (EQUIV: rs ≡ r ⋅ rt)
    (PRE: Own r ⊢ fsp.(precond) meta tt↑ tt↑)
    (SAT: Own rt ⊢ P)
    (POST: ∀ vret ret, (fsp.(postcond) meta vret ret) ==∗ ⌜vret = ret⌝)
  :  
  refines_mod
    (HMod.to_mod (HModInline.inline (SModCancel.to_hmod md)) rs)
    (HMod.to_mod (HModInline.inline (SMod.to_hmod (sp_from md) md)) rt).
Proof.
  r. eapply adequacy_global.
  instantiate (1:= smj_top).
  instantiate (1:= smj_top).
  unfold Mod.compile. s. unfold ITree.map.
  destruct (alist_find "CRIS_init" (SMod.fnsems md)) eqn:E; cycle 1.
  {
    rewrite !alist_find_map/o_map E. s.
    rewrite /sp_from E in SPC. ss.
  }
  rewrite !alist_find_map/o_map E. s. 
  erewrite !wrap_elimI_well_scoped; cycle 1.
  { unfold SMod.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
  { unfold SModCancel.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
  ired. destruct p. s.
  unfold HMod.sandbox_body, interp_hp_fun. s.
  unfold inline_hp_fun, interp_sb_hp. s.
  unfold HoareFun.
  
  unfold interp_modE, interp_schE_callE. 
  destruct f.
  assert (TMP:=SPC). unfold sp_from in TMP. rewrite E in TMP. depdes TMP.
  hide_l.
  ginit.
  rewrite SBRed.bind SBRed.core HIRed.bind_core HRed.bind HRed.core. ired.
  _iter. _core. st. exists meta. st. ired. 
  _tau. st. _iter. _tau. st. st.
  rewrite HRed.tau. _iter. _tau. st. st.
  rewrite SBRed.bind SBRed.core HIRed.bind_core HRed.bind HRed.core. ired.
  _iter. _core. st. exists (tt↑). st. ired.
  _iter. _tau. st. st. st.
  rewrite HRed.tau. _iter. _tau. st. st.
  rewrite SBRed.bind SBRed.ag HIRed.bind_ag HRed.bind HRed.Assume. ired.
  _iter. _supd. hss. ired. hss. ired.
  _iter. _core. st. exists (r ⋅ rt). st. ired. _tau. st. 
  _iter. _core. st.
  assert (VALID': ✓(r ⋅ rt) ∧ (Own (r ⋅ rt) ==∗ precond fsp meta () ↑ () ↑ ∗ Own rt)).
  { split.
    - rewrite -EQUIV. eauto.
    - iIntros "[R RT]". iFrame. iModIntro. iStopProof. eauto.
  }
  exists VALID'. ired. _tau. st. st.
  _iter. _supd. _iter. _supd.
  _iter. _tau. st. st. rewrite HRed.tau. _iter. _tau. st. st.

  (* CRIS_init's precond all executed. *)
  reveal ITREE. 
  eapply cancel_aux; eauto; cycle 1.
  { eapply Own_equiv in EQUIV. iIntros "H". iModIntro. iApply EQUIV. eauto. }
  econs; eauto using Forall2i.
  econs; s; eauto; try rewrite bind_ret_l; ss.
  { i. specialize (POST vret ret). auto.
    iIntros "H". iMod (POST with "H") as "H". eauto.
  }
  { eapply elim_rel_refl; eauto. }
  rewrite SBRed.bind HIRed.bind. 
  do 2 f_equal. extensionalities.
  rewrite SBRed.bind SBRed.core. do 2 f_equal.
  extensionalities.
  rewrite SBRed.bind SBRed.ag. do 2 f_equal.
  extensionalities.
  rewrite SBRed.ret. ss.
(*FAST*)Qed.

(*** Final Theorem ***)
Theorem cancellation `{Σ: GRA} md P fsp meta
  (SPC: sp_from md "CRIS_init" = Some fsp)
  (POST: ∀ vret ret,
         ((fsp).(postcond) (meta) vret ret) -∗ ⌜vret = ret⌝)
  :
  refines (SModCancel.to_hmod md, P ∗ ((fsp).(precond) (meta) tt↑ tt↑))%I
          (SMod.to_hmod (sp_from md) md, P).
Proof. 
  etrans.
  { eapply cancel_call_rev. }
  etrans; cycle 1.
  { eapply cancel_call. }
  ii; split.
  {
    inv WFM. econs; eauto. s.
    do 2 rewrite List.map_map fst_map_snd.
    do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
  }
  inv WFM. s; i.
  eapply Own_split in SRC; eauto. des.
  exists a1. esplits; eauto.
  { eapply cmra_valid_op_l, valid_solve_eq; eauto. }

  eapply cancel_main; eauto.
  - econs; eauto. s.
    rewrite List.map_map fst_map_snd.
    do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
  - rewrite SRC. rewrite comm. eauto.
  - iIntros (? ?) "H". iModIntro. iApply POST; eauto.
(*FAST*)Qed.

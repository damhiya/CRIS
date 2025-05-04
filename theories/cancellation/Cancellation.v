Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import SModCancel HModInline ElimRel.
Require Import CancelLib InlineIntro InlineElim.
Require Import SimGlobal SimGTactics.
Require Import CancelRet CancelCore CancelPG CancelAssume CancelGuarantee.
Require Import CancelHead CancelTail CancelSpawn CancelYield.

Set Implicit Arguments.

Lemma cancel_aux `{Σ: GRA} md rs0 rt0
  rs rt srcs tgts cid st ps pt
  (WF: ✓ rs)       
  (LEN: cid < List.length srcs)
  (REL: Forall2i (thread_rel md) 0 srcs tgts)
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
                    thread_rel md k x y).
  { i. eapply Forall2i_forall in REL; eauto. }
  clear REL. rename REL0 into REL. unfold elim_rel in REL.
  simpl plus in *. subst.
  rename x0 into SRC, x1 into TGT.
  revert_until md. gcofix CIH. i.
  
  assert (RT: ✓ rt). { eapply Own_wand_valid with (a1:=rs); eauto. }

  punfold REL. depdes REL; subst; i; pclearbot.
  - ziter_r. rewrite TGT. zstep_r.
  - ziter_l. rewrite SRC. zstep_l.
  - eapply cancel_aux_ret; try eassumption; et. i; eapply CIH; eauto.
  - (* Tau case *)
    ziter_l. ziter_r. rewrite SRC TGT.
    zstep_l. zstep_r.
    gstep. econs; econs; eauto using smj_lt_mid_top.
    gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
    intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
  - eapply cancel_aux_core; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_pg; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_Assume; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_Guarantee; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_head; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_tail; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_spawn; try eassumption; et. i; eapply CIH; eauto.
  - eapply cancel_aux_yield; try eassumption; et. i; eapply CIH; eauto.
Unshelve. all: eauto.
(*SLOW*)Admitted.

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
  unfold Mod.compile. s. unfold ITree.map. unfold Mod.prog at 1 2 3.
  destruct (alist_find "CRIS_init" (SMod.fnsems md)) eqn:E; cycle 1.
  { rewrite !alist_find_map /o_map E.
    rewrite /sp_from /Sp.to_sp alist_find_map E in SPC. ss. }
  rewrite !alist_find_map/o_map E. s.
  erewrite !wrap_elimI_well_scoped; cycle 1.
  { unfold SMod.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
  { unfold SModCancel.to_hmod. s.
    rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
  ired. destruct p. s.
  unfold HModTr.sandbox_body, HModTr.trans_ktree. s.
  unfold inline_hp_fun, SModTr.trans_ktree. s.
  unfold SModTr.HoareFun.
  unfold ModTr.trans, ModTr.interp_callE.
  
  destruct f as [sp bd].
  assert (TMP:=SPC).
  rewrite /sp_from /Sp.to_sp alist_find_map E in TMP. depdes TMP.

  ginit.
  zonly_r.
  rewrite SBRed.bind SBRed.core HIRed.bind_core HRed.bind HRed.core.
  zshow.

  ziter_r. zstep_r. exists meta. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. exists (tt↑). zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. exists (r ⋅ rt). zstep_r.

  assert (VALID': ✓(r ⋅ rt) ∧ (Own (r ⋅ rt) ==∗ precond fsp meta () ↑ () ↑ ∗ Own rt)).
  { split.
    - rewrite -EQUIV. eauto.
    - iIntros "[R RT]". iFrame. iModIntro. iStopProof. eauto.
  }
  
  ziter_r. zstep_r. exists VALID'. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  (* CRIS_init's precond all executed. *)
  eapply cancel_aux; eauto; cycle 1.
  { eapply Own_equiv in EQUIV. iIntros "H". iModIntro. iApply EQUIV. eauto. }
  econs; eauto using Forall2i.
  econs; s; eauto; try rewrite bind_ret_l; ss.
  { i. specialize (POST vret ret). auto.
    iIntros "H". iMod (POST with "H") as "H". eauto.
  }
  { eapply elim_rel_refl; eauto. }

  rewrite -/(HModTr.sandbox _ _ _) -HIRed.iter_handle_bind.
  do 2 f_equal. s.
  rewrite SBRed.bind. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.core. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.ag. f_equal. extensionalities.
  rewrite SBRed.ret. ss.
Unshelve. all: eauto.  
(*SLOW*)Admitted.

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
  { eapply inline_elim. }
  etrans; cycle 1.
  { eapply inline_intro. }
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
(*SLOW*)Admitted.

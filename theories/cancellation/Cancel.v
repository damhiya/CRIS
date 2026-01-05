Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.
Require Import CancelCore CancelPG CancelAG CancelSpawn CancelPre CancelPost CancelYield CancelGetTid.

Set Implicit Arguments.

Module Cancel. Section Cancel.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma cancel_elim md {X: Type} (PQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm
  (r_i r_s r_t: Σ) rs_diff srcs tgts cid st ps pt
  (WFS: SMod.cancellable md)
  (MAIN: (SMod.conc_sp_from md) !! speckey_entry = Some (fspec_simple PQ))
  (* (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md))) *)
  (REL: Forall3i (thread_rel PQ N mm (SMod.conc_sp_from md) cid) rs_diff srcs tgts)
  (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
  (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
         TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
  :
  gsim cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
       (Any.pair (ModTr.state_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (SMod.conc_sp_from md) md)) r_i))) (cid, tgts))
       (Any.pair (ModTr.state_encode st) r_t ↑)).
Proof using.
  ginit. move WFS at top. (* move WF at top. *)
  revert_until r_i. gcofix CIH. i.
  destruct (decide (cid < length srcs)) as [Hcid|]; cycle 1.
  { iter_l. erewrite (proj2 (lookup_ge_None srcs cid)); try nia.
    s. step_l. norm_l. step_l. i; ss. }
  inversion REL as [Hlenxy [Hlenyz Hrel]].
  exploit (@Forall3i_nth _ _ _ cid); eauto; try lia; clear REL.
  intros [r_diff [i_s [i_t [Hdiff [Hs [Ht Hcidrel]]]]]]; ss.

  inversion_clear Hcidrel; subst; ss; cycle 1.
  
  assert (Hkey :
    ∀ itr_s itr_t st (r_s r_t: Σ) r_diff,
    ✓ r_s → map_Forall (const is_Some) st →
    (Own r_s ⊢ |==> ([∗ list] i ∈ <[cid := r_diff]> rs_diff, Own i) ∗ Own r_t ∗
       TIDAUTH cid ∗ YIELDAUTH (length (<[cid := r_diff]> rs_diff))) →
    cid < List.length srcs →
    thread_rel PQ N mm (SMod.conc_sp_from md) cid cid r_diff itr_s itr_t →
    gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
      (Any.t * Any.t)%type cancel_eq smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
          (SMod.to_mod ∅ (SMod.cancel md))) r_i)))
              (cid, <[cid:=itr_s]> srcs))
       (Any.pair (ModTr.state_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (SMod.conc_sp_from md) md)) r_i)))
              (cid, <[cid:=itr_t]> tgts))
       (Any.pair (ModTr.state_encode st) r_t ↑))).
  { i. subst. zprogress.
    gbase. eapply CIH; et.
    split.
    { rewrite !length_insert. et. }
    split.
    { rewrite !length_insert. et. }
    i. destruct (classic (cid = i)); cycle 1.
    { rewrite list_lookup_insert_ne in H4; et.
      rewrite list_lookup_insert_ne in H5; et.
      rewrite list_lookup_insert_ne in H6; et.
    }
    subst. rewrite !list_lookup_insert in H4, H5, H6; et; cycle 1.
    { rewrite -Hlenyz. et. }
    { rewrite Hlenxy. et. }
    inv H4. done.
  }
  
  punfold REL; depdes REL; ii; subst; pclearbot.
  - iter_l; rewrite Hs /=; step_l; i; ss.
  - iter_l; rewrite Hs /=; step_l; norm_l.
    iter_l; rewrite list_lookup_insert //; step_l; i; ss.
  - iter_r; rewrite Ht /=; step_r; i; ss.
  - iter_l; rewrite Hs /=.
    iter_r; rewrite Ht /=. destruct cid; s; cycle 1.
    { step_l; rewrite /triggerUB; step_l; i; ss. }
    specialize (RET eq_refl). subst. s. step_l. norm_l.
    step_r. i. step_r. norm_r.
    guardH Hlenxy.
    Ltac sir :=
      match goal with
      | [ H : length _ = length _ |- _ ] =>
          iter_r; rewrite list_lookup_insert ?length_insert -?H //; norm_r; step_r
      end;
      match goal with
      | [ |- ∀ _, _ ] => i; step_r
      | _ => idtac
      end; norm_r; rewrite !list_insert_insert.
    sir. sir.
    rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
    sir; sir; sir.
    rewrite bind_ret_l Any.pair_split /= bind_ret_l.
    sir. sir.
    iter_r. rewrite list_lookup_insert -?Hlenyz //. step_r. norm_r.
    rewrite Any.pair_split /=. ired. hss. ired.
    sir. ired. sir. ired. sir. ired.
    rewrite Any.pair_split /=. ired. sir. ired. sir.
    iter_r. rewrite list_lookup_insert -?Hlenyz //. step_r. norm_r.

    gstep. econs. econs. 
    r. esplits; eauto; hss.
    eapply Own_pure_soundness.
    { eapply Own_wand_valid; [|instantiate (1 := r_s); eauto].
      rewrite RS; eauto. iIntros ">(_ & $ & _)"; eauto. }
    { rewrite x2 x5. iIntros ">[_ >[[$ _] _]]". }
  - iter_l. iter_r. rewrite Hs Ht /=. step_l. norm_l. step_r. norm_r. eapply Hkey; et.
    { rewrite list_insert_id //. }
    { econs; eauto. }
  - eapply cancel_core; eauto.
  - eapply cancel_pg; eauto.
  - eapply cancel_ag; eauto.
  - eapply cancel_yield; eauto.
  - eapply cancel_spawn; eauto.
  - eapply cancel_pre; eauto.
  - eapply cancel_post; eauto.
  - eapply cancel_gettid; eauto.
(*SLOW*)Qed.


Lemma cancel_main md rs rt {X} (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm
  (WFS: SMod.cancellable md)
  (MAIN: SMod.conc_sp_from md !! speckey_entry = Some (fspec_simple PQ))
  (WF: Mod.wf (SMod.to_mod ∅ (SMod.cancel md)))
  (VALID: ✓ rs)
  (RES: Own rs ⊢ |==> TID 0 ∗ YIELD 0 ∗ winv (↑N, ↑N) ∗ Own rt ∗ (PQ mm).1 tt↑ ∗ TIDAUTH 0 ∗ YIELDAUTH 1)
  :  
  refines_lmod
    (Mod.to_lmod (MInline.inline (SMod.to_mod ∅ (SMod.cancel md))) rs)
    (Mod.to_lmod (MInline.inline (SMod.to_mod (SMod.conc_sp_from md) md)) rt).
Proof using.
  r. eapply gsim_adequacy.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.

  rewrite !lookup_fmap !lookup_omap !lookup_fmap.
  destruct ((SMod.fnsems md) !! None) eqn: FIND; rewrite ?FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. destruct o; ss; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  rewrite /ModTr.trans_fnsem /SModTr.trans_fnsem.
  destruct p as [msk [fspo bd]]. s. ired.
  (* assert (SCP: incl scp (SMod.scopes md)). *)
  (* { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. } *)
  erewrite !sandbox_inline_commute; et; cycle 1.
  { r in WFS. hexploit WFS; eauto. i; des; eauto. }
  { hexploit (SMod.well_scoped_fns md None (msk, (fspo, bd))).
    { rewrite lookup_omap FIND //. }
    i; des. rewrite /SMod.to_mod; ss. }
  { r in WFS. hexploit WFS; eauto. i; des; eauto. }
  { hexploit (SMod.well_scoped_fns md None (msk, (fspo, bd))).
    { rewrite lookup_omap FIND //. }
    i; des. rewrite /SMod.to_mod; ss. }
  rewrite /SB.sandbox_body. s.
 
  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=λ vrs vrt, cancel_eq vrs vrt). i. gstep. econs. econs.
    destruct SIM. des. et. }
  iter_l. step_l. norm_l. iter_l. step_l. norm_l.
  exploit WFS; et. i; des; subst; ss.

  r in x2. des. destruct fspo; ss. inv x2.
  rewrite /SMod.conc_sp_from lookup_insert_ne // /SMod.sp_from lookup_kmap_Some in MAIN.
  des. rewrite /SMod.lift_fn in MAIN. des_ifs. rewrite !lookup_omap /= !lookup_fmap lookup_omap FIND /= in MAIN0.
  inv MAIN0.

  dup x0. r in x0; des.
  rewrite SBRed.bind SBRed.vis !vis_trigger x0. ired.
  iter_r. step_r. exists (N, 0). step_r. ired. iter_r. step_r. ired.
  rewrite SBRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x0. ired.
  iter_r. step_r. exists mm. step_r. ired. iter_r. step_r. ired.
  rewrite SBRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x0. ired.
  iter_r. step_r. exists (tt↑). step_r. ired. iter_r. step_r. ired.
  rewrite SBRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x4. ired.
  iter_r. step_r. ired. rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l !bind_bind.
  iter_r. step_r. rewrite (assoc _ (Own rt)) (assoc _ (winv (↑N, ↑N))) (assoc _ (YIELD 0) _) (assoc _ (TID 0)) in RES.
  hexploit (Own_bupd_split); eauto. i; des.
  do 3 rewrite -assoc in RES.
  assert (✓ a1).
  { eapply (Own_wand_valid rs); eauto. iIntros "P". iPoseProof (H with "P") as "[>$ _]". eauto. }
  hexploit (Own_bupd_split a1); eauto.
  { iIntros "P"; iPoseProof (H0 with "P") as "(A & B & C & D & E)". iModIntro. iSplitR "E".
    { iCombine "A B C D" as "A". iApply "A". }
    { iApply "E". }
  }
  i; des.
  exists a0. step_r. ired. iter_r. step_r. unshelve eexists; ired.
  { esplits; eauto.
    { eapply (Own_wand_valid a1); eauto. iIntros "P". iPoseProof (H3 with "P") as "[>$ _]". eauto. }
    { iIntros "P"; iPoseProof (H4 with "P") as "($ & $ & $ & $)". eauto. }
  }
  iter_r. step_r. ired. step_r. ired. rewrite Any.pair_split /= bind_ret_l.
  iter_r. step_r. ired. iter_r. step_r. ired.
  rewrite SBRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x4. ired.
  iter_r. step_r. ired. rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l !bind_bind.
  iter_r. step_r. exists a1. step_r. ired. iter_r. step_r. unshelve eexists; ired.
  { esplits; eauto. iIntros "P"; iPoseProof (H3 with "P") as ">[A B]". iFrame.
    iModIntro. rewrite /precond /fspec_simple. iSplit; eauto. iApply H5; eauto. }
  step_r. iter_r. step_r. ired. rewrite Any.pair_split /= !bind_ret_l.
  iter_r. step_r. ired. iter_r. step_r. ired. rewrite SBRed.ret bind_ret_l SBRed.bind MIRed.bind.

  (* set (itr := vret <- SModTr.trans true (sp_from md) (bd arg);; _: itree crisE Any.t). *)
  (* replace (interpV (SB.handle_sandbox true msk scp) itr) with (SB.sandbox true msk scp itr) by refl. *)
  (* rewrite SBRed.bind MIRed.bind. *)
  set (itr0 := (λ _, inline_body _ _)).
  eassert (itr0 = λ vret, (ret <- trigger (Choose Any.t);; tau;;
         trigger (Guarantee (TID 0 ∗ YIELD 0 ∗ winv (↑N, ↑N)));;; tau;;
         trigger (Guarantee (⌜vret = ret⌝ ∗ (PQ mm).2 vret));;; tau;;
         Ret ret)).
  { subst itr0. rewrite /postcond /fspec_simple. eapply func_ext. i.
    rewrite SBRed.bind SBRed.vis vis_trigger x3 MIRed.bind MIRed.core. ired. f_equal.
    extensionalities. ired. do 2 f_equal.
    rewrite SBRed.ret MIRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x6 MIRed.bind MIRed.ag. ired. f_equal.
    extensionalities. ired. do 2 f_equal.
    rewrite SBRed.ret MIRed.ret bind_ret_l SBRed.bind SBRed.vis !vis_trigger x6 MIRed.bind MIRed.ag. ired. f_equal.
    extensionalities. ired. do 2 f_equal.
    rewrite SBRed.ret MIRed.ret bind_ret_l SBRed.ret MIRed.ret //.
  }
  rewrite H6. rewrite interpV_bind.

  gfinal. right.

  eapply (cancel_elim rs a1 (rs_diff:=[ε])); eauto.
  { rewrite /SMod.conc_sp_from /SMod.sp_from lookup_insert_ne // lookup_kmap_Some.
    exists None. esplit; eauto. rewrite !lookup_omap !lookup_fmap !lookup_omap FIND //. }
  { econs; et.
    split; ss.
    i. destruct i; ss. inv H0. 
    econs; et.
    { rewrite /SMod.conc_sp_from /SMod.sp_from lookup_insert_ne // lookup_kmap_Some.
      exists None. esplit; eauto. rewrite !lookup_omap !lookup_fmap !lookup_omap FIND //. }
    eapply elim_rel_cancel; et.
  }
  { eapply (SMod.nodup_init). inv WF. ss. }
  ss. iIntros "P". iPoseProof (H with "P") as ">[$ P]".
  iPoseProof (H1 with "P") as "[$ $]".
  iModIntro. iSplit; eauto. iApply Own_unit.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.

End Cancel.

Section Cancel.
Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

(*** Final Theorem ***)
Theorem cancellation md P {X: Type} (PQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm
  (WFS: SMod.cancellable md)
  (WF: Mod.wf (SMod.to_mod ∅ (SMod.cancel md)))
  (MAIN: SMod.conc_sp_from md !! speckey_entry = Some (fspec_simple PQ))
  :
  refines (SMod.to_mod ∅ (SMod.cancel md), (P ∗ TIDAUTH 0 ∗ YIELDAUTH 1 ∗ TID 0 ∗ YIELD 0 ∗ winv (↑N, ↑N) ∗ (PQ mm).1 tt↑)%I)
          (SMod.to_mod (SMod.conc_sp_from md) md, P).
Proof using. 
  etrans.
  { eapply inline_elim. }
  etrans; cycle 1.
  { eapply inline_intro. }
  ii; split.
  { 
    inv WFM. econs; eauto. s.
    ii. ss. r in wf_fns. specialize (wf_fns i). ss.
    rewrite !lookup_fmap in H, wf_fns. destruct (SMod.fnsems md !! i); ss.
    destruct o; ss; cycle 1.
    { inv H. hexploit wf_fns; eauto. }
    inv H. destruct p as [msk [fspo bd]]. ss.
  }
  inv WFM. s; i.
  rewrite assoc in SRC.
  hexploit (Own_bupd_split); eauto.
  intros [rt [ra [Hr1 [Hr2 Hr3]]]].
  exists rt. esplits; et.
  { eapply Own_wand_valid; [iIntros "S"; iPoseProof (Hr1 with "S") as ">[$ _]"; done|done]. }
  { rewrite Hr2. eauto. }
  eapply cancel_main; eauto.
  iIntros "S". iPoseProof (Hr1 with "S") as ">[$ A]".
  rewrite Hr3. iDestruct "A" as "(A & B & C & D & E)"; iFrame; eauto.
(*SLOW*)Qed.

End Cancel. End Cancel.

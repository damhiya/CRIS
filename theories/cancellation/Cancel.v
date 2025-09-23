Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.
Require Import CancelCore CancelPG CancelAG CancelSpawn CancelPre CancelPost CancelYield CancelGetTid.

Set Implicit Arguments.

Module Cancel. Section Cancel.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma cancel_elim md (r_i r_s r_t: Σ) rs_diff srcs tgts cid st ps pt
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (REL: Forall3i (thread_rel (sp_from md) cid) rs_diff srcs tgts)
  (WFR: ✓ r_s)
  (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
         TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
  :
  gsim cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp_none (SMod.cancel md))) r_i))) (cid, srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (sp_from md) md)) r_i))) (cid, tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑)).
Proof using.
  ginit. move WFS at top. move WF at top.
  revert_until r_i. gcofix CIH. i.
  destruct (decide (cid < length srcs)) as [Hcid|]; cycle 1.
  { ziter_l. erewrite (proj2 (lookup_ge_None srcs cid)); try nia.
    s. zstep_l. zstep_l.
  }
  inversion REL as [Hlenxy [Hlenyz Hrel]].
  exploit (@Forall3i_nth _ _ _ cid); eauto; try lia; clear REL.
  intros [r_diff [i_s [i_t [Hdiff [Hs [Ht Hcidrel]]]]]]; ss.

  inversion_clear Hcidrel; subst; ss; cycle 1.
  
  assert (Hkey :
    ∀ itr_s itr_t st (r_s r_t: Σ) r_diff,
    ✓ r_s →
    (Own r_s ⊢ |==> ([∗ list] i ∈ <[cid := r_diff]> rs_diff, Own i) ∗ Own r_t ∗
       TIDAUTH cid ∗ YIELDAUTH (length (<[cid := r_diff]> rs_diff))) →
    cid < List.length srcs →
    thread_rel (sp_from md) cid cid r_diff itr_s itr_t →
    gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
      (Any.t * Any.t)%type cancel_eq smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
          (SMod.to_mod sp_none (SMod.cancel md))) r_i)))
              (cid, <[cid:=itr_s]> srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (sp_from md) md)) r_i)))
              (cid, <[cid:=itr_t]> tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑))).
  { i. subst. zprogress.
    gbase. eapply CIH; et.
    split.
    { rewrite !length_insert. et. }
    split.
    { rewrite !length_insert. et. }
    i. destruct (classic (cid = i)); cycle 1.
    { rewrite list_lookup_insert_ne in H3; et.
      rewrite list_lookup_insert_ne in H4; et.
      rewrite list_lookup_insert_ne in H5; et.
    }
    subst. rewrite !list_lookup_insert in H3, H4, H5; et; cycle 1.
    { rewrite -Hlenyz. et. }
    { rewrite Hlenxy. et. }
    inv H3. done.
  }
  
  punfold REL; depdes REL; ii; subst; pclearbot.
  - ziter_l; rewrite Hs /=; zstep_l.
  - ziter_l; rewrite Hs /=; zstep_l; ziter_l; zstep_l.
  - ziter_r; rewrite Ht /=; zstep_r.
  - ziter_l; rewrite Hs /=.
    ziter_r; rewrite Ht /=. destruct cid; s; cycle 1.
    { zstep_l. zstep_l. }
    specialize (RET eq_refl). subst. s. zstep_l.
    zstep_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ired.
    ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r.
    gstep. econs. econs.
    r. esplits; et; hss.
    eapply Own_pure_soundness.
    { eapply Own_wand_valid; [|instantiate (1 := r_s); eauto].
      rewrite RS; eauto. iIntros ">(_ & $ & _)"; eauto. }
    { rewrite x2. iIntros ">[$ _]". }
  - ziter_l. ziter_r. rewrite Hs Ht /=. zstep_l. zstep_r. eapply Hkey; et.
    { rewrite list_insert_id //. }
    { econs; eauto. }
  - eapply cancel_core; eauto.
  - eapply cancel_pg; eauto.
  - eapply cancel_ag; eauto.
  - eapply cancel_yield; eauto.
  - eapply cancel_spawn; et.
  - eapply cancel_pre; et.
  - eapply cancel_post; et.
  - eapply cancel_gettid; eauto.
(*SLOW*)Qed.

Lemma cancel_main md rs rt
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (VALID: ✓ rs)
  (RES: Own rs ⊢ |==> Own rt ∗ TIDAUTH 0 ∗ YIELDAUTH 1)
  :  
  refines_lmod
    (Mod.to_lmod (MInline.inline (SMod.to_mod sp_none (SMod.cancel md))) rs)
    (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rt).
Proof using.
  r. intro arg. eapply gsim_adequacy.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.  

  rewrite !alist_find_map_snd.
  destruct (alist_find None (SMod.fnsems md)) eqn: FIND; rewrite FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. rewrite /ModTr.trans_ktree.
  destruct f as [[[img msk] scp] [fspo bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. }
  erewrite !sandbox_inline_commute; et.
  (* erewrite sandbox_inline_commute; et. *)
  rewrite /SB.sandbox_body. s.
 
  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=λ vrs vrt, cancel_eq vrs vrt). i. gstep. econs. econs.
    destruct SIM. des. et. }
  ziter_l. zstep_l. ziter_l. zstep_l.
  exploit WFS; et. i; des; subst; ss.

  hexploit x2; eauto; i; subst; ss.
  ziter_r. zstep_r. exists tt. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. exists arg. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. ired.
  ziter_r. zstep_r. exists rt. zstep_r. ziter_r. zstep_r.
  unshelve eexists.
  { split; eauto. eapply Own_wand_valid; cycle 1; eauto.
    rewrite RES. iIntros ">[$ _]"; eauto. }
  ired. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
  ziter_r. zstep_r.
  set (itr := vret <- SModTr.trans true (sp_from md) (bd arg);; _: itree crisE Any.t).
  replace (interpV (SB.handle_sandbox true msk scp) itr) with (SB.sandbox true msk scp itr) by refl.
  rewrite SBRed.bind MIRed.bind.
  set (itr0 := (λ _, inline_body _ _)).
  eassert (itr0 = λ vret, ret <- trigger (Choose Any.t);; tau;; trigger (Guarantee ⌜vret = ret⌝);;; tau;; Ret ret).
  { subst itr0. eapply func_ext. i.
    rewrite SBRed.bind SBRed.choose MIRed.core. f_equal.
    extensionalities. do 2 f_equal.
    rewrite SBRed.bind SBRed.Guarantee MIRed.ag. f_equal.
    extensionalities. do 2 f_equal.
    rewrite SBRed.ret MIRed.ret. refl.
  }
  rewrite H. rewrite Red.bind.

  gfinal. right.

  eapply (cancel_elim rs rt (rs_diff:=[ε])); eauto.
  { econs; et.
    split; ss.
    i. destruct i; ss. inv H0. 
    (* exploit WFS; et. i. subst. *)

    econs; et.
    eapply elim_rel_cancel; et.
  }
  ss. rewrite right_id assoc -Own_op left_id. rewrite RES.
  iIntros ">$"; eauto.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.

End Cancel.

Section Cancel.
Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

(*** Final Theorem ***)
Theorem cancellation md P
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  :
  refines (SMod.to_mod sp_none (SMod.cancel md), (P ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I)
          (SMod.to_mod (sp_from md) md, P).
Proof using. 
  etrans.
  { eapply inline_elim. }
  etrans; cycle 1.
  { eapply inline_intro. }
  ii; split.
  {
    inv WFM. econs; eauto. s.
    repeat rewrite List.map_map fst_map_snd.
    repeat rewrite List.map_map fst_map_snd in wf_fns. eauto.
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
  rewrite Hr3; iFrame; eauto.
(*SLOW*)Qed.

End Cancel. End Cancel.

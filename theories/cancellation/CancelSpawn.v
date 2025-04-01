Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelLib.

Import CancelTAC.

Lemma cancel_aux_spawn `{Σ: GRA} md
  ginv r ps pt srcs tgts
  cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT f fn args
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md ginv cid k x y)
  (STB: sp_from md fn = Some f)
  (KTR: ∀ tid, upaco3 (@elim_rel_def _ md ginv _) bot3 l (ktrS tid) (ktrT tid))
  (SRC : srcs !! cid = Some (Ret ();;; interp_hp (x <- SpawnCancelE fn args;; ktrS x)))
  (TGT : tgts !! cid = Some (Ret ();;; interp_hp (cancel_term md ginv meta Q (x <- HoareSpawnE ginv f fn args;; ktrT x))))
  (CIH: ∀ rs rt srcs tgts cid st ps pt X (meta : X) Q itrS itrT l,
      ✓ rs → (Own rs ==∗ Own rt) →
      List.length srcs = List.length tgts →
      cid < List.length srcs → cid < List.length tgts → 
      srcs !! cid = Some (Ret ();;; interp_hp itrS) →
      tgts !! cid = Some (Ret ();;; interp_hp (cancel_term md ginv meta Q itrT)) →
      (∀ vret ret, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝) →
      paco3 (@elim_rel_def _ md ginv _) bot3 l itrS itrT →
      (∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md ginv cid k x y)
      → CANCEL_GOAL md r ginv rs0 rt0 ps pt srcs tgts cid st rs rt)
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) ginv rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r. _iter. _iter. rewrite SRC TGT. ired.
  hide_l. _coreA.
  iterT 2. iterL. _coreA. ls.
  iterT 2. iterL. tau 1. ls.
  rewrite !length_insert.
  rewrite <- insert_app_l; eauto.
  match goal with [|-context[tgts ++ ?t]] =>
    assert(LTT: cid < List.length (tgts ++ t)) by (rewrite length_app; nia)
  end.
  iterT 2. iterL. _supd.
  iterL. _coreA. iterL. _coreA. ls.
  iterL. _supd. iterL. _supd.
  iterT 2. iterL. _supd.
  iterL. _coreA. iterL. _coreA. ls.
  iterL. _supd. iterL. _supd.
  iterT 2. iterL. tau 1. ls.
  reveal ITREE.
  hide_r. tau 1.
  rewrite -insert_app_l; eauto.
  match goal with [|-context[srcs ++ ?t]] =>
    assert(LTS: cid < List.length (srcs ++ t)) by (rewrite length_app; nia)
  end.
  iterT 2.
  iterL. tau 1. ls.
  hexploit sp_in_alist_find; eauto. i. des.
  reveal ITREE.
  rewrite !alist_find_map_snd !H. s.
  erewrite wrap_elimI_well_scoped; cycle 1.
  {
    instantiate (1:= fn).
    s. unfold interp_sb_hp_cancel. s.
    rewrite alist_find_map_snd H. ss.
  }
  erewrite wrap_elimI_well_scoped; cycle 1.
  {
    instantiate (1:= fn).
    s. unfold interp_sb_hp. s.
    rewrite alist_find_map_snd H. ss.
  }
  ired.
  unfold interp_hp_fun, inline_hp_fun, HMod.sandbox_body. s.
  unfold interp_sb_hp, interp_sb_hp_cancel. s.
  hide_l. _iter.
  rewrite list_lookup_insert_ne; try nia.
  rewrite list_lookup_length. ired.
  assert (forall x, List.length tgts < List.length (tgts ++ [x])).
  { i. rewrite length_app. s. nia. }
  hexploit (Own_bupd_split rt); eauto. i. des.
  hexploit (Own_bupd_split x1); eauto.
  i. des.
  _coreE x.
  iterT 2. iterL. _coreE args. ls.
  iterT 2. iterL. _supd. iterL. _coreE (a0 ⋅ a1 ⋅ x3). ls.
  assert (UPD': Own rs ==∗ Own (a0 ⋅ a1 ⋅ x3)).
  {
    iIntros "H". iPoseProof (UPD with "H") as ">H".
    iPoseProof (H1 with "H") as ">[H0 H1]".
    iPoseProof (H3 with "H1") as "H1".
    iPoseProof (H4 with "H1") as ">[H1 H2]".
    iPoseProof (H6 with "H2") as "H2".
    iModIntro. rewrite !Own_op. iFrame.
  }
  assert (VALID: ✓(a0 ⋅ a1 ⋅ x3) ∧ (Own (a0 ⋅ a1 ⋅ x3) ==∗ precond f x args x0 ∗ Own x3)).
  { split.
    - eapply Own_wand_valid with (a1 := rs); eauto.
    - iIntros "((H0 & H1) & H2)". iFrame.
      iPoseProof (H5 with "H0") as "H0".
      iPoseProof (H2 with "H1") as "H1".
      iApply "H1". eauto.
  }
  iterL. _coreE VALID. ls.
  iterL. _supd. iterL. _supd.
  iterT 2.
  reveal ITREE.
  rewrite LEN.
  prb. gbase. pclearbot.
  eapply CIH; try (rewrite !length_insert !length_app; s; nia); swap 4 6; swap 5 6.
  { auto. }
  { auto. }
  {
    rewrite list_lookup_insert_ne; try nia.
    rewrite -LEN list_lookup_length bind_ret_l. refl.
  }
  { eapply elim_rel_refl; eauto. }
  {
    rewrite list_lookup_insert; eauto; cycle 1.
    { rewrite length_insert length_app. s. nia. }
    grind. unfold cancel_term, inline_hp.
    match goal with [|-context[translate (_ ?scopes) ?itr]]=>
      fold (HMod.sandbox scopes itr)
    end.
    rewrite -HIRed.iter_handle_bind SBRed.bind.
    do 4 f_equal. extensionalities.
    rewrite SBRed.bind SBRed.core.
    f_equal. extensionalities.
    rewrite SBRed.bind SBRed.ag SBRed.ret.
    refl.
  }
  { i. nia. }
  i. rewrite list_lookup_insert_ne in H9; eauto.
  destruct (Nat.eq_dec cid k).
  {
    subst k. rewrite list_lookup_insert in H9; cycle 1.
    { rewrite length_app. s. nia. }
    rewrite list_lookup_insert in H8; cycle 1.
    { rewrite length_app. s. nia. }
    inv H9. econs; eauto; cycle 1.
    { destruct (Nat.eq_dec cid (base.length tgts)); try nia. grind. }
    {
      destruct (Nat.eq_dec cid (base.length tgts)); try nia.
      instantiate (1:= ktrT (base.length tgts)).
      unfold yield_post. ired. rewrite -HRed.tau.
      do 6 f_equal.
    }
    eapply KTR.
  }
  rewrite !list_lookup_insert_ne in H8, H9; try nia.
  eapply lookup_snoc_Some in H8, H9. des; try nia.
  specialize (RELS k x7 y n H11 H10).
  inv RELS. econs; eauto; des_ifs.
Qed.

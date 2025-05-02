From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelLib.

Import CancelTAC.

Lemma cancel_aux_spawn `{Σ: GRA} md
  r ps pt srcs tgts
  cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT f fn args
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md cid k x y)
  (STB: sp_from md fn = Some f)
  (KTR: ∀ tid, upaco3 (@elim_rel_def _ md _) bot3 l (ktrS tid) (ktrT tid))
  (SRC : srcs !! cid = Some (Ret ();;; HModTr.trans (x <- SpawnCancelE fn args;; ktrS x)))
  (TGT : tgts !! cid = Some (Ret ();;; HModTr.trans (cancel_term md meta Q (x <- HoareSpawnE f fn args;; ktrT x))))
  (CIH: ∀ rs rt srcs tgts cid st ps pt X (meta : X) Q itrS itrT l,
      ✓ rs → (Own rs ==∗ Own rt) →
      List.length srcs = List.length tgts →
      cid < List.length srcs → cid < List.length tgts → 
      srcs !! cid = Some (Ret ();;; HModTr.trans itrS) →
      tgts !! cid = Some (Ret ();;; HModTr.trans (cancel_term md meta Q itrT)) →
      (∀ vret ret, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝) →
      paco3 (@elim_rel_def _ md _) bot3 l itrS itrT →
      (∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md cid k x y)
      → CANCEL_GOAL md r rs0 rt0 ps pt srcs tgts cid st rs rt)
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r. _iter. _iter. rewrite SRC TGT. ired.
  hide_r.
  rewrite !alist_find_map_snd. remember wrap_elimI as WRAP; guardH HeqWRAP.
  destruct (alist_find fn (SMod.fnsems md)) eqn: EQ; s; cycle 1.
  { unfold ModTr.interp_stateE, triggerUB, ModTr.pure_state. ired.
    gstep. econs. econs. ss. }
  ired.
  reveal ITREE.
  hide_l. _coreA.
  iterT 2. iterL. _coreA. ls.
  iterT 2. iterL.
  rewrite !alist_find_map_snd EQ. remember wrap_elimI as WRAP'; guardH HeqWRAP'.
  s. ired.
  tau 1. ls.
  rewrite !length_insert.
  rewrite <- insert_app_l; eauto.
  match goal with [|-context[tgts ++ ?t]] =>
    assert(LTT: cid < List.length (tgts ++ t)) by (rewrite length_app; nia)
  end.
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
  unguard. subst.
  erewrite wrap_elimI_well_scoped; cycle 1.
  {
    instantiate (1:= fn).
    s. unfold SModCancel.trans_ktree.
    rewrite alist_find_map_snd EQ. ss.
  }
  erewrite wrap_elimI_well_scoped; cycle 1.
  {
    instantiate (1:= fn).
    s. unfold SModTr.trans_ktree. s.
    rewrite alist_find_map_snd EQ. ss.
  }
  unfold SModTr.trans_ktree, inline_hp_fun, HModTr.sandbox_body. s.
  unfold SModTr.trans_ktree, SModCancel.trans_ktree. s.
  hide_l. _iter.
  rewrite list_lookup_insert_ne; try nia.
  rewrite list_lookup_length. ired.
  assert (forall x, List.length tgts < List.length (tgts ++ [x])).
  { i. rewrite length_app. s. nia. }
  hexploit (Own_bupd_split rt); eauto. i. des.
  rewrite EQ in H. depdes H.
  _coreE x.
  iterT 2. iterL. _coreE args. ls.
  iterT 2. iterL. _supd. iterL. _coreE (a1 ⋅ x1). ls.
  assert (UPD': Own rs ==∗ Own (a1 ⋅ x1)).
  {
    iIntros "H". iPoseProof (UPD with "H") as ">H".
    iPoseProof (H1 with "H") as ">[H0 H1]".
    iPoseProof (H3 with "H1") as "H1".
    iModIntro. rewrite !Own_op. iFrame.
  }
  assert (VALID: ✓(a1 ⋅ x1) ∧ (Own (a1 ⋅ x1) ==∗ precond f x args x0 ∗ Own x1)).
  { split.
    - eapply Own_wand_valid with (a1 := rs); eauto.
    - iIntros "(H1 & H2)". iFrame.
      iPoseProof (H2 with "H1") as "H1".
      iApply "H1".
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
    match goal with [|-context[interpV (_ ?scopes) ?itr]]=>
      fold (HModTr.sandbox scopes itr)
    end.
    unfold cancel_term, inline_hp.
    rewrite SBRed.bind HIRed.iter_handle_bind. ired.
    do 3 f_equal. extensionalities.
    rewrite SBRed.bind SBRed.core.
    do 2 f_equal. extensionalities.
    rewrite SBRed.bind SBRed.ag SBRed.ret.
    refl.
  }
  { i. nia. }
  i. rewrite list_lookup_insert_ne in H5; eauto.
  destruct (Nat.eq_dec cid k).
  {
    subst k. rewrite list_lookup_insert in H5; cycle 1.
    { rewrite length_app. s. nia. }
    rewrite list_lookup_insert in H4; cycle 1.
    { rewrite length_app. s. nia. }
    inv H5. econs; eauto; cycle 1.
    { destruct (Nat.eq_dec cid (base.length tgts)); try nia. grind. }
    {
      destruct (Nat.eq_dec cid (base.length tgts)); try nia.
      instantiate (1:= ktrT (base.length tgts)).
      ired. rewrite -HRed.tau.
      repeat f_equal.
    }
    eapply KTR.
  }
  rewrite !list_lookup_insert_ne in H4, H5; try nia.
  eapply lookup_snoc_Some in H4, H5. des; try nia.
  specialize (RELS k x4 y n H7 H6).
  inv RELS. econs; eauto; des_ifs.
Unshelve. all: eauto.
(*SLOW*)Qed.

Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelLib.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable md: SMod.t.

  Import CancelTAC.

  Lemma cancel_aux_yield
    ginv sk (SKINCL: incl (SMod.sk md) sk) (SKWF: Sk.wf sk) r ps pt srcs tgts
    cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT tid
    (WFS: ✓ rs) (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (LENS: cid < List.length srcs)
    (LENT: cid < List.length tgts)
    (LEN: List.length srcs = Datatypes.length tgts)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md ginv sk cid k x y)
    (KTR: ∀ x, upaco3 (@elim_rel_def _ md ginv sk _) bot3 l (ktrS x) (ktrT x))
    (SRC : srcs !! cid = Some (Ret ();;; interp_hp (x <- trigger (Yield tid);; ktrS x)))
    (TGT : tgts !! cid = Some (Ret ();;; interp_hp (cancel_term md ginv sk cid meta Q (x <- HoareYieldE (ginv sk) tid;; ktrT x))))
    (CIH: ∀ rs rt srcs tgts cid st ps pt X (meta : X) Q itrS itrT l,
        ✓ rs → (Own rs ==∗ Own rt) →
        List.length srcs = List.length tgts →
        cid < List.length srcs → cid < List.length tgts → 
        srcs !! cid = Some (Ret ();;; interp_hp itrS) →
        tgts !! cid = Some (Ret ();;; interp_hp (cancel_term md ginv sk cid meta Q itrT)) →
        (∀ vret ret, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) →
        paco3 (@elim_rel_def _ md ginv sk _) bot3 l itrS itrT →
        (∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md ginv sk cid k x y)
        → CANCEL_GOAL md r ginv sk rs0 rt0 ps pt srcs tgts cid st rs rt)
    :
    CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) ginv sk rs0 rt0 ps pt srcs tgts cid st rs rt.
  Proof.
    r. _iter. _iter. rewrite SRC TGT. ired.
    hide_r. tau 1.
    reveal ITREE. hide_l.
    _supd. iterL. _coreA. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. tau 1. ls. des.
    hexploit (Own_bupd_split rt); eauto. i. des.
    assert (UPD': Own rs ==∗ Own (a1 ⋅ x)).
    {
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H with "H") as ">[H0 H1]".
      iModIntro. iSplitL "H0"; eauto.
      iApply H1; eauto.
    }
    assert (VALID: ✓ (a1 ⋅ x)).
    { eapply Own_wand_valid with (a1 := rs); eauto. }
    destruct (Nat.eq_dec cid tid).
    {
      (* yield to itself *)
      subst tid.
      iterT 2. iterL. tau 1. iterT 2.
      iterL. _supd. iterL. _coreE (a1 ⋅ x).
      assert (SAT: ✓ (a1 ⋅ x) ∧ (Own (a1 ⋅ x) -∗ ginv sk cid ∗ Own x)).
      { split; eauto. iIntros "[A X]". iFrame. iApply H0. eauto. }
      iterL. _coreE SAT. ls.
      iterL. _supd. iterL. _supd.
      iterT 1.
      reveal ITREE. hide_r. iterT 1. reveal ITREE.
      prb. gbase. pclearbot.
      eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); eauto; grind.
      rewrite !list_lookup_insert_ne in H3, H4; eauto.
    }
    destruct (classic (tid < List.length srcs)); cycle 1.
    {
      reveal ITREE.
      hide_r. eapply Nat.le_ngt, lookup_ge_None_2 in H2.
      _iter. rewrite list_lookup_insert_ne; [|et]. rewrite H2.
      s. unfold triggerUB. ired. _coreA.
    }
    exploit lookup_lt_is_Some_2; eauto. i. inv x3.
    exploit (lookup_lt_is_Some_2 tgts tid); [nia|]. i. inv x4.
    assert (tid < base.length tgts) by nia.
    hexploit RELS; eauto. i.
    depdes H6.
    (* move to another thread *)
    destruct (Nat.eq_dec tid cid); try nia.
    subst. _iter.
    match goal with [|-context[interp_stateE _ (_ <- ?tm ?;; _)]]=>
      replace tm with (tgts !! tid) by (rewrite list_lookup_insert_ne; eauto)
    end.
    rewrite H4. ired. tau 2.
    iterT 1. iterL. tau 1. ls. iterT 2.
    iterL. _supd. iterL. _coreE (a1 ⋅ x). ls.
    assert (SAT: ✓ (a1 ⋅ x) ∧ (Own (a1 ⋅ x) -∗ ginv sk tid ∗ Own x)).
    { split; eauto. iIntros "[A X]". iFrame. iApply H0. eauto. }
    iterL. _coreE SAT. ls.
    iterL. _supd. iterL. _supd.
    reveal ITREE.
    prb. gbase. pclearbot.
    eapply CIH with (Q:=Q0); try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind).
    { eauto. }
    { eauto. }
    { rewrite list_lookup_insert_ne; eauto.
      rewrite H3. grind. rewrite -interp_hp_tau. refl.
    }
    { unfold cancel_term. rewrite -interp_hp_tau -bind_tau. refl. }
    { rewrite length_insert. nia. }
    { eauto. }
    { pstep. econs. eauto. }
    i. destruct (Nat.eq_dec cid k); cycle 1.
    {
      rewrite !list_lookup_insert_ne in H7, H8; eauto.
      hexploit RELS; eauto. i. depdes H9; econs; eauto.
      { rewrite SRC0. des_ifs. }
      rewrite TGT0. des_ifs.
    }
    subst k.
    rewrite list_lookup_insert_ne in H8; eauto.
    rewrite list_lookup_insert in H7; eauto.
    rewrite list_lookup_insert in H8; eauto.
    inv H7. econs; try refl; grind; eauto.
    rewrite/yield_post -interp_hp_tau.
    f_equal. ired. do 5 f_equal.
    extensionalities. ired. do 3 f_equal.
    extensionalities. ired. f_equal.
    destruct H8. eauto.
  Qed.

End CANCEL.

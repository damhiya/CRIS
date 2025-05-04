Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_spawn `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
  (KTR: ∀ tid, paco3 (@elim_rel_def _ md _) bot3 l (ktrS tid) (ktrT tid))
  (CIH: ∀ rs rt srcs tgts cid st ps pt X (meta : X) Q itrS itrT l,
      ✓ rs → (Own rs ==∗ Own rt) →
      List.length srcs = List.length tgts →
      cid < List.length srcs → cid < List.length tgts → 
      srcs !! cid = Some (HModTr.trans itrS) →
      tgts !! cid = Some (HModTr.trans (cancel_term md meta Q itrT)) →
      (∀ vret ret, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝) →
      paco3 (@elim_rel_def _ md _) bot3 l itrS itrT →
      (∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
      → CANCEL_GOAL md r rs0 rt0 ps pt srcs tgts cid st rs rt)

  f fn args  
  (STB: sp_from md fn = Some f)
  (SRC : srcs !! cid = Some (HModTr.trans (x <- SpawnCancelE fn args;; ktrS x)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (x <- HoareSpawnE f fn args;; ktrT x))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. rewrite SRC. ired.
  
  zonly_l.
  rewrite !alist_find_map_snd.
  destruct (alist_find fn (SMod.fnsems md)) eqn: EQ; s; cycle 1.
  { unfold triggerUB. do 3 zstep_l. }
  destruct p as [[msk sc] [sp bd]]. ired.
  rewrite /sp_from /Sp.to_sp alist_find_map EQ in STB. inv STB.
  zshow.

  zstep_l.
  ziter_l. zstep_l.
  ziter_l. zstep_l.

  ziter_r. rewrite TGT. ired. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  
  zonly_r.
  rewrite !alist_find_map_snd EQ. ired.
  zshow.
  
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  erewrite (wrap_elimI_well_scoped _ fn); cycle 1.
  { s. rewrite /SModCancel.trans_ktree alist_find_map_snd EQ. ss. }
  
  erewrite (wrap_elimI_well_scoped _ fn); cycle 1.
  { s. rewrite /SModCancel.trans_ktree alist_find_map_snd EQ. ss. }

  unfold SModTr.trans_ktree, inline_hp_fun.
  unfold HModTr.sandbox_body, SModCancel.trans_ktree. s.

  ziter_r. s. zstep_r. exists x. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. eexists args. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  hexploit (Own_bupd_split rt); i; des; et.

  ziter_r. zstep_r. eexists (a1 ⋅ x1). zstep_r.

  assert (UPD': Own rs ==∗ Own (a1 ⋅ x1)).
  {
    iIntros "H". iPoseProof (UPD with "H") as ">H".
    iPoseProof (H with "H") as ">[H0 H1]".
    iPoseProof (H1 with "H1") as "H1".
    iModIntro. rewrite !Own_op. iFrame.
  }
  
  assert (VALID: ✓(a1 ⋅ x1) ∧ (Own (a1 ⋅ x1) ==∗ precond f x args x0 ∗ Own x1)).
  { split.
    - eapply Own_wand_valid with (a1 := rs); eauto.
    - iIntros "(H1 & H2)". iFrame.
      iPoseProof (H0 with "H1") as "H1".
      iApply "H1".
  }
  
  ziter_r. zstep_r. exists VALID. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  rewrite LEN.
  zprogress.
  gbase. eapply CIH; zsimpl_len; try eapply elim_rel_refl; et; zsimpl_len.
  { zsimpl_lookup. zlookup_insert. rewrite -LEN. zsimpl_len. ired. et. }
  { zsimpl_lookup. zlookup_insert.
    rewrite -/(HModTr.sandbox _ _ _).
    rewrite /cancel_term /inline_hp /HModTr.trans.
    rewrite SBRed.bind HIRed.iter_handle_bind.
    do 3 f_equal. extensionalities.
    rewrite SBRed.bind SBRed.core.
    do 2 f_equal. extensionalities.
    rewrite SBRed.bind SBRed.ag SBRed.ret. refl.
  }

  intros k t1 t2 NEQ LOOKUP1 LOOKUP2.
  rewrite list_lookup_insert_ne in LOOKUP2; eauto.
  destruct (Nat.eq_dec cid k).
  - subst k.
    revert LOOKUP1. zsimpl_lookup. zlookup_insert. i. depdes LOOKUP1.
    revert LOOKUP2. zsimpl_lookup. zlookup_insert. i. depdes LOOKUP2.
    econs; eauto.
    eapply KTR.
  - assert (L1 := LOOKUP1). eapply lookup_snoc_Some in L1. des; cycle 1.
    { subst. revert NEQ. zsimpl_len. }
    revert LOOKUP1. zsimpl_lookup. zlookup_insert_ne. i.
    assert (L2 := LOOKUP2). eapply lookup_snoc_Some in L2. des; cycle 1.
    { subst. revert NEQ. zsimpl_len. }
    revert LOOKUP2. zsimpl_lookup. zlookup_insert_ne. i.
    specialize (RELS k t1 t2 n LOOKUP1 LOOKUP2).
    inv RELS. econs; eauto.
Unshelve. all: eauto.
(*SLOW*)Qed.

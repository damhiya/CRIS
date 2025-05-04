Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_yield `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
  (KTR: ∀ x, paco3 (@elim_rel_def _ md _) bot3 l (ktrS x) (ktrT x))
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

  tid  
  (SRC : srcs !! cid = Some (HModTr.trans (x <- trigger (Yield tid);; ktrS x)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (x <- HoareYieldE tid;; ktrT x))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. rewrite SRC. ired. zstep_l.
  ziter_r. rewrite TGT. ired. zstep_r.

  destruct (Nat.eq_dec cid tid).
  {
    subst tid.
    gstep. econs; econs; eauto using smj_lt_mid_top.
    gbase. eapply CIH; zsimpl_len; et; zsimpl_len.
    { zlookup_insert. ired. et. }
    { zlookup_insert. ired. et. }
    
    intros k t1 t2 NEQ.
    do 2 zlookup_insert_ne. i. eauto.
  }

  destruct (classic (tid < List.length srcs)); cycle 1.
  {
    ziter_l. zlookup_insert_ne.
    rewrite lookup_ge_None_2; try nia.
    zstep_l. unfold triggerUB. zstep_l.
  }

  exploit lookup_lt_is_Some_2; eauto. i. inv x0.
  exploit (lookup_lt_is_Some_2 tgts tid); [nia|]. i. inv x1.
  assert (tid < base.length tgts) by nia.
  hexploit RELS; eauto. i.
  depdes H3. subst.

  gstep. econs; econs; eauto using smj_lt_mid_top.
  gbase. eapply CIH; zsimpl_len; et; zsimpl_len.
  { zlookup_insert_ne. ired. et. }
  { zlookup_insert_ne. ired. et. }

  i. destruct (Nat.eq_dec cid k); subst; cycle 1.
  { revert H4 H5. do 2 zlookup_insert_ne. i. eauto. }

  revert H4 H5. zlookup_insert. zlookup_insert. i. inv H5.
  econs; grind; eauto.
Unshelve. all: eauto.
(*SLOW*)Qed.

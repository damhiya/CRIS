Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelLib.

Import CancelTAC.

Lemma cancel_aux_yield `{Σ: GRA} md
  r ps pt srcs tgts
  cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT tid
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md cid k x y)
  (KTR: ∀ x, upaco3 (@elim_rel_def _ md _) bot3 l (ktrS x) (ktrT x))
  (SRC : srcs !! cid = Some (Ret ();;; HModTr.trans (x <- trigger (Yield tid);; ktrS x)))
  (TGT : tgts !! cid = Some (Ret ();;; HModTr.trans (cancel_term md meta Q (x <- HoareYieldE tid;; ktrT x))))
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
  hide_l. tau 1. reveal ITREE.
  hide_r. tau 1. reveal ITREE.
  destruct (Nat.eq_dec cid tid).
  {
    subst tid.
    hide_l. iterT 1. reveal ITREE.
    hide_r. iterT 1. reveal ITREE.
    prb. gbase. pclearbot.
    eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); eauto; grind.
    rewrite !list_lookup_insert_ne in H0, H1; eauto.
  }
  destruct (classic (tid < List.length srcs)); cycle 1.
  {
    hide_r. eapply Nat.le_ngt, lookup_ge_None_2 in H.
    _iter. rewrite list_lookup_insert_ne; [|et]. rewrite H.
    s. unfold triggerUB. ired. _coreA.
  }
  exploit lookup_lt_is_Some_2; eauto. i. inv x0.
  exploit (lookup_lt_is_Some_2 tgts tid); [nia|]. i. inv x1.
  assert (tid < base.length tgts) by nia.
  hexploit RELS; eauto. i.
  depdes H3.
  (* move to another thread *)
  destruct (Nat.eq_dec tid cid); try nia.
  subst.
  prb. gbase. pclearbot.
  eapply CIH with (Q:=Q0); try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind).
  { eauto. }
  { eauto. }
  { rewrite list_lookup_insert_ne; eauto.
    rewrite H0. grind. rewrite -HRed.tau. refl.
  }
  { rewrite list_lookup_insert_ne; eauto.
    rewrite H1 /cancel_term. instantiate (2:= tau;; itrT).
    ired. rewrite HRed.tau.  eauto.
  }
  { eauto. }
  { pstep. econs. eauto. }
  i. destruct (Nat.eq_dec cid k); cycle 1.
  {
    rewrite !list_lookup_insert_ne in H4, H5; eauto.
    hexploit RELS; eauto. i. depdes H6; econs; eauto.
    { rewrite SRC0. des_ifs. }
    rewrite TGT0. des_ifs.
  }
  subst k.
  rewrite list_lookup_insert in H4; eauto.
  rewrite list_lookup_insert in H5; eauto.
  inv H4.
  econs; grind; eauto.
(*SLOW*)Qed.

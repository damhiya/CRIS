Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_core `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q R ktrS ktrT
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

  (e: coreE R)
  (SRC : srcs !! cid = Some (HModTr.trans (x <- trigger e;; ktrS x)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (x <- trigger e;; ktrT x))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. ziter_r. rewrite SRC TGT.
  depdes e.
  + zstep_r. zstep_r.
    zstep_l. exists x. zstep_l.
    gstep. econs; econs; eauto using smj_lt_mid_top.
    gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
    intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
  + zstep_l. zstep_l.
    zstep_r. exists x. zstep_r.
    gstep. econs; econs; eauto using smj_lt_mid_top.
    gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
    intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
  + zstep. zstep_l. zstep_r. subst.
    gstep. econs; econs; eauto using smj_lt_mid_top.
    gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
    intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
Unshelve. all: eauto.
(*SLOW*)Qed.

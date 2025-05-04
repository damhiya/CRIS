Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel CancelLib.
Require Import SimGTactics.

Lemma cancel_aux_tail `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) l X X0 (meta: X) (m: X0) Q Q0 ktrS ktrT
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
  (KTR: ∀ vret, paco3 (@elim_rel_def _ md _) bot3 l (ktrS vret) (ktrT vret))
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

  vret  
  (SRC : srcs !! cid = Some (HModTr.trans (tau;; tau;; ktrS vret)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (x <- hmod_elim_tail X0 Q0 (m, m) vret;; ktrT x))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. rewrite SRC. ired. zstep_l.
  ziter_l. zstep_l.
  
  ziter_r. rewrite TGT. ired. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. exists vret. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  hexploit (Own_bupd_split rt); i; des; eauto.
  assert (VALID: ✓ (a1 ⋅ x0) ∧ (Own (a1 ⋅ x0) ==∗ Q0 m vret x ∗ Own x0)).
  { split.
    - eapply Own_wand_valid with (a1 := rt); eauto.
      iIntros "RT". iMod (H with "RT") as "[A X]". iModIntro.
      iSplitL "A"; eauto. iApply H1; eauto.
    - iIntros "[A X]". iFrame. iApply H0. eauto.
  }
  
  ziter_r. zstep_r. exists (a1 ⋅ x0). zstep_r.
  ziter_r. zstep_r. exists VALID. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  zprogress.
  gbase. eapply CIH; zsimpl_len; try zlookup_insert; ired; et.
  { iIntros "RS". iMod (UPD with "RS") as "RS". iMod (H with "RS") as "[A1 A2]".
    iSplitL "A1"; eauto. iApply H1. eauto.
  }
  { intros k t1 t2 NEQ. do 2 zlookup_insert_ne. i. eauto. }
Unshelve. all: eauto.
(*SLOW*)Qed.

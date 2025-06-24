Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_Guarantee `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) l X (meta: X) Q ktrS ktrT
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
  (KTR: paco3 (@elim_rel_def _ md _) bot3 l (ktrS ()) (ktrT ()))
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

  P
  (SRC : srcs !! cid = Some (HModTr.trans (x <- trigger (Guarantee P);; ktrS x)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (a <- trigger (Guarantee P);; ktrT a))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. ziter_r. rewrite SRC TGT. zstep_l. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.

  des.
  assert (VALID: ✓ x ∧ (Own rs ==∗ P ∗ Own x)).
  { split; eauto. iIntros "H". iMod (UPD with "H") as "H". iApply x1; eauto. }
  ziter_l. zstep_l. exists x. zstep_l.
  ziter_l. zstep_l. exists VALID. zstep_l.
  ziter_l. zstep_l.
  ziter_l. zstep_l.

  zprogress.
  gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
  intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
Unshelve. all: eauto.
(*SLOW*)Admitted.

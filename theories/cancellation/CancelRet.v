Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_ret `{Σ: GRA} md
  r ps pt srcs tgts cid st (rs rt rs0 rt0: Σ) X (meta: X) Q
  (WFS: ✓ rs) (WFT: ✓ rt)
  (UPD: Own rs ==∗ Own rt)
  (LENS: cid < List.length srcs)
  (LENT: cid < List.length tgts)
  (LEN: List.length srcs = Datatypes.length tgts)
  (RET: ∀ vret ret : Any.t, cid = 0 → Q meta vret ret ⊢ ⌜vret = ret⌝)
  (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md k x y)
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

  v
  (SRC : srcs !! cid = Some (HModTr.trans (Ret v)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (Ret v))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. rewrite SRC.
  zonly_l.
  des_ifs; cycle 1.
  { unfold triggerUB. do 2 zstep_l. }
  zshow.
  zstep_l.
  ziter_r. rewrite TGT. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  zstep.

  hexploit (Own_bupd_split rt); i; des; eauto.
  depdes Heq. specialize (RET r0 x eq_refl).
  eapply Own_pure_soundness with (a := a1).
  + eapply Own_bupd_valid in H; eauto.
    eapply cmra_valid_op_l; eauto.
  + etrans; eauto.
Unshelve. all: eauto.
(*SLOW*)Qed.

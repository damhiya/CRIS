Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import SimGlobal SimGTactics.
Require Import SModCancel HModInline ElimRel CancelLib.

Lemma cancel_aux_Assume `{Σ: GRA} md
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
  (SRC : srcs !! cid = Some (HModTr.trans (x <- trigger (Assume P);; ktrS x)))
  (TGT : tgts !! cid = Some (HModTr.trans (cancel_term md meta Q (a <- trigger (Assume P);; ktrT a))))
  :
  CANCEL_GOAL md (gpaco7 _simg (cpn7 _simg) bot7 r) rs0 rt0 ps pt srcs tgts cid st rs rt.
Proof.
  r.
  ziter_l. ziter_r. rewrite SRC TGT. zstep_l. zstep_r.
  ziter_l. zstep_l. zstep_l.
  ziter_l. zstep_l.
  ziter_l. zstep_l. zstep_l.
  ziter_l. zstep_l.

  des. eapply bi.wand_entails, Own_bupd_split in x1; et. des.
  assert (UPD': Own (a1 ⋅ a2) ==∗ Own (a1 ⋅ rt)).
  { iIntros "[A1 A2]". iSplitL "A1"; eauto.
    iApply UPD. iApply x3. eauto.
  }
  assert (VALID: ✓ (a1 ⋅ rt) ∧ (Own (a1 ⋅ rt) ==∗ P ∗ Own rt)). 
  { split.
    - eapply bi.wand_entails in UPD'.
      eapply Own_wand_valid; eauto.
      eapply Own_wand_valid, x0.
      iIntros "X"; iMod (x1 with "X") as "[A1 A2]". iSplitL "A1"; eauto.
    - iIntros "[H0 H1]". iFrame. iApply x2. eauto.
  }
  
  ziter_r. zstep_r. exists (a1 ⋅ rt). zstep_r.
  ziter_r. zstep_r. exists VALID. zstep_r.
  ziter_r. zstep_r.
  ziter_r. zstep_r.
  
  gstep. econs; econs; eauto using smj_lt_mid_top.
  gbase. eapply CIH; zsimpl_len; try zlookup_insert; et.
  { iIntros "X"; iMod (x1 with "X") as "[A1 A2]". 
    iApply UPD'. iSplitL "A1"; eauto. }
  intros ? ? ? ?. do 2 zlookup_insert_ne. eauto.
Unshelve. all: eauto.
(*SLOW*)Qed.

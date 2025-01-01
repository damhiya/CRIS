Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelLib.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable md: SMod.t.

  Import CancelTAC.

  Lemma cancel_aux_tail
    ginv sk (SKINCL: incl (SMod.sk md) sk) (SKWF: Sk.wf sk) r ps pt srcs tgts
    cid st (rs rt rs0 rt0: Σ) l tid X X0 (meta: X) (m: X0) Q Q0 ktrS ktrT vret
    (WFS: ✓ rs) (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (LENS: cid < List.length srcs)
    (LENT: cid < List.length tgts)
    (LEN: List.length srcs = Datatypes.length tgts)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (RELS: ∀ k x y, cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel md ginv sk cid k x y)
    (KTR: ∀ vret, upaco3 (@elim_rel_def _ md ginv sk _) bot3 l (ktrS vret) (ktrT vret))
    (SRC : srcs !! cid = Some (Ret ();;; interp_hp (tau;; tau;; tau;; ktrS vret)))
    (TGT : tgts !! cid = Some (Ret ();;; interp_hp (cancel_term md ginv sk cid meta Q (x <- hmod_elim_tail X0 Q0 (tid, m, tid, m) vret;; (tau;; ktrT x)))))
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
    hide_r. tau 2. iterT 2.
    reveal ITREE. hide_l. _coreA.
    iterT 2. iterL. _supd.
    iterL. _coreA. ls.
    iterL. _coreA. ls.
    iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 4.
    iterL. _coreE vret.
    iterT 2.
    hexploit (Own_bupd_split rt); eauto.
    i. des.
    iterL. _supd.
    iterL. _coreE (a1 ⋅ x0). ls.
    assert (VALID: ✓ (a1 ⋅ x0)).
    { eapply Own_wand_valid with (a1 := rt); eauto.
      iIntros "RT". iMod (H with "RT") as "[A X]". iModIntro.
      iSplitL "A"; eauto. iApply H1; eauto. }
    iterL. _coreE VALID. ls.
    assert (UPD': (Own (a1 ⋅ x0) -∗ Q0 tid m vret x ∗ Own x0)).
    { iIntros "[A X]". iFrame. iApply H0. eauto. }
    iterL. _coreE UPD'. ls.
    iterL. _supd. iterL. _supd.
    iterT 3.
    reveal ITREE.
    done_by_CIH CIH LKX LKY.
    { iIntros "RS". iMod (UPD with "RS") as "RS". iMod (H with "RS") as "[A1 A2]".
      iSplitL "A1"; eauto. iApply H1. eauto.
    }
    i. rewrite !list_lookup_insert_ne in H3, H4; eauto.
  Qed.
  
End CANCEL.

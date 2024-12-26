Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import SimGlobal.
Require Import SMod2HModAux HModInline ElimRel StRed CancelDef.

(* Yield *)

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.
  Variable md: SMod.t.
  Notation iProp := (iProp Σ).

  Let sk: Sk.t := SMod.sk md.
  Let ms (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0) := 
    SMod.modsem md sk0.
  Let sbtb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspecbody) := 
    (ms sk0 SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb sk0 SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Let md_src: HMod.t := SModAux.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

  Import CancelTAC.



  Lemma cancel_main_yield
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q (cid tid: nat) st ps pt l
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WFS: ✓ rs)
    (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ (x: ()), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS x) (ktrT x))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel ginv stb md sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post ginv sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel ginv stb md sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  : 
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
              (tid, <[cid:=tau;; interp_hp (ktrS ())]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger sGet;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : (),
                        Ret
                          (inl
                             (vret <-
                              ITree.subst (λ x0 : (), ktrT x0)
                                (ITree.subst (λ _ : (), tau;; trigger (Yield tid);;; (tau;; my_tid <- trigger Tid;; (tau;; trigger (Assume (ginv sk0 my_tid))))) (Ret x));;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))))
                     (ITree.subst (λ mr : Σ, mr' <- trigger (Choose Σ);; guarantee (Own mr ==∗ ginv sk0 tid ∗ Own mr');;; mput_res mr')
                        (ITree.subst (λ st0 : Any.t, x_0 <- (Any.split st0) ?;; (let (_, mr) := x_0 in (mr ↓) ?)) (Ret x_)));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_r. tau 1.
    reveal ITREE. hide_l.
    _supd. iterL. _coreA. ls. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. tau 1. ls.  
    hexploit (Own_bupd_split rt); eauto. i. des.
    assert (UPD': Own rs ==∗ Own (a1 ⋅ x)). 
    {
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H with "H") as ">[H0 H1]".
      iModIntro. iSplitL "H0"; eauto.
      iApply H1; eauto.
    }
    assert (✓ (a1 ⋅ x)). 
    { eapply Own_wand_valid with (a1 := rs); eauto. } 
    destruct (Nat.eq_dec cid tid).
    {
      (* yield to itself *)
      subst tid.
      iterT 2. iterL. tau 1. iterT 2.
      iterL. _coreE a1. iterL. _supd.
      iterL. _coreE H2. ls.
      iterL. _coreE H0. ls.
      iterL. _supd. iterL. _supd. 
      iterT 1.
      reveal ITREE. hide_r. iterT 1. reveal ITREE.
      prb. gbase. pclearbot. 
      eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); eauto; grind.
      rewrite !list_lookup_insert_ne in H4, H5; eauto.
    }
    destruct (classic (tid < base.length srcs)); cycle 1.
    {
      reveal ITREE. 
      hide_r. eapply Nat.le_ngt, lookup_ge_None_2 in H3.
      _iter. rewrite list_lookup_insert_ne; [|et]. rewrite H3.
      s. unfold triggerUB. ired. _coreA.
    } 
    exploit lookup_lt_is_Some_2; eauto. i. inv x2.
    exploit (lookup_lt_is_Some_2 tgts tid); [nia|]. i. inv x3.
    assert (tid < base.length tgts) by nia.
    hexploit RELS; eauto. i. 
    depdes H7.
    (* move to another thread *)
    destruct (Nat.eq_dec tid cid); try nia.
    subst. _iter.  
    replace (<[cid:=tau;; interp_hp
    (tau;; ' r0 : nat <- trigger Tid;;
           ' x1 : () <- (tau;; trigger (Assume (ginv sk0 r0)));;
           ' x2 : Any.t <- ktrT x1;;
           inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
             (' ret : Any.t <- trigger (Choose Any.t);; trigger (Guarantee (Q  cid meta x2 ret));;; Ret ret))]> tgts !! tid)
    with (tgts !! tid) by (rewrite list_lookup_insert_ne; eauto).
    rewrite H5. ired. tau 2.
    iterT 1. iterL. tau 1. ls. iterT 2. 
    iterL. _coreE a1. ls. iterL. _supd.
    iterL. _coreE H2. ls. iterL. _coreE H0. ls.
    iterL. _supd. iterL. _supd. 
    reveal ITREE. prb. gbase. pclearbot. 
    eapply CIH with (Q:=Q0); try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); swap 1 6.
    { 
      instantiate (1:= tau;; itrT). instantiate (1:= tau;; itrS).
      pstep. econs. eauto.
    }
    all: eauto.
    {
      des_ifs. grind. rewrite list_lookup_insert_ne; eauto.
      rewrite H4 interp_hp_tau. grind. 
    }
    { rewrite length_insert. nia. }
    { des_ifs. rewrite -interp_hp_tau. grind. }
    i. destruct (Nat.eq_dec cid k); cycle 1.
    {
      rewrite !list_lookup_insert_ne in H8, H9; eauto.
      hexploit RELS; eauto. i. depdes H10; econs; eauto.
      { rewrite SRC. des_ifs. }
      rewrite TGT. des_ifs.
    }
    subst k.
    rewrite list_lookup_insert_ne in H9; eauto.
    rewrite list_lookup_insert in H8; eauto.
    rewrite list_lookup_insert in H9; eauto.
    inv H8. econs; try refl; grind; eauto.
    rewrite/yield_post -interp_hp_tau.
    f_equal. ired. do 5 f_equal. 
    extensionalities. ired. do 3 f_equal.
    extensionalities. ired. f_equal.
    destruct H9. eauto.
  Qed.

End CANCEL.

(* 41 sec *)

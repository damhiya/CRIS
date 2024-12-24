Require Import Coqlib.
Require Import Behavior.
Require Import AList.
Require Import SMod2HMod SMod2HModAux.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim ISim HPSim.
Require Import CtxRefine CtxRefineFacts MainAdequacy ClosedAdequacy.
Require Import SimGlobal SimGlobalFacts.
Require Import SMod HMod Mod Events.
Require Import HModInline ElimRel.
Require Import Mod2ITree StRed CancelDef.

(* pre/post conditions of function calls *)

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

  Lemma cancel_main_head
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X X0 (meta: X) (rs0 rt0 rs rt: Σ) P Q cid st ps pt l varg
    src srcs tgts ktrS ktrT
    (SRC: src = ktrS varg)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WFS: ✓ rs)
    (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀(tid: nat) (m: X0) (varg: Any.t), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 ((tid, existT X0 m) :: l) (ktrS varg) (ktrT (tid, m, tid, m, varg)))
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
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=interp_hp src]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0)))
    (cid, <[cid:=tau;; interp_hp (tau;; x_ <- trigger (Choose X0);; x_0 <-
                                     (tau;; arg <- trigger (Choose Any.t);;
                                            (tau;; trigger (Guarantee (P cid x_ varg arg));;;
                                                   (tau;; tau;; my_tid' <- trigger Tid;;
                                                                (tau;; x' <- trigger (Take X0);;
                                                                       (tau;; varg' <- trigger (Take Any.t);;
                                                                              (tau;; trigger (Assume (P my_tid' x' varg' arg));;; (tau;; Ret (cid, x_, my_tid', x', varg'))))))));;
                  x_1 <- ktrT x_0;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta x_1 ret));;; Ret ret))]> tgts)) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_r. tau 2.
    reveal ITREE. hide_l. tau 1.
    iterT 2. iterL. _coreA. ls.
    iterT 2. iterL. _coreA. ls.
    iterT 2. iterL. _supd. 
    iterL. _coreA. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 3. iterL. ls. tau 1.
    iterT 2. iterL. _coreE x. ls.
    iterT 2. iterL. _coreE varg. ls.
    iterT 2.
    hexploit (Own_bupd_split rt); eauto.
    i. des.
    iterL. _coreE a1. ls.
    iterL. _supd.
    assert (UPD': Own rs ==∗ Own (a1 ⋅ x1)).
    {  
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H with "H") as ">[H0 H1]".
      iPoseProof (H1 with "H1") as "H1".
      iModIntro. rewrite Own_op. iFrame.
    }
    assert (✓ (a1 ⋅ x1)). 
    { eapply Own_wand_valid with (a1 := rs); eauto. } 
    iterL. _coreE H2. ls.
    iterL. _coreE H0. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. 
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH with (l:= _ :: l); eauto; try (rewrite !length_insert; nia); 
    try (eapply KTR); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H4, H5; eauto.
  Qed.

  Lemma cancel_main_tail
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X X0 (meta: X) (m: X0) (rs0 rt0 rs rt: Σ) Q Q0 (cid tid: nat) st ps pt l vret
    src srcs tgts ktrS ktrT
    (SRC: src = ktrS vret)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WFS: ✓ rs)
    (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ vret : Any.t, upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS vret) (ktrT vret))
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
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=interp_hp (tau;; tau;; src)]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (x_ <- trigger (Choose Any.t);;
    x_0 <- Ret (inl
      (cid, <[cid:=lr <- ITree.subst (λ x : Any.t, Ret (inl
              (vret0 <- ITree.subst (λ x0 : Any.t, tau;; ktrT x0) 
                        (ITree.subst (λ ret : Any.t, tau;; trigger (Guarantee (Q0 tid m vret ret));;;
                          (tau;; tau;; tau;; vret0 <- trigger (Take Any.t);; (tau;; trigger (Assume (Q0 tid m vret0 ret));;; (tau;; Ret vret0)))) (Ret x));;
                          inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                          (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret0 ret));;; Ret ret)))) (Ret x_);;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_r. tau 2. iterT 2. 
    reveal ITREE. hide_l. _coreA.
    iterT 2. iterL. _supd.
    iterL. _coreA. ls.
    iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 4.
    iterL. _coreE vret.
    iterT 2.
    hexploit (Own_bupd_split rt); eauto.
    i. des.
    iterL. _coreE a1. ls.
    iterL. _supd.
    assert (UPD': Own rs ==∗ Own (a1 ⋅ x0)). 
    {  
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H with "H") as ">[H0 H1]".
      iPoseProof (H1 with "H1") as "H1".
      iModIntro. rewrite Own_op. iFrame.
    }
    assert (✓ (a1 ⋅ x0)). 
    { eapply Own_wand_valid with (a1 := rs); eauto. }
    iterL. _coreE H2. ls.
    iterL. _coreE H0. ls.
    iterL. _supd. iterL. _supd.
    iterT 3. 
    reveal ITREE. prb. gbase. pclearbot. 
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H4, H5; eauto.
  Qed.


End CANCEL.
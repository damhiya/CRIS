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
Require Import HModInline Cancel ElimRel.
Require Import Mod2ITree StRed.

Set Implicit Arguments.


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
    (ms SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Let md_src: HMod.t := SModAux.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

  (* Let md_src_inline: HMod.t := HModAux.inline md_src.  *)
  (* Let md_tgt_inline: HMod.t := HModAux.inline md_tgt. *)
  
  (* Let ms_src: HModSem.t := HMod.modsem md_src_inline (md_src_inline.(HMod.sk)). *)
  (* Let ms_tgt: HModSem.t := HMod.modsem md_tgt_inline (md_tgt_inline.(HMod.sk)). *)

  Ltac hide_l := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ ?it _] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ ?it _] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac hide_r := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ _ ?it] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ _ ?it] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac reveal ITR := unfold ITR; clear ITR.

  Ltac st := prep; guclo simg_indC_spec; econs; try instantiate (1:= smj_top).
  Ltac prb := gstep; econs; econs; try instantiate (1:= smj_bot); try instantiate (1:= smj_bot); eauto.  
  Ltac prm := gstep; econs; econs; try instantiate (1:= smj_mid); try instantiate (1:= smj_mid); eauto.  
  Ltac _iter := rewrite unfold_iter_eq; ired.
  Ltac _iterI := rewrite [ITree.iter (handle_callE _) _]unfold_iter_eq; ired.
  Ltac _tau := rewrite !StRed.tau.
  Ltac _core := rewrite StRed.bind StRed.core; prep.
  Ltac _coreH := rewrite HModSB.transl_bind HModSB.transl_core interp_hp_bind interp_hp_core; prep.
  Ltac _asm := rewrite HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Assume /mget_res; prep.
  Ltac _grt := rewrite HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Guarantee /mget_res; prep.
  Ltac _sget := rewrite/sGet !StRed.bind [interp_stateE Any.t _ _]StRed.state/handle_stateE. 
  (* Ltac __supd := rewrite/sPut /sGet !StRed.bind [interp_stateE _ _ _]StRed.state/handle_stateE.  *)
  Ltac ls := rewrite !list_insert_insert.
  Ltac __supd := rewrite !StRed.bind StRed.state. 
  Ltac _supd := __supd; grind; try ls; _tau; st; st; try (rewrite Any.pair_split; ired); try (rewrite Any.upcast_downcast; ired).
  Ltac _ub := rewrite/triggerUB !StRed.bind StRed.core; st; i; ss.
  Ltac iterL := _iter; rewrite list_lookup_insert;[|try rewrite !length_insert; auto]; ired.

  Tactic Notation "tau" integer(n) := _tau; do n st.
  Tactic Notation "iterT" integer(n) := do n (iterL; ls; tau 2).
  Ltac _coreA := _core; st; i; st; grind; _tau; st.
  Ltac _coreE x := _core; st; exists x; st; grind; _tau; st.

  Inductive Forall2i X Y (R: nat -> X -> Y -> Prop): nat -> list X -> list Y -> Prop :=
  | Forall2i_nil i: Forall2i R i [] []
  | Forall2i_cons
      i x y xs ys
      (REL: R i x y)
      (TAIL: Forall2i R (S i) xs ys):
      Forall2i R i (x :: xs) (y :: ys).

  Lemma Forall2i_len 
    X Y (R: nat -> X -> Y -> Prop) i xs ys
    (REL: Forall2i R i xs ys)
  :
    List.length xs = List.length ys.
  Proof.
    induction REL; s; eauto.
  Qed.

  Lemma Forall2i_nth
    X Y (R: nat -> X -> Y -> Prop) (i k: nat) 
    (xs: list X) (ys: list Y)
    (REL: Forall2i R i xs ys)
    (NTH: k < List.length xs)
  :
    ∃ x y,
    xs !! k = Some x /\
    ys !! k = Some y /\
    R (i + k) x y.
  Proof.
    revert k NTH.
    induction REL; s; i; eauto.
    - nia.
    - destruct k; s.
      + replace (i + 0) with i by nia. eauto 7.
      + replace (i + S k) with (S i + k) by nia.
      eapply IHREL; nia.
  Qed.

  Lemma Forall2i_forall
      X Y (R: nat -> X -> Y -> Prop) i xs ys
      (REL: Forall2i R i xs ys)
    :
    ∀k x y (LKX: xs !! k = Some x) (LKY: ys !! k = Some y), R (i + k) x y.
  Proof.
    i. hexploit (lookup_lt_Some _ _ _ LKX).
    i. hexploit Forall2i_nth; eauto.
    i. des. rewrite LKX in H0. rewrite LKY in H1.
    inv H0. eauto.
  Qed.

  Definition yield_post sk0: itree hmodE _ :=
      tau;; tau;; r <- trigger Tid;; x <- (tau;; trigger (Assume (ginv sk0 r)));; Ret ().

  Variant thread_rel sk0 (cid tid: nat) src tgt : Prop :=
  | thread_rel_body X (meta: X) (Q: nat -> X -> Any.t -> Any.t -> iProp) l itrS itrT
      (RET: ∀vret ret, 
            tid = 0 -> Q tid meta vret ret ⊢ ⌜vret = ret⌝)
      (REL: @elim_rel _ ginv stb sk0 _ l itrS itrT)
      (SRC: src = 
          ((if Nat.eq_dec tid cid then Ret tt else tau;; Ret tt);;; interp_hp itrS))
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else yield_post sk0);;;
              vret <- itrT;; 
              (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                (ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q tid meta vret ret));;;
                  Ret ret))))) 
  .

  Lemma valid_solve (a b c: Σ) :
    ✓ a -> a ≡  b ⋅ c -> ✓ b.
  Proof.
    i. eapply cmra_valid_op_l. setoid_rewrite <- H0. eauto.
  Qed.

  (* Lemma valid_solve_eq (a b : Σ) :
    ✓ a -> a ≡ b -> ✓ b.
  Proof.
    i. rewrite <- H0. eauto.
  Qed. *)

  Lemma valid_extends (r a b: Σ):
    b ≼ a -> ✓(r ⋅ a) -> ✓ (r ⋅ b).
  Proof.
    i. apply cmra_mono_l with (z:=r) in H.
    eapply cmra_valid_included; eauto.
  Qed.

  Lemma Own_bupd_valid (r a b: Σ):
    (Own r ⊢|==> Own a ∗ Own b) -> ✓ r -> ✓ (a ⋅ b).
  Proof.
    i. eapply Own_wand_valid with (a1 := r); eauto.
    iIntros "H". iApply Own_op. iStopProof. eauto.
  Qed.

  Lemma list_lookup_length {X} (x: X) l:
    (l ++ [x]) !! (base.length l) = Some x.
  Proof.
    eapply lookup_snoc_Some; right; eauto.
  Qed. 

  Lemma cancel_main_ret
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    r X (meta: X) (rs0 rt0 rs rt: Σ) v  Q cid st ps pt
    (srcs tgts: list (itree modE Any.t))
    (WFT: ✓ rt)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- (if Nat.eq_dec cid 0 then Ret (inr v) else triggerUB);;
      match x_ with
      | inl l => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Choose Any.t)%sum;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : Any.t,
                        Ret
                          (inl
                             (ITree.subst
                                (λ lr : itree hmodE Any.t + Any.t,
                                   match lr with
                                   | inl l => tau;; ITree.iter (handle_callE (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))) l
                                   | inr r0 => Ret r0
                                   end) (ITree.subst (λ v0 : Any.t, Ret (inl (ITree.subst (λ ret : Any.t, trigger (Guarantee (Q cid meta v ret));;; Ret ret) (Ret v0)))) (Ret x)))))
                     (Ret x_);; match lr with
                                | inl l => tau;; interp_hp l
                                | inr r0 => Ret r0
                                end]> tgts));;
      match x_0 with
      | inl l => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2)
  .
  Proof. 
    hide_r. des_ifs; cycle 1.
    { unfold triggerUB. ired. _coreA. }
    ired. reveal ITREE.
    _coreA. iterT 2. 
    iterL. _supd. iterL. _coreA. ls.
    iterL. _coreA. ls. iterL. _supd. iterL. _supd.
    iterT 2. iterL. rewrite !StRed.ret. ired. st.
    hexploit Own_bupd_split; eauto. i. des.
    specialize (RET v x ltac:(refl)).
    eapply Own_pure_soundness with (x := a1).
    {
      eapply Own_bupd_valid in WFT; eauto.
      eapply cmra_valid_op_l; eauto.
    }
    etrans; eauto.
  Qed.

  Lemma cancel_main_tau
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l
    srcs tgts itrS itrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (ITR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l itrS itrT)
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=interp_hp itrS]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0)))
    (cid, <[cid:=interp_hp (vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))]> tgts)) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    tau 4. prb. gbase. pclearbot. 
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.
  
  Lemma cancel_main_core
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l R (e:coreE R)
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ v : R, upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS v) (ktrT v))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t 
    (x_ <- trigger e;;
      x_0 <- Ret (inl (cid, <[cid:=lr <- ITree.subst (λ x : R, Ret (inl (ITree.subst ktrS (Ret x)))) (Ret x_);; 
                              match lr with
                              | inl l0 => tau;; interp_hp l0
                              | inr r0 => Ret r0
                              end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t
    (x_ <- trigger e;;
      x_0 <- Ret (inl (cid, <[cid:=lr <- ITree.subst (λ x : R, Ret (inl (vret <- ITree.subst (λ a : R, ktrT a) (Ret x);;
                                                                                  inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                                                                  (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret)))) (Ret x_);;
                              match lr with
                              | inl l0 => tau;; interp_hp l0
                              | inr r0 => Ret r0
                              end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
  depdes e.
  - hide_l. _coreA. iterT 1.
    reveal ITREE. hide_r. _coreE x. iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  - hide_r. _coreA. iterT 1.
    reveal ITREE. hide_l. _coreE x. iterT 1. 
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  - hide_l. _core. reveal ITREE. hide_r. _core. reveal ITREE. st. instantiate (1:= smj_top). i. subst. 
    hide_l. st. ired. tau 1. iterT 1.
    reveal ITREE. hide_r. st. ired. tau 1. iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

  Lemma cancel_main_pg
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l R (e:pgE R)
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ v : R, upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS v) (ktrT v))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t
    (x_ <- match _observe 
                          (match observe (ITree.map (λ x : R, inl (ITree.subst ktrS (Ret x))) (handle_pgE e)) with
                          | RetF r0 => 
                            match r0 with
                            | inl l0 => tau;; interp_hp l0
                            | inr r1 => Ret r1
                            end
                          | TauF t => tau;; lr <- t;; 
                            match lr with
                            | inl l0 => tau;; interp_hp l0
                            | inr r0 => Ret r0
                            end
                          | @VisF _ _ _ X0 e1 h => Vis e1 (λ x : X0, lr <- h x;; 
                            match lr with
                            | inl l0 => tau;; interp_hp l0
                            | inr r0 => Ret r0
                            end)
                          end) 
           with
          | RetF rv => if Nat.eq_dec cid 0 then Ret (inr rv) else triggerUB
          | TauF itr' => tau;; Ret (inl (cid, <[cid:=itr']> srcs))
          | @VisF _ _ _ X0 e1 k =>
            match e1 with
            | (e2|)%sum =>
                match e2 in (schE T) return ((T → itree modE Any.t) → itree (stateE +' coreE) (nat * list (itree modE Any.t) + Any.t)) with
                | Spawn fn arg =>
                    λ k0 : nat → itree modE Any.t,
                      Ret
                        (inl
                           (cid,
                            <[cid:=k0 (base.length srcs)]> srcs ++
                            [sem <-
                             (alist_find fn
                                (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                                   (List.map (map_snd (wrap_elimI (SModSemAux.to_hmod (SMod.modsem md sk0))))
                                      (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_aux ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; 
                             sem arg]))
                | Yield tid' => λ k0 : () → itree modE Any.t, Ret (inl (tid', <[cid:=k0 ()]> srcs))
                | Tid => λ k0 : nat → itree modE Any.t, Ret (inl (cid, <[cid:=k0 cid]> srcs))
                end k
            | (|s)%sum =>
                match s with
                | (e2|)%sum => Ret (inl (cid, <[cid:=x <- ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0) e2;; (tau;; k x)]> srcs))
                | (|e2)%sum => v <- trigger e2;; Ret (inl (cid, <[cid:=k v]> srcs))
                end
            end
          end;;
          match x_ with
          | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
          | inr r0 => Ret r0
          end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <-
      match
        _observe
          match
            observe
              (ITree.map
                 (λ x : R,
                    inl
                      (vret <- ITree.subst (λ a : R, ktrT a) (Ret x);;
                       inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                         (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))) (handle_pgE e))
          with
          | RetF r0 => match r0 with
                       | inl l0 => tau;; interp_hp l0
                       | inr r1 => Ret r1
                       end
          | TauF t => tau;; lr <- t;; match lr with
                                      | inl l0 => tau;; interp_hp l0
                                      | inr r0 => Ret r0
                                      end
          | @VisF _ _ _ X0 e1 h => Vis e1 (λ x : X0, lr <- h x;; match lr with
                                                                 | inl l0 => tau;; interp_hp l0
                                                                 | inr r0 => Ret r0
                                                                 end)
          end
      with
      | RetF rv => if Nat.eq_dec cid 0 then Ret (inr rv) else triggerUB
      | TauF itr' => tau;; Ret (inl (cid, <[cid:=itr']> tgts))
      | @VisF _ _ _ X0 e1 k =>
          match e1 with
          | (e2|)%sum =>
              match e2 in (schE T) return ((T → itree modE Any.t) → itree (stateE +' coreE) (nat * list (itree modE Any.t) + Any.t)) with
              | Spawn fn arg =>
                  λ k0 : nat → itree modE Any.t,
                    Ret
                      (inl
                         (cid,
                          <[cid:=k0 (base.length tgts)]> tgts ++
                          [sem <-
                           (alist_find fn
                              (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                                 (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
                                    (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2))) (SModSem.fnsems (SMod.modsem md sk0))))))
                           !;; sem arg]))
              | Yield tid' => λ k0 : () → itree modE Any.t, Ret (inl (tid', <[cid:=k0 ()]> tgts))
              | Tid => λ k0 : nat → itree modE Any.t, Ret (inl (cid, <[cid:=k0 cid]> tgts))
              end k
          | (|s)%sum =>
              match s with
              | (e2|)%sum =>
                  Ret
                    (inl
                       (cid, <[cid:=x <- ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0) e2;; (tau;; k x)]> tgts))
              | (|e2)%sum => v <- trigger e2;; Ret (inl (cid, <[cid:=k v]> tgts))
              end
          end
      end;;
      match x_ with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    depdes e.
    - hide_l. grind. _supd. iterL. _supd. iterT 1.
      reveal ITREE. hide_r. 
      grind. _supd. iterL. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
    - hide_l. grind. _supd. iterT 1.
      reveal ITREE. hide_r.
      grind. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

  Lemma cancel_main_asm
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l P
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS ()) (ktrT ()))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Take Σ);;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst (λ x : (), Ret (inl (ITree.subst ktrS (Ret x))))
                     (ITree.subst (λ r0 : Σ, mr <- mget_res;; assume (✓ (r0 ⋅ mr));;; assume (Own r0 ⊢ P);;; mput_res (r0 ⋅ mr)) (Ret x_));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Take Σ);;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : (),
                        Ret
                          (inl
                             (vret <- ITree.subst (λ a : (), ktrT a) (Ret x);;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))))
                     (ITree.subst (λ r0 : Σ, mr <- mget_res;; assume (✓ (r0 ⋅ mr));;; assume (Own r0 ⊢ P);;; mput_res (r0 ⋅ mr)) (Ret x_));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_r. _coreA. iterL. _supd. 
    iterL. _coreA. iterL. _coreA.
    iterL. _supd. iterL. _supd. iterT 1.
    reveal ITREE. hide_l. _coreE x.
    assert (UPD': Own(x ⋅ rs) ==∗ Own (x ⋅ rt)).
    { iIntros "[H0 H1]". iSplitL "H0"; eauto.
      iApply UPD; eauto.
    }
    assert (✓ (x ⋅ rt)). 
    { 
      hexploit Own_bupd_valid; eauto.
      iIntros "H". iPoseProof (UPD' with "H") as ">[H0 H1]".
      iModIntro. iFrame.
    }
    iterL. _supd. iterL. _coreE H. ls.
    iterL. _coreE x1. ls. 
    iterL. _supd. iterL. _supd.
    iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H1, H2; eauto.
  Qed.




  Lemma cancel_main_grt
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l P
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS ()) (ktrT ()))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- trigger sGet;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst (λ x : (), Ret (inl (ITree.subst ktrS (Ret x))))
                     (ITree.subst (λ mr : Σ, mr' <- trigger (Choose Σ);; guarantee (Own mr ==∗ P ∗ Own mr');;; mput_res mr')
                        (ITree.subst (λ st0 : Any.t, x_0 <- (Any.split st0) ?;; (let (_, mr) := x_0 in (mr ↓) ?)) (Ret x_)));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
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
                             (vret <- ITree.subst (λ a : (), ktrT a) (Ret x);;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))))
                     (ITree.subst (λ mr : Σ, mr' <- trigger (Choose Σ);; guarantee (Own mr ==∗ P ∗ Own mr');;; mput_res mr')
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
      ired. hide_l. _supd.
      iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd. iterT 1.
      reveal ITREE. hide_r. _supd.
      assert (Own rs ==∗ P ∗ Own x).
      {
        iIntros "H". iPoseProof (UPD with "H") as ">H". 
        iApply x0; eauto.
      }
      iterL. _coreE x. iterL. _coreE H.
      iterL. _supd. iterL. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      { 
        hexploit Own_bupd_split; eauto. i. des.
        eapply Own_bupd_valid in H0; eauto.
        eapply Own_pure_soundness with (x:=a2).
        { eapply cmra_valid_op_r, Own_wand_valid; eauto. }
        iIntros "H". iApply Own_valid. iStopProof. eauto.
      }
      i. rewrite !list_lookup_insert_ne in H1, H2; eauto.
  Qed.

  Lemma cancel_main_tid
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ (tid: nat), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS tid) (ktrT tid))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=tau;; interp_hp (ktrS cid)]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0)))
    (cid, <[cid:=tau;; interp_hp (x_ <- ktrT cid;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta x_ ret));;; Ret ret))]> tgts)) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_l. tau 1. iterT 1. 
    reveal ITREE. hide_r. tau 1. iterT 1. 
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

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
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
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
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
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

  Lemma cancel_main_spawn
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q (cid tid: nat) st ps pt l fn f args
    srcs tgts ktrS ktrT
    (STB: stb sk0 fn = Some f)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WFS: ✓ rs)
    (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ (x: nat), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS x) (ktrT x))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  : 
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=tau;; interp_hp (tau;; trigger (Yield (base.length srcs));;; ktrS (base.length srcs))]> srcs ++ 
            [sem <- (alist_find fn (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                    (List.map (map_snd (wrap_elimI (SModSemAux.to_hmod (SMod.modsem md sk0))))
                    (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_aux ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem args])) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t
    (x_ <- trigger (|resum IFun (SMod2HMod.meta f) (Choose (SMod2HMod.meta f)))%sum;;
      x_0 <- Ret (inl
        (cid, <[cid:=lr <- ITree.subst (λ x : SMod2HMod.meta f, Ret (inl (vret <-
                              ITree.subst (λ x0 : nat, ktrT x0)
                                (ITree.subst
                                   (λ x0 : SMod2HMod.meta f,
                                      tau;; arg <- trigger (Choose Any.t);;
                                            (tau;; tid <- trigger (Spawn fn arg);;
                                                   (tau;; trigger (Guarantee (ginv sk0 tid -∗ precond f tid x0 args arg));;; (tau;; HoareYieldE (ginv sk0) tid;;; Ret tid))))
                                   (Ret x));;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret)))) (Ret x_);;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_l. _coreA.
    iterT 2. iterL. _coreA. ls.
    iterT 2. iterL. tau 1. ls. 
    rewrite !length_insert. 
    rewrite <- insert_app_l; eauto.
    assert (cid <
    base.length
      (tgts ++
       [' sem : (Any.t → itree modE Any.t) <-
        (alist_find fn
           (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
              (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
                 (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2)))
                    (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem x0])).
    { rewrite length_app. nia. }
    iterT 2. iterL. _supd.
    iterL. _coreA. ls. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. _supd. 
    iterL. _coreA. ls. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. tau 1. ls.    
    reveal ITREE. hide_r. tau 1. 
    rewrite -insert_app_l; eauto. 
    assert (cid <
    base.length
      (srcs ++
       [' sem : (Any.t → itree modE Any.t) <-
        (alist_find fn
           (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
              (List.map (map_snd (wrap_elimI (SModSemAux.to_hmod (SMod.modsem md sk0))))
                 (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_aux ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; 
        sem args])).
    { rewrite length_app. nia. }
    iterT 2.
    iterL. tau 1. ls. 
    hexploit stb_in_alist_find; eauto. i. des.
    reveal ITREE. 
    rewrite !alist_find_map_snd !H1. s.
    erewrite wrap_elimI_well_scoped; cycle 1.
    {
      instantiate (1:= fn).
      s. unfold interp_sb_hp_aux. s.
      rewrite alist_find_map_snd H1. ss.
    }
    erewrite wrap_elimI_well_scoped; cycle 1.
    {
      instantiate (1:= fn).
      s. unfold interp_sb_hp. s.
      rewrite alist_find_map_snd H1. ss.
    }
    ired.
    unfold interp_hp_fun, inline_hp_fun, HModSem.sandbox_body. s. 
    unfold interp_sb_hp, interp_sb_hp_aux. s.
    hide_l. _iter.
    rewrite list_lookup_insert_ne; try nia. 
    rewrite list_lookup_length. ired. tau 1.
    assert (forall x, base.length tgts < base.length (tgts ++ [x])). { i. rewrite length_app. s. nia. }
    hexploit (Own_bupd_split rt); eauto. i. des.
    hexploit (Own_bupd_split x1); eauto. 
    {
      hexploit (Own_wand_valid rt (a1 ⋅ x1)); eauto.
      {
        iIntros "H". iPoseProof (H3 with "H") as ">[H0 H1]".
        iPoseProof (H5 with "H1") as "H1". 
        iModIntro. rewrite Own_op. iFrame.
      }
      i. eapply cmra_valid_op_r. eauto. 
    }  
    i. des.
    iterT 2. iterL. _coreE x. ls.
    iterT 2. iterL. _coreE args. ls.
    iterT 2. iterL. _coreE (a0 ⋅ a1). ls. iterL. _supd. 
    assert (UPD': Own rs ==∗ Own (a0 ⋅ a1 ⋅ x3)). 
    {  
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H3 with "H") as ">[H0 H1]".
      iPoseProof (H5 with "H1") as "H1".
      iPoseProof (H6 with "H1") as ">[H1 H2]".
      iPoseProof (H8 with "H2") as "H2".
      iModIntro. rewrite !Own_op. iFrame.
    }
    assert (✓(a0 ⋅ a1 ⋅ x3)). 
    { eapply Own_wand_valid with (a1 := rs); eauto. }
    iterL. _coreE H9. ls. 
    assert (Own (a0 ⋅ a1) ⊢ precond f (base.length tgts) x args x0).
    {
      iIntros "[H0 H1]".  
      iPoseProof (H7 with "H0") as "H0".
      iPoseProof (H4 with "H1") as "H1".
      iApply "H1". eauto.
    } 
    iterL. _coreE H10. ls.
    iterL. _supd. iterL. _supd.
    iterT 2.
    reveal ITREE. prb. gbase. pclearbot. rewrite LEN.
    eapply CIH; try (rewrite !length_insert !length_app; s; nia); swap 6 8.
    { auto. }
    { auto. }
    {
      rewrite list_lookup_insert_ne; try nia. 
      rewrite -LEN list_lookup_length. f_equal.
    }
    {
      rewrite list_lookup_insert; eauto.
      rewrite length_insert length_app. s. nia. 
    }
    { i. nia. }
    {
      instantiate (1:= x). instantiate (1:= postcond f).
      instantiate (1:= inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox l0 (interp_smod (ginv sk0) (stb sk0) (fbody args)))).        
      des_ifs. rewrite bind_ret_l. f_equal.
      rewrite (bisim_is_eq (translate_bind _ _ _)).
      rewrite -HIRed.bind. 
      do 3 f_equal. extensionalities.
      match goal with [|-(?itr = _)] => set itr end.
      eassert (i = HModSem.sandbox l0 _). { unfold i. f_equal. }
      rewrite H12 HModSB.transl_bind HModSB.transl_core. 
      f_equal. extensionalities.
      rewrite HModSB.transl_bind HModSB.transl_ag.
      f_equal. extensionalities.
      rewrite HModSB.transl_ret. eauto.
    }
    { grind. }
    { eapply elim_rel_refl; eauto. } 
    i. rewrite list_lookup_insert_ne in H13; eauto.
    destruct (Nat.eq_dec cid k).
    {
      subst k. rewrite list_lookup_insert in H12; cycle 1.
      { rewrite length_app. s. nia. }
      rewrite list_lookup_insert in H13; cycle 1.
      { rewrite length_app. s. nia. }
      inv H12. econs; eauto; cycle 1.
      { destruct (Nat.eq_dec cid (base.length tgts)); try nia. grind. }
      {
        destruct (Nat.eq_dec cid (base.length tgts)); try nia.
        instantiate (1:= ktrT (base.length tgts)).
        unfold yield_post. ired. rewrite -interp_hp_tau. 
        do 6 f_equal. extensionalities. grind.
      }
      eapply KTR.
    }
    rewrite !list_lookup_insert_ne in H12, H13; try nia.
    eapply lookup_snoc_Some in H12, H13. des; try nia.
    specialize (RELS k x5 y n H15 H14).
    inv RELS. econs; eauto; des_ifs.
  Qed.

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
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel sk0 cid k x y)
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

  Lemma cancel_aux rs0 rt0 sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs rt srcs tgts cid st ps pt
       (WF: ✓ rs)       
       (LEN: cid < List.length srcs)
       (REL: Forall2i (thread_rel sk0 cid) 0 srcs tgts)
       (UPD: Own rs ==∗ Own rt)
       ,
       gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
       (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
              (cid, srcs))
         (Any.pair st rs↑);; Ret x.2)
         (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSem.to_hmod (ginv sk0) 
                            (stb sk0) (SMod.modsem md sk0))) rt0))) 
              (cid, tgts))
         (Any.pair st rt↑);; Ret x.2).
  Proof.
    i. exploit Forall2i_nth; eauto. i. des.
    rename x into src, y into tgt.
    depdes x2.
    hexploit REL. i. eapply Forall2i_len in H. des.
    assert (cid < List.length tgts). { rewrite <- H. eauto. }
    assert (RELS: forall k x y (NEQ: cid ≠ k)
                    (LKX: srcs !! k = Some x)
                    (LKY: tgts !! k = Some y),
                      thread_rel sk0 cid k x y). 
    { i. eapply Forall2i_forall in REL; eauto. }
    clear REL. rename REL0 into REL. unfold elim_rel in REL.
    revert_until SKWF. s. gcofix CIH. i.
    _iter. _iter. rewrite x7 x8. subst. ired.
    destruct (Nat.eq_dec cid cid); ss. grind.
    assert (✓ rt). { eapply Own_wand_valid with (a1:=rs); eauto. } 
    punfold REL.  
    pattern itrS, itrT. depdes REL; ired.
    - hide_l. _coreA.
    - eapply cancel_main_ret; eauto. 
    - eapply cancel_main_tau; eauto.
    - eapply cancel_main_core; eauto.
    - eapply cancel_main_pg; eauto. 
    - eapply cancel_main_asm; eauto.
    - eapply cancel_main_grt; eauto.
    - eapply cancel_main_tid; eauto.
    - eapply cancel_main_head; eauto.
    - eapply cancel_main_tail; eauto.
    - eapply cancel_main_spawn; eauto.
    - eapply cancel_main_yield; eauto.
  Qed.

  Lemma fsb_find_spec fn l fsp fbody (sk0: Sk.t)
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
    alist_find fn (_stb SKINCL SKWF) = Some (l, fsp).
  Proof.
    unfold sbtb, _stb.
    rewrite alist_find_map_snd/o_map FIND. ss.
  Qed. 

  Lemma stb_find_fsb fn fsp l fspec fbody (sk0: Sk.t)
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (STB: stb sk0 fn = Some fsp)
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec:= fspec; fsb_body := fbody|}))
  :
    fsp = fspec.
  Proof.
    specialize (STBCOMPLETE SKINCL SKWF fn).
    eapply fsb_find_spec, STBCOMPLETE in FIND; ss.
    rewrite FIND in STB. inv STB. ss. 
  Qed.

  Lemma cancel_main 
      P sk0 fsp meta rs rt r
      (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0)
      (WF: HModSem.wf (md_src.(HMod.modsem) sk0))
      (STB: stb sk0 "CRIS_init" = Some fsp)
      (VALID: ✓ rs)
      (EQUIV: rs ≡ r ⋅ rt)
      (PRE: Own r ⊢ fsp.(precond) 0 meta tt↑ tt↑)
      (SAT: Own rt ⊢ P sk0)
      (POST: ∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    :  
      refines_modsem
        (HModSem.to_mod ((HModAux.inline md_src).(HMod.modsem) sk0) rs)
        (HModSem.to_mod ((HModAux.inline md_tgt).(HMod.modsem) sk0) rt).
  Proof.
    r. eapply adequacy_global.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.compile. s. unfold ITree.map.
    destruct (alist_find "CRIS_init" (SModSem.fnsems (SMod.modsem md sk0))) eqn:E; cycle 1.
    {
      rewrite !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite StRed.bind. grind.
      destruct (resum IFun False (Choose False)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite [interp_stateE _ _ _]StRed.core. grind.
      ginit. st. i. ss.
    }
    rewrite !alist_find_map/o_map E. s. 
    erewrite !wrap_elimI_well_scoped; cycle 1.
    { unfold SModSem.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    { unfold SModSemAux.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    ired. destruct p. s.
    unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold inline_hp_fun, interp_sb_hp. s.
    unfold HoareFun.
    
    unfold interp_modE, interp_schE_callE. 
    destruct f.
    assert (SKINCL: incl sk sk0). { eapply Sk.equiv_incl. eauto. }
    pose proof (stb_find_fsb SKINCL SKWF STB E). subst.
    hide_l.
    ginit.
    rewrite !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists meta. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists r. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    assert (V: ✓(r ⋅ rt)). { eapply valid_solve_eq; eauto. }
    exists V. ired. _tau. st. st. 
    _iter. _core. st. exists PRE. ired.
    _iter. _tau. st. st. _supd. _iter. _supd.
    _iter. _tau. st. st. rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CRIS_init's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto; cycle 1.
    { eapply Own_equiv in EQUIV. iIntros "H". iModIntro. iApply EQUIV. eauto. }
    econs; eauto using Forall2i.
    econs; s; eauto; try rewrite bind_ret_l; ss.
    { i. specialize (POST meta vret ret). auto. }
    { eapply elim_rel_refl; eauto. }
    rewrite HModSB.transl_bind HIRed.bind. 
    do 2 f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_ag. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed.
  
  (*** Final Theorem ***)
  Theorem cancellation P fsp meta
      (STB: ∀sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), stb sk0 "CRIS_init" = Some fsp)
      (POST: ∀sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0) m vret ret, 
                (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    :
    refines (md_src, P ∗∗ (fun _ => fsp.(precond) 0 meta tt↑ tt↑)) (md_tgt, P).
  Proof. 
    etrans.
    { eapply cancel_call_rev. }
    etrans; cycle 1.
    { eapply cancel_call. }
    r. esplits; ss.
    ii. eapply Own_split in SRC; eauto. des.
    exists a1. esplits; eauto.
    { eapply cmra_valid_op_l, valid_solve_eq; eauto. }
    {
      inv WFM. econs; eauto. s.
      do 2 rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    }
    eapply cancel_main; eauto.
    {
      inv WFM. econs; eauto. s.
      rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    }
    etrans; eauto. r_solve.
  Qed.
    
End CANCEL.

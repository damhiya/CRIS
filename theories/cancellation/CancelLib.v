Require Import Common.

Require Import SMod2HMod HMod2Mod SMod HMod Mod.
Require Import SimGlobal ITactics.
Require Import ElimRel SModCancel StRed HModInline.

Set Implicit Arguments.

Module CancelTAC.
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
  Ltac _iter := rewrite {1}unfold_iter_eq; ired.
  Ltac _tau := rewrite !StRed.tau.
  Ltac ls := rewrite !list_insert_insert.
  Ltac _supd := rewrite !StRed.bind StRed.state; grind; try ls; _tau; st; st; try (rewrite Any.pair_split; ired); try (rewrite Any.upcast_downcast; ired).
  Ltac iterL := _iter; rewrite list_lookup_insert;[|try rewrite !length_insert; auto]; ired.
  Tactic Notation "tau" integer(n) := _tau; do n st.
  Tactic Notation "iterT" integer(n) := do n (iterL; ls; tau 2).
  Ltac _core := rewrite StRed.bind StRed.core; prep.
  Ltac _coreA := _core; st; i; st; grind; _tau; st.
  Ltac _coreE x := _core; st; exists x; st; grind; _tau; st.

  Ltac done_by_CIH CIH LKX LKY :=
    prb; gbase; pclearbot; eapply CIH; eauto;
    try (rewrite !length_insert; nia);
    try (rewrite list_lookup_insert; grind);
    try (i; rewrite !list_lookup_insert_ne in LKX, LKY; eauto).
  
End CancelTAC.

Section CANCEL.
  Context `{Σ: GRA}.
  Variable md: SMod.t.

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

  Definition yield_post (ginv: nat -> iProp Σ): itree hmodE _ :=
      tau;; tau;; tid <- trigger Tid;; x <- (tau;; trigger (Assume (ginv tid)));; Ret ().

  Variant thread_rel ginv (cid tid: nat) src tgt : Prop :=
  | thread_rel_body X (meta: X) (Q: nat -> X -> Any.t -> Any.t -> iProp Σ) l itrS itrT
      (RET: ∀vret ret, 
            tid = 0 -> Q tid meta vret ret ⊢ ⌜vret = ret⌝)
      (REL: @elim_rel _ md ginv _ l itrS itrT)
      (SRC: src = 
          ((if Nat.eq_dec tid cid then Ret tt else tau;; Ret tt);;; interp_hp itrS))
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else yield_post ginv);;;
              vret <- itrT;; 
              (inline_hp (prog (SMod.to_hmod ginv (spc_global md) md))
                (ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q tid meta vret ret));;;
                  Ret ret))))) 
  .

  Lemma valid_solve (a b c: Σ) :
    ✓ a -> a ≡  b ⋅ c -> ✓ b.
  Proof.
    i. eapply cmra_valid_op_l. setoid_rewrite <- H0. eauto.
  Qed.

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

  Definition CANCEL_GOAL
    (R: ∀ x0 x1, (x0→x1→Prop)→smj→smj→itree coreE x0→itree coreE x1→Prop)
    ginv (rs0 rt0: Σ) ps pt srcs tgts cid st (rs rt: Σ) : Prop :=
    R Any.t Any.t eq ps pt
    (x <-
     interp_stateE Any.t
       (ITree.iter
          (handle_schE_callE
             (Mod.prog
                (HMod.to_mod
                   (HModInline.inline
                      (SModCancel.to_hmod md)) rs0)))
          (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
    (x <-
     interp_stateE Any.t
       (ITree.iter
          (handle_schE_callE
             (Mod.prog
                (HMod.to_mod
                   (HModInline.inline
                      (SMod.to_hmod ginv (spc_global md)
                         md)) rt0)))
          (cid, tgts)) (Any.pair st rt ↑);; Ret x.2).

  Definition cancel_term ginv (cid:nat) X (meta: X) Q (itrT: itree hmodE Any.t) :=
    (vret <- itrT;;
     inline_hp (prog
          (SMod.to_hmod ginv
             (spc_global md) md))
       (ret <- trigger (Choose Any.t);;
        trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
  .
  
End CANCEL.

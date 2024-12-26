Require Import Common.

Require Import SMod2HMod HMod2Mod SMod HMod Mod Skeleton.
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

End CancelTAC.

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

  Let md_src: HMod.t := SModCancel.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

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
  
End CANCEL.

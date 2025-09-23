Require Import Common Sp ConcRA.
Require Import SMod Mod LMod SModTr ModTr LModTr.
Require Import MInline Tactics GSim.
From iris.proofmode Require Export proofmode.

Set Implicit Arguments.

Section CancelLib.

  Definition Forall2i X Y (R: nat -> X -> Y -> Prop) (xs: list X) (ys: list Y) :=
    length xs = length ys ∧
    ∀ i x y (EQx: xs !! i = Some x) (EQy: ys !! i = Some y),
      R i x y.

  Definition Forall3i {X Y Z}
      (R : nat → X → Y → Z → Prop)
      (xs : list X) (ys : list Y) (zs : list Z) :=
    length xs = length ys ∧ length ys = length zs ∧
    ∀ i x y z,
      xs !! i = Some x → ys !! i = Some y → zs !! i = Some z →
      R i x y z.

  Lemma Forall2i_nth
    X Y (xs: list X) (ys: list Y) (R: nat → X → Y → Prop) i
    (REL: Forall2i R xs ys)
    (NTH: i < List.length xs)
    :
    ∃ x y,
    xs !! i = Some x /\
    ys !! i = Some y /\
    R i x y.
  Proof using.
    destruct REL. revert_until xs. induction xs; i.
    - destruct ys; ss. destruct i; try nia.
    - destruct ys; ss. destruct i; s. { esplits; et. }
      eapply (IHxs ys (λ i, R (S i))); et; nia.
  Qed.

  Lemma Forall3i_nth {X Y Z}
      (i : nat)
      (xs : list X) (ys : list Y) (zs : list Z)
      (R: nat → X → Y → Z → Prop) :
    Forall3i R xs ys zs →
    i < List.length xs →
    (∃ x y z,
      xs !! i = Some x ∧ ys !! i = Some y ∧ zs !! i = Some z ∧
      R i x y z).
  Proof using.
    intros Hrel Hlt; destruct Hrel as [? [? ?]]. revert_until xs. revert i.
    induction xs; i.
    - destruct ys; ss. destruct zs; des; ss. destruct i; try nia.
    - destruct ys; ss. destruct zs; des; ss. destruct i; s.
      { esplits; et. }
      eapply (IHxs i ys zs (λ i, R (S i))); et; nia.
  Qed.
  
  Lemma list_lookup_length {X} (x: X) l:
    (l ++ [x]) !! (base.length l) = Some x.
  Proof using.
    eapply lookup_snoc_Some; right; eauto.
  Qed.

End CancelLib.

Section ELIM_REL.
Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Definition NativeSpawnE (fn: string) (arg: Any.t) : itree crisE nat :=
  tid <- trigger (Spawn fn arg);; tau;; Ret tid.

Definition NativeYieldE tid : itree crisE () :=
  trigger (Yield tid);;; tau;; Ret tt.

Definition NativeGetTidE : itree crisE nat :=
  my_tid <- trigger GetTid;; tau;; Ret my_tid.

Definition HoareSpawnE fn varg (fspo: option fspec) : itree crisE nat :=
  match fspo with
  | Some (@fspec_spawn _ meta pre post) =>
      x <- trigger (Choose meta);; tau;;
      arg <- trigger (Choose Any.t);; tau;;
      tid <- trigger (Spawn fn arg);; tau;;
      trigger (Assume (YIELD tid));;; tau;;
      trigger (Guarantee (pre (tid, x) varg arg));;; tau;;
      Ret tid
  | Some (@fspec_call _ meta pre post) =>
      triggerNB
  | None => NativeSpawnE fn varg
  end.

Definition HoareYieldE tid : itree crisE () :=
  my_tid <- trigger (Choose nat);; tau;;
  trigger (Guarantee (TID(my_tid) ∗ YIELD(tid) ∗ winv(⊤, ⊤)));;; tau;;
  trigger (Yield tid);;; tau;;
  trigger (Assume (TID(my_tid) ∗ YIELD(my_tid) ∗ winv(⊤, ⊤)));;; tau;;
  Ret tt.

Definition HoareGetTidE : itree crisE nat :=
  my_tid <- trigger (Choose nat);; tau;;
  trigger (Guarantee (TID(my_tid)));;; tau;;
  tid <- trigger GetTid;; tau;;
  trigger (Assume (⌜tid = my_tid⌝ ∗ TID(my_tid)));;; tau;;
  Ret tid.

Definition elim_precond {X X' : Type} P P' (varg: Any.t) : itree crisE (X * X' * Any.t) :=
  x <- trigger (Choose X);; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (P x varg arg));;; tau;; tau;;
  x' <- trigger (Take X');; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  trigger (Assume (P' x' varg' arg));;; tau;;
  Ret (x, x', varg').

Definition elim_postcond {X X' : Type} Q Q' (x : X) (x' : X') (vret': Any.t) : itree crisE Any.t :=
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (Q' x' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  trigger (Assume (Q x vret ret));;; tau;;
  Ret vret.

(* Definition elim_trivial_precond (arg: Any.t) : itree crisE Any.t := *)
(*   trigger (Take ());;; tau;; *)
(*   varg <- trigger (Take Any.t);; tau;; *)
(*   trigger (Assume ⌜varg = arg⌝);;; tau;; *)
(*   Ret varg. *)

(* Definition elim_trivial_postcond (vret: Any.t) : itree crisE Any.t := *)
(*   ret <- trigger (Choose Any.t);; tau;; *)
(*   trigger (Guarantee (⌜vret = ret⌝)%I);;; tau;; *)
(*   Ret ret. *)

Definition elim_spawnee_precond (X : Type) P (arg : Any.t) : itree crisE (nat * X * Any.t) :=
  tid <- trigger (Take nat);; tau;;
  trigger (Assume (TID tid ∗ YIELD tid ∗ winv(⊤, ⊤)));;; tau;;
  x <- trigger (Take X);; tau;;
  varg <- trigger (Take Any.t);; tau;;
  trigger (Assume (P (tid, x) varg arg));;; tau;;
  Ret (tid, x, varg).

Definition elim_spawnee_postcond {X : Type} Q (tid : nat) (x : X) (vret : Any.t) : itree crisE Any.t :=
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (Q (tid, x) vret ret));;; tau;;
  trigger (Guarantee (TID tid ∗ winv(⊤, ⊤)));;; tau;;
  Ret ret.

Variant elim_rel_def
    (sp : sp_type)
    (self : ∀ T, Σ → itree crisE T → itree crisE T → Prop) (T : Type)
  : Σ → itree crisE T → itree crisE T → Prop :=

(* handling void cases *)
| elim_take_false ktrS itrT :
   elim_rel_def sp self ε (trigger (Take False) >>= ktrS) itrT
| elim_tau_take_false ktrS itrT :
   elim_rel_def sp self ε (tau;; trigger (Take False) >>= ktrS) itrT
| elim_choose_false itrS ktrT :
   elim_rel_def sp self ε itrS (trigger (Choose False) >>= ktrT)
(* handling normal cases *)
| elim_rel_ret v :
   elim_rel_def sp self ε (Ret v) (Ret v)
| elim_rel_tau itrS itrT :
   self _ ε itrS itrT →
   elim_rel_def sp self ε (tau;; itrS) (tau;; itrT)
| elim_rel_core {R} (e : coreE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
| elim_rel_pg {R} (e : pgE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
| elim_rel_ag {R} (e : agE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
(* handling cancellation *)
| elim_rel_yield tid ktrS ktrT itrS itrT :
    itrS = NativeYieldE tid >>= ktrS →
    itrT = HoareYieldE tid >>= ktrT →
    (∀ x, self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def sp self ε itrS itrT
| elim_rel_spawn fn args ktrS ktrT itrS itrT :
   (* (img = false → fspec_imply (fspec_flat (sp fn)) fspec_trivial) → *)
   itrS = NativeSpawnE fn args >>= ktrS →
   itrT = HoareSpawnE fn args (sp fn) >>= ktrT →
   (∀ x, self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε itrS itrT
| elim_rel_precond (X X' : Type) P P' varg itrS itrT ktrT :
   (∀ (x : X), ∃ (x' : X'),
     (∀ arg, P x varg arg ⊢ |==> P' x' varg arg) ∧ self _ ε itrS (ktrT (x, x', varg))) →
   itrT = elim_precond P P' varg >>= ktrT →
   elim_rel_def sp self ε (tau;; tau;; tau;; itrS) itrT
| elim_rel_postcond (X X': Type) Q Q' (x: X) (x': X') vret itrS itrT ktrT :
   ((∀ ret, Q' x' vret ret ⊢ |==> Q x vret ret) ∧ self _ ε itrS (ktrT vret)) →
   itrT = elim_postcond Q Q' x x' vret >>= ktrT →
   elim_rel_def sp self ε (tau;; tau;; itrS) itrT
| elim_rel_gettid ktrS ktrT itrS itrT :
   itrS = NativeGetTidE >>= ktrS ->
   itrT = HoareGetTidE >>= ktrT ->
   (∀ x, self _ ε (ktrS x) (ktrT x)) ->
   elim_rel_def sp self ε itrS itrT
.

Definition elim_rel sp T r_diff itrS itrT :=
  paco4 (@elim_rel_def sp) bot4 T r_diff itrS itrT.

Lemma elim_rel_def_mon sp r1 r2 :
  r1 <4= r2 →
  @elim_rel_def sp r1 <4= elim_rel_def sp r2.
Proof using.
  intros ??????PR; destruct PR; eauto using @elim_rel_def.
  - eapply elim_rel_precond; eauto; des_safe.
    i. specialize (H0 x). des; eauto.
  - eapply elim_rel_postcond; eauto; des_safe.
    esplits; eauto.
Qed.

Hint Resolve cpn4_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Variant elim_rel_bindC
    (r : ∀ T, Σ → itree crisE T -> itree crisE T -> Prop) T
  : Σ → itree crisE T -> itree crisE T -> Prop :=
  | elim_rel_bindC_intro R r_diff itrS itrT ktrS ktrT :
     r R r_diff itrS itrT →
     (∀ v, r T ε (ktrS v) (ktrT v)) →
     elim_rel_bindC r r_diff (itrS >>= ktrS) (itrT >>= ktrT).

Lemma elim_rel_bindC_mon : monotone4 elim_rel_bindC.
Proof using. ii. destruct IN; econs; eauto. Qed.

Lemma elim_rel_bindC_spec sp :
  elim_rel_bindC <5= gupaco4 (@elim_rel_def sp) (cpn4 (@elim_rel_def sp)).
Proof using.
  eapply wrespect4_uclo; eauto with paco.
  econs; [apply elim_rel_bindC_mon|].
  i. inv PR. apply GF in H.
  inv H; grind; eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
  - eapply elim_rel_precond; i; et.
    specialize (H1 x). des; esplits; eauto.
    eapply rclo4_clo'; cycle 1.
    + econs; [eapply H2|]; et.
    + eauto using rclo4.
  - eapply elim_rel_postcond; i; et.
    des_safe. esplits; et.
    eapply rclo4_clo'; cycle 1.
    + econs; [eapply H2|]; et.
    + eauto using rclo4.
Qed.

Lemma SBRed_NativeSpawn img msk scp fn varg :
  SB.sandbox img msk scp (SModTr.NativeSpawn fn varg) =
    if msk fn then SModTr.NativeSpawn fn varg else triggerUB.
Proof using. rewrite /SModTr.NativeSpawn SBRed.spawn. des_ifs; cycle 1. Qed.

Lemma SBRed_HoareSpawn (img: bool) (msk : _ → bool) scp fn varg fspo
  (MSK: msk fn)
  (IMG: (negb img) → fspo = None)
  :
  SB.sandbox img msk scp (SModTr.HoareSpawn fn varg fspo) =
    SModTr.HoareSpawn fn varg fspo.
Proof using.
  rewrite /SModTr.HoareSpawn. destruct fspo; cycle 1.
  { rewrite SBRed_NativeSpawn MSK. et. }
  destruct img; cycle 1.
  { exploit IMG; et. i. ss. }
  destruct f.
  { rewrite /triggerNB /= SBRed.bind SBRed.choose. f_equal. extensionalities; ss. }
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.spawn MSK. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Assume. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
  rewrite SBRed.ret. f_equal.
Qed.

Lemma MIRed_NativeSpawn prog fn varg :
  inline_body prog (SModTr.NativeSpawn fn varg) = NativeSpawnE fn varg.
Proof using.
  rewrite /SModTr.NativeSpawn /NativeSpawnE.
  rewrite -(bind_ret_r (trigger _)).
  rewrite MIRed.spawn. f_equal.
  { rewrite bind_ret_r //. }
  extensionalities. do 2 f_equal.
  rewrite MIRed.ret //.
Qed.

Lemma MIRed_HoareSpawn prog fspo fn varg (ST: fspo = None ∨ is_spawn_ospec fspo) :
  inline_body prog (SModTr.HoareSpawn fn varg fspo) = HoareSpawnE fn varg fspo.
Proof using.
  destruct fspo; ss; [|rewrite MIRed_NativeSpawn //].
  destruct f; des; ss.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.spawn. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  by rewrite MIRed.ret.
Qed.

Lemma SBRed_NativeYield img msk scp tid :
  SB.sandbox img msk scp (SModTr.NativeYield tid) = SModTr.NativeYield tid.
Proof using. rewrite /SModTr.NativeYield SBRed.yield. refl. Qed.

Lemma SBRed_HoareYield (img: bool) (msk : _ → bool) scp tid :
  SB.sandbox img msk scp (SModTr.HoareYield img tid) =
    SModTr.HoareYield img tid.
Proof using.
  rewrite /SModTr.HoareYield. destruct img; cycle 1.
  { eapply SBRed_NativeYield. }
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.yield. f_equal. extensionalities.
  rewrite SBRed.Assume. f_equal.
Qed.

Lemma MIRed_NativeYield prog tid :
  inline_body prog (SModTr.NativeYield tid) = NativeYieldE tid.
Proof using.
  rewrite /SModTr.NativeYield /NativeYieldE.
  rewrite -(bind_ret_r (trigger _)).
  rewrite MIRed.yield. f_equal.
  { rewrite bind_ret_r //. }
  extensionalities. do 2 f_equal.
  rewrite MIRed.ret //. destruct H; refl.
Qed.

Lemma MIRed_HoareYield prog tid :
  inline_body prog (SModTr.HoareYield true tid) = HoareYieldE tid.
Proof using.
  rewrite /SModTr.HoareYield /HoareYieldE. ired.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.yield. f_equal. extensionalities. do 2 f_equal.
  rewrite -{1}(bind_ret_r (trigger _)).
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  destruct H2. by rewrite MIRed.ret.
Qed.

Lemma SBRed_NativeGetTid img msk scp :
  SB.sandbox img msk scp SModTr.NativeGetTid = SModTr.NativeGetTid.
Proof using. rewrite /SModTr.NativeGetTid SBRed.gettid. refl. Qed.

Lemma SBRed_HoareGetTid (img: bool) (msk : _ → bool) scp :
  SB.sandbox img msk scp (SModTr.HoareGetTid img) =
    SModTr.HoareGetTid img.
Proof using.
  rewrite /SModTr.HoareGetTid. destruct img; cycle 1.
  { eapply SBRed_NativeGetTid. }
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.gettid. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Assume. f_equal. extensionalities.
  rewrite SBRed.ret. f_equal.
Qed.

Lemma MIRed_NativeGetTid prog :
  inline_body prog SModTr.NativeGetTid = NativeGetTidE.
Proof using.
  rewrite /SModTr.NativeGetTid /NativeGetTidE.
  rewrite -(bind_ret_r (trigger _)).
  rewrite MIRed.gettid. f_equal.
  { rewrite bind_ret_r //. }
  extensionalities. do 2 f_equal.
  rewrite MIRed.ret //.
Qed.

Lemma MIRed_HoareGetTid prog :
  inline_body prog (SModTr.HoareGetTid true) = HoareGetTidE.
Proof using.
  rewrite /SModTr.HoareGetTid /HoareGetTidE. ired.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.gettid. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  by rewrite MIRed.ret.
Qed.

Lemma if_simpl X (b: bool) (x: X):
  (if b then x else x) = x.
Proof using. destruct b; et. Qed.

Lemma MIRed_HoareFun
    (md : SMod.t) (sp : sp_type) (img : bool) (msk : string → bool) (scp : list string)
    (bd : fbody) (fspo : option fspec) (arg : Any.t)
    (fno : option string) meta pre post:
  SMod.cancellable md →
  alist_find fno (SMod.fnsems md) = Some (img, msk, scp, (fspo, bd)) →
  fspo = Some (@fspec_spawn _ meta pre post) →
  inline_body
    (sandboxed_prog (SMod.to_mod sp md))
    (SB.sandbox_body (true, msk, scp,
      SModTr.HoareFun fspo (SModTr.trans true sp ∘ bd)) arg) =
  '(tid, x, varg) : _ <- @elim_spawnee_precond _ pre arg;;
  vret <-
    inline_body
      (sandboxed_prog (SMod.to_mod sp md))
      (SB.sandbox true msk scp (SModTr.trans true sp (bd varg)));;
  elim_spawnee_postcond post tid x vret.
Proof using.
  intros Hwf Hfind Hst.
  rewrite /SModTr.HoareFun /elim_spawnee_precond /elim_spawnee_postcond /=.
  destruct fspo; ss. destruct f; ss. depdes Hst.
  rewrite /SB.sandbox_body SBRed.bind SBRed.take /=.
  rewrite MIRed.core; ired; f_equal.
  extensionalities x; ired; do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume MIRed.ag; f_equal.
  extensionalities y; destruct y; ired; do 2 f_equal.
  rewrite SBRed.bind SBRed.take MIRed.core; f_equal.
  extensionalities z; ired; do 2 f_equal.
  rewrite SBRed.bind SBRed.take MIRed.core; f_equal.
  extensionalities w; ired; do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume MIRed.ag; f_equal.
  extensionalities a; destruct a; ired; do 2 f_equal.
  rewrite SBRed.bind MIRed.bind; f_equal.
  extensionalities vret.
  rewrite SBRed.bind SBRed.choose MIRed.core; f_equal.
  extensionalities ret; ired; do 2 f_equal.
  rewrite SBRed.bind SBRed.Guarantee MIRed.ag; f_equal.
  extensionalities b; destruct b; do 2 f_equal.
  rewrite SBRed.bind SBRed.Guarantee MIRed.ag; f_equal.
  extensionalities c; destruct c; do 2 f_equal.
  rewrite SBRed.ret MIRed.ret //.
Qed.

Lemma MIRed_HoareCall md sp fn varg
  (msk msk0: _→bool) scp scp0 fspo fspo0 bd0 m m0 pre pre0 post post0
  (WF: SMod.cancellable md)
  (IN: msk fn)
  (SP: fspo = sp fn)
  (FIND: alist_find (Some fn) (SMod.fnsems md) = Some (true, msk0, scp0, (fspo0, bd0)))
  (ST: fspo = Some (@fspec_call _ m pre post))
  (ST0: fspo0 = Some (@fspec_call _ m0 pre0 post0))
  :
  inline_body (sandboxed_prog (SMod.to_mod sp md)) (SB.sandbox true msk scp (SModTr.HoareCall fn varg fspo))
  =
  (* head *)
  '(x,x0,arg):_ <- elim_precond pre pre0 varg ;;
  (* body *)
  vret0 <- inline_body (sandboxed_prog (SMod.to_mod sp md)) 
                       (SB.sandbox true msk0 scp0 (SModTr.trans true sp (bd0 arg)));;
  (* tail *)
  elim_postcond post post0 x x0 vret0.
Proof using.
  destruct fspo; ss. destruct f; ss. depdes ST.
  destruct fspo0; ss. destruct f; ss. depdes ST0.
  rewrite /elim_precond /elim_postcond. ired.
  rewrite !SBRed.bind !SBRed.choose /= MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.bind !SBRed.choose /= MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.bind SBRed.Guarantee MIRed.ag. ired. do 2 f_equal.
  extensionalities. do 2 f_equal.
  rewrite SBRed.call. destruct (msk fn); ss.
  rewrite MIRed.call {2}/sandboxed_prog.
  ired. rewrite alist_find_map_snd FIND. s. ired.
  rewrite /SB.sandbox_body /SModTr.trans_body. s. do 2 f_equal.
  rewrite !SBRed.bind !SBRed.take /= MIRed.bind MIRed.core. ired. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.bind SBRed.take /=. ired. rewrite MIRed.core. ired. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.bind SBRed.Assume /=. ired. rewrite MIRed.ag. ired. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite MIRed.bind. ired. do 2 f_equal.
  extensionalities. ired.
  rewrite !SBRed.bind SBRed.choose MIRed.core. ired. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.bind SBRed.Guarantee MIRed.ag. ired. do 2 f_equal.
  extensionalities. do 2 f_equal.
  rewrite !SBRed.ret MIRed.ret. ired.
  rewrite !MIRed.tau !SBRed.bind SBRed.take /= MIRed.core. ired. do 6 f_equal.
  extensionalities. do 2 f_equal.
  rewrite !SBRed.bind SBRed.Assume /=. ired. rewrite MIRed.ag. ired. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite SBRed.ret MIRed.ret. refl.
(*SLOW*)Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto 6 with paco.

Lemma elim_rel_cancel (md: SMod.t) T msk scp (itr: itree _ T)
  (WF: SMod.cancellable md)
  :
  @elim_rel (sp_from md) T ε
    (inline_body (sandboxed_prog (SMod.to_mod sp_none (SMod.cancel md))) 
      (SB.sandbox true msk scp (SModTr.trans false sp_none itr)))
    (inline_body (sandboxed_prog (SMod.to_mod (sp_from md) md)) 
      (SB.sandbox true msk scp (SModTr.trans true (sp_from md) itr))).
Proof using.
  ginit. revert T itr msk scp. gcofix CIH. i.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SBRed.ret !MIRed.ret. estep 1.
  - rewrite !SRed.tau !SBRed.tau !MIRed.tau. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Assume.
    rewrite !MIRed.ag. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind !SBRed.AssumeRes.
    rewrite !MIRed.ag. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind !SBRed.Guarantee !MIRed.ag.
    estep 2. edone.
  - depdes c; s.
    (* call case *)
    { 
      rewrite !SRed.bind !SBRed.bind !SRed.call !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. estep 2. destruct (msk fn) eqn: E; cycle 1.
      { rewrite SBRed.call E /triggerUB // MIRed.core. ired. estep 1. }
      destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: E0; cycle 1.
      { rewrite SBRed.call E -(bind_ret_r (trigger _)) MIRed.call
                {2}/sandboxed_prog // !alist_find_map_snd E0 //.
        ired. rewrite MIRed.core. ired. estep 1. }
      destruct f as [[[img0 msk0] scp0] [fsp0 bd0]].
      destruct fsp0; [destruct f|]; cycle 1.
      { rewrite /SModTr.HoareCall. rewrite /sp_from /to_sp alist_find_map_snd E0 /=.
        rewrite /triggerNB /= SBRed.bind SBRed.choose MIRed.core. ired. estep 1. }
      { r in WF. hexploit WF; eauto; i; ss; des; ss. }
      replace img0 with true in *; cycle 1.
      { r in WF. hexploit WF; eauto 1; i; ss; des. destruct img0; ss. }

      des. erewrite MIRed_HoareCall; et; cycle 1.
      { rewrite /sp_from /to_sp alist_find_map_snd E0 //. }
      rewrite SBRed.call E -(bind_ret_r (trigger _)) MIRed.call.
      rewrite {2}/sandboxed_prog. s. rewrite !alist_find_map_snd E0. s. ired.
      rewrite /SB.sandbox_body /SModTr.trans_body. s.
      rewrite SBRed.tau bind_tau MIRed.tau ?bind_tau MIRed.bind. ired.
      
      gstep. eapply elim_rel_precond; eauto. i.
      exists x. split; eauto.

      ired. guclo elim_rel_bindC_spec. econs; [edone|].

      i. ired. rewrite !MIRed.tau MIRed.ret. ired.
      gstep. eapply elim_rel_postcond; et.
      split; eauto. edone.
    }
    
    (* spawn case *)
    {
      rewrite !SRed.bind !SBRed.bind !SRed.spawn !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. rewrite SBRed_NativeSpawn. estep 2.
      destruct (msk fn) eqn: E; cycle 1.
      { rewrite /triggerUB // MIRed.core. ired. estep 1. }
      rewrite MIRed_NativeSpawn SBRed_HoareSpawn; et; ss.
      destruct (match (sp_from md) fn with | Some (@fspec_call _ _ _ _) => true | _ => false end) eqn:ST.
      { destruct (sp_from md fn); ss. destruct f; ss. rewrite MIRed.core. ired. estep 1. }
      rewrite MIRed_HoareSpawn; cycle 1.
      { destruct (sp_from md fn); ss; eauto. destruct f; ss; eauto. }
      gstep. eapply elim_rel_spawn; et.
      i. edone.
    }

    (* yield case *)
    {
      rewrite !SRed.bind !SRed.yield !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau. estep 2.
      rewrite !MIRed.bind SBRed_HoareYield SBRed_NativeYield /= MIRed_HoareYield MIRed_NativeYield.
      gstep. eapply elim_rel_yield; eauto.
      i; s. edone.
    }

    (* get tid case *)
    {
      rewrite !SRed.bind !SRed.gettid !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau.
      rewrite !MIRed.bind SBRed_HoareGetTid SBRed_NativeGetTid MIRed_HoareGetTid MIRed_NativeGetTid.
      estep 2. gstep. eapply elim_rel_gettid; eauto.
      i; s. edone.
    }

  - rewrite !SRed.bind !SRed.pg !SBRed.bind. destruct s.
    + rewrite !SBRed.put. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2. edone.
    + rewrite !SBRed.get. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2. edone.
  - rewrite !SRed.bind !SRed.core !SBRed.bind. destruct e.
    + rewrite !SBRed.choose !MIRed.core. estep 2. edone.
    + rewrite !SBRed.take. destruct (_ || _) eqn: E; cycle 1.
      { ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2. edone.
    + rewrite !SBRed.io !MIRed.core. estep 2. edone.
(*SLOW*)Qed.

End ELIM_REL.
Hint Resolve cpn4_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Section CancelDef.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

  Definition main_post : Any.t → itree lmodE Any.t :=
    λ vret,
      ModTr.trans
        (ret <- trigger (Choose Any.t);; tau;;
         trigger (Guarantee ⌜vret = ret⌝);;; tau;; Ret ret).

  (* thread_rel cid tid ... *)
  Variant thread_rel sp cid : nat → Σ → itree lmodE Any.t → itree lmodE Any.t → Prop :=
  | thread_rel_body itrS itrT src tgt r_diff tid (k: Any.t → itree lmodE Any.t)
      (RET: tid = 0 -> k = main_post)
      (TEQ: cid = tid)
      (REL: elim_rel sp r_diff itrS itrT)
      (SRC: src = ModTr.trans itrS)
      (TGT: tgt = ModTr.trans itrT >>= k) :
     thread_rel sp cid tid r_diff src tgt
  | thread_rel_spawn src tgt r_diff tid itrS fspo m pre post varg arg bd x :
     tid ≠ 0 →
     cid ≠ tid →
     fspo = Some (@fspec_spawn _ m pre post) →
     src = ModTr.trans (tau;; tau;; itrS) →
     tgt = ModTr.trans (
       '(tid, m, varg):_ <- elim_spawnee_precond pre arg;;
       vret <- bd varg;;
       elim_spawnee_postcond post tid m vret) →
     (Own r_diff ⊢ |==> pre (tid, x) varg arg)%I →
     elim_rel sp ε itrS (bd varg) →
     thread_rel sp cid tid r_diff src tgt
  | thread_rel_yield src tgt r_diff tid itrS itrT (k: Any.t → itree lmodE Any.t) :
     (tid = 0 -> k = main_post) →
     cid ≠ tid →
     src = ModTr.trans (tau;; itrS) →
     tgt = ModTr.trans (tau;; trigger (Assume (TID(tid) ∗ YIELD(tid) ∗ winv(⊤, ⊤)));;; tau;; itrT) >>= k →
     elim_rel sp ε itrS itrT →
     thread_rel sp cid tid r_diff src tgt
  .
  
  Definition cancel_eq (x y: Any.t * Any.t) : Prop :=
    ∃ st r_s r_t,
    Any.split x.1 = Some (st,r_s) ∧ Any.split y.1 = Some (st,r_t) ∧
    x.2 = y.2.

  Definition CANCEL_GOAL md sp R (it_src it_tgt: itree crisE R) :=
    ∀ (r_i r_s r_t : Σ)
      (rs_diff : list Σ) (srcs tgts : list (itree lmodE Any.t))
      (cid : nat)
      (st : list (key * Any.t))
      (ps pt : smj)
      ktrS k ktrT
      (r : ∀ x x0, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
      (WFS: SMod.cancellable md)
      (VP: sp = sp_from md)
      (* (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md))) *)
      (CIH :
        ∀ (r_s r_t : Σ) (rs_diff : list Σ) (srcs tgts : list (itree lmodE Any.t)) 
          (cid : nat) (st : list (key * Any.t)) (ps pt : smj)
          (REL : Forall3i (thread_rel sp cid) rs_diff srcs tgts)
          (WFR: ✓ r_s)
          (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
                 TIDAUTH cid ∗ YIELDAUTH (length rs_diff)),
        r (Any.t * Any.t)%type (Any.t * Any.t)%type cancel_eq ps pt
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp_none (SMod.cancel md))) r_i))) (cid, srcs))
              (Any.pair (ModTr.alist_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i))) (cid, tgts))
              (Any.pair (ModTr.alist_encode st) r_t ↑)))
      (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
              (WFR: ✓ r_s)
              (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                     TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
              (LEN: cid < List.length srcs)
              (REL: thread_rel sp cid cid r_diff itr_s itr_t),
        gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
          (Any.t * Any.t)%type cancel_eq smj_top smj_top
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp_none (SMod.cancel md))) r_i)))
                    (cid, <[cid:=itr_s]> srcs))
              (Any.pair (ModTr.alist_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i)))
                    (cid, <[cid:=itr_t]> tgts))
              (Any.pair (ModTr.alist_encode st) r_t ↑)))
      (EQLEN : length srcs = length tgts)
      (EQLEN2 : length rs_diff = length srcs)
      (REL : ∀ i x y z, srcs !! i = Some x → tgts !! i = Some y → rs_diff !! i = Some z →
        thread_rel sp cid i z x y)
      (WFR : ✓ r_s)
      (RS : Own r_s ⊢
              |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗ 
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
      (LEN : cid < length srcs)
      (x0 : srcs !! cid = Some (ModTr.trans (x <- it_src;; ktrS x)))
      (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- it_tgt;; ktrT x);; k x))
      (x2 : rs_diff !! cid = Some ε)
      (RET : cid = 0 → k = main_post)
      (KTR : ∀ x, paco4 (elim_rel_def sp) bot4 Any.t ε (ktrS x) (ktrT x)),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp_none (SMod.cancel md))) r_i))) (cid, srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp md)) r_i))) (cid, tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑)).

End CancelDef.

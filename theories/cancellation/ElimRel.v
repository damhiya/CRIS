Require Import Common Sp.
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
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Definition NativeSpawnE (fn: string) (arg: Any.t) : itree crisE nat :=
  tid <- trigger (Spawn fn arg);; tau;;
  (* trigger (Yield tid);;; tau;; *)
  Ret tid.

Definition HoareSpawnE fn varg (fspo: option fspec) : itree crisE nat :=
  match fspo with
  | Some fsp =>
    x <- trigger (Choose (meta fsp));; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (precond fsp x varg arg));;; tau;;
    tid <- trigger (Spawn fn arg);; tau;;
    (* trigger (Yield tid);;; tau;; *)
    Ret tid
  | None =>
    NativeSpawnE fn varg
  end.

Definition NativeYieldE tid : itree crisE () :=
  my_tid <- trigger (Yield tid);; tau;;
  Ret my_tid.

Definition elim_precond {X X' : Type} Po Po' varg : itree crisE (X * X' * Any.t) :=
  '(x, arg): _ <-
    match Po with
    | inl P =>
       x <- trigger (Choose X);; tau;;
       arg <- trigger (Choose Any.t);; tau;;
       trigger (Guarantee (P x varg arg));;; tau;; tau;;
       Ret (x, arg)
    | inr x =>
       tau;; Ret (x, varg)
    end;;
  match Po' with
  | inl P' =>
     x' <- trigger (Take X');; tau;;
     varg' <- trigger (Take Any.t);; tau;;
     trigger (Assume (P' x' varg' arg));;; tau;;
     Ret (x, x', varg')
  | inr x' =>
     tau;; tau;; Ret (x, x', arg)
  end.

Definition elim_postcond {X X' : Type} Qo Qo' (x : X) (x' : X') vret' : itree crisE Any.t :=
  ret <-
    match Qo' with
    | Some Q' =>
       ret <- trigger (Choose Any.t);; tau;;
       trigger (Guarantee (Q' x' vret' ret));;; tau;; tau;; tau;;
       Ret ret
    | None =>
       tau;; tau;; Ret vret'
    end;;
  match Qo with
  | Some Q =>
     vret <- trigger (Take Any.t);; tau;;
     trigger (Assume (Q x vret ret));;; tau;;
     Ret vret
  | None =>
     Ret ret
  end.

Definition elim_spawnee_precond (X : Type) Po (arg : Any.t) : itree crisE (X * Any.t) :=
  match Po with
  | inl P =>
     x <- trigger (Take X);; tau;;
     varg <- trigger (Take Any.t);; tau;;
     trigger (Assume (P x varg arg));;; tau;;
     Ret (x, varg)
  | inr x =>
     tau;; tau;; Ret (x, arg)
  end.

Definition elim_spawnee_postcond {X : Type} Qo (x : X) (vret : Any.t) : itree crisE Any.t :=
  match Qo with
  | Some Q =>
     ret <- trigger (Choose Any.t);; tau;;
     trigger (Guarantee (Q x vret ret));;; tau;;
     Ret ret
  | None =>
     Ret vret
  end.

Variant elim_rel_def
    (sp : sp_type)
    (self : ∀ T, Σ → itree crisE T → itree crisE T → Prop) (T : Type)
  : Σ → itree crisE T → itree crisE T → Prop :=

(* handling void cases *)
(* | elim_choose_false itrS ktrT
  :
  elim_rel_def sp self (itrS)
                       (trigger (Choose False) >>= ktrT) *)
| elim_take_false ktrS itrT :
   elim_rel_def sp self ε (trigger (Take False) >>= ktrS) itrT
| elim_tau_take_false ktrS itrT :
   elim_rel_def sp self ε (tau;; trigger (Take False) >>= ktrS) itrT
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
| elim_rel_yield tid ktrS ktrT :
   (∀ x, self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε (trigger (Yield tid) >>= ktrS) (trigger (Yield tid) >>= ktrT)
(* handling cancellation *)
| elim_rel_spawn fn args img ktrS ktrT itrS itrT :
   (img = false → fspec_imply (fspec_flat (sp fn)) fspec_trivial) →
   itrS = NativeSpawnE fn args >>= ktrS →
   itrT = HoareSpawnE fn args ((if img then sp else sp_none) fn) >>= ktrT →
   (∀ x, self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def sp self ε itrS itrT
| elim_rel_precond (X X' : Type) Po Po' varg itrS itrT ktrT :
   (∃ P, (Po = inl P ∨ (∃ x, X = unit ∧ Po = inr x ∧ P = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
   ∃ P', (Po' = inl P' ∨ (∃ x', X' = unit ∧ Po' = inr x' ∧ P' = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
   ∀ (x : X), ∃ (x' : X'),
     (∀ arg, P x varg arg ⊢ |==> P' x' varg arg) ∧ self _ ε itrS (ktrT (x, x', varg))) →
   itrT = elim_precond Po Po' varg >>= ktrT →
   elim_rel_def sp self ε (tau;; tau;; tau;; itrS) itrT
| elim_rel_postcond (X X': Type) Qo Qo' (x: X) (x': X') vret itrS itrT ktrT :
   (∃ Q, (Qo = Some Q ∨ (Qo = None ∧ Q = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
   ∃ Q', (Qo' = Some Q' ∨ (Qo' = None ∧ Q' = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
   (∀ ret, Q' x' vret ret ⊢ |==> Q x vret ret) ∧ self _ ε itrS (ktrT vret)) →
   itrT = elim_postcond Qo Qo' x x' vret >>= ktrT →
   elim_rel_def sp self ε (tau;; tau;; itrS) itrT.
(* | elim_rel_spawnee_pre X (x : X) Po arg varg r_diff itrS itrT ktrT :
   (self _ ε itrS (ktrT (x, varg))) →
   (Own r_diff ⊢ |==> match Po with | inl P => P x varg arg | inr x' => emp end)%I →
   (itrT = @elim_spawnee_precond X Po arg >>= ktrT) →
   elim_rel_def sp self r_diff (tau;; tau;; itrS) itrT
| elim_rel_spawnee_post {X : Type} Qo (x : X) (vret : Any.t) itrS ktrT :
   (∀ vret, self _ ε itrS (ktrT vret)) →
   elim_rel_def sp self ε itrS (elim_spawnee_postcond Qo x vret >>= ktrT) *)

Definition elim_rel sp T r_diff itrS itrT :=
  paco4 (@elim_rel_def sp) bot4 T r_diff itrS itrT.

Lemma elim_rel_def_mon sp r1 r2 :
  r1 <4= r2 →
  @elim_rel_def sp r1 <4= elim_rel_def sp r2.
Proof using.
  intros ??????PR; destruct PR; eauto using @elim_rel_def.
  - eapply elim_rel_precond; eauto; des_safe.
    esplits; eauto; i; specialize (H2 x). des; eauto.
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
    des_safe. esplits; et. i. specialize (H3 x).
    des_safe. esplits; et.
    eapply rclo4_clo'; cycle 1.
    + econs; [eapply H4|]; et.
    + eauto using rclo4.
  - eapply elim_rel_postcond; i; et.
    des_safe. esplits; et.
    eapply rclo4_clo'; cycle 1.
    + econs; [eapply H4|]; et.
    + eauto using rclo4.
  (* - eapply elim_rel_spawnee_pre; i; eauto.
    esplits; et.
    eapply rclo4_clo'; cycle 1.
    + econs; [eapply H1|]; et.
    + eauto using rclo4. *)
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
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
  rewrite SBRed.spawn.
  rewrite MSK. f_equal.
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

Lemma MIRed_HoareSpawn prog fspo fn varg :
  inline_body prog (SModTr.HoareSpawn fn varg fspo) = HoareSpawnE fn varg fspo.
Proof using.
  destruct fspo; cycle 1.
  { s. rewrite MIRed_NativeSpawn. et. }
  rewrite /SModTr.HoareSpawn /HoareSpawnE. ired.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite -(bind_ret_r (trigger _)) MIRed.spawn. f_equal.
  { by rewrite bind_ret_r. }
  extensionalities. do 2 f_equal.
  by rewrite MIRed.ret.
Qed.

Lemma MIRed_NativeYield prog tid :
  inline_body prog (trigger (Yield tid)) = NativeYieldE tid.
Proof using.
  rewrite -(bind_ret_r (trigger _)) /NativeYieldE.
  rewrite MIRed.yield. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ret. et.
Qed.

Definition fspo_pre (fspo: option fspec) : ((meta (fspec_flat fspo)) → _) + (meta (fspec_flat fspo)):=
  match fspo with
  | Some fsp => inl (precond fsp)
  | None => inr ()
  end.

Definition fspo_post (fspo: option fspec) : option ((meta (fspec_flat fspo)) → _) :=
  match fspo with
  | Some fsp => Some (postcond fsp)
  | None => None
  end.

Lemma if_simpl X (b: bool) (x: X):
  (if b then x else x) = x.
Proof using. destruct b; et. Qed.

Lemma MIRed_HoareFun
    (md : SMod.t) (sp : sp_type) (img : bool) (msk : string → bool) (scp : list string)
    (bd : fbody) (fspo : option fspec) (arg : Any.t)
    (fn : string) :
  SMod.wf md →
  alist_find (Some fn) (SMod.fnsems md) = Some (img, msk, scp, (fspo, bd)) →
  inline_body
    (sandboxed_prog (SMod.to_mod sp md))
    (SB.sandbox_body (img, msk, scp,
      SModTr.HoareFun fspo (SModTr.trans (if img then sp else sp_none) ∘ bd)) arg) =
  '(x, varg) : _ <- @elim_spawnee_precond _ (fspo_pre fspo) arg;;
  vret <-
    inline_body
      (sandboxed_prog (SMod.to_mod sp md))
      (SB.sandbox img msk scp (SModTr.trans (if img then sp else sp_none) (bd varg)));;
  elim_spawnee_postcond (fspo_post fspo) x vret.
Proof using.
  intros Hwf Hfind.
  rewrite /SModTr.HoareFun /elim_spawnee_precond /elim_spawnee_postcond /=.
  destruct fspo as [fsp|]; subst; ired.
  { rewrite /SB.sandbox_body SBRed.bind SBRed.take /=.
    destruct img; cycle 1; ss.
    { hexploit (Hwf (Some fn)); eauto; ss. }
    rewrite MIRed.core; f_equal.
    extensionalities x; ired; do 2 f_equal.
    rewrite SBRed.bind SBRed.take MIRed.core; f_equal.
    extensionalities y; ired; do 2 f_equal.
    rewrite SBRed.bind SBRed.Assume MIRed.ag; f_equal.
    extensionalities z; destruct z; ired.
    do 2 f_equal.
    rewrite SBRed.bind MIRed.bind; f_equal.
    extensionalities vret.
    rewrite SBRed.bind SBRed.choose MIRed.core; f_equal.
    extensionalities ret; ired; do 2 f_equal.
    rewrite SBRed.bind SBRed.Guarantee MIRed.ag; f_equal.
    extensionalities z; destruct z; do 2 f_equal.
    rewrite SBRed.ret MIRed.ret //.
  }
  rewrite /SB.sandbox_body //= SBRed.tau MIRed.tau.
  do 4 f_equal.
Qed.


Lemma MIRed_HoareCall md sp fn varg
  (img img0: bool) (msk msk0:_→bool) scp scp0 fspo fspo0 bd0
  (WF: SMod.wf md)
  (VP: valid_sp md sp)
  (IN: msk fn)
  (SP: fspo = if img then sp fn else None)
  (FIND: alist_find (Some fn) (SMod.fnsems md) = Some (img0, msk0, scp0, (fspo0, bd0)))
  :
  inline_body (sandboxed_prog (SMod.to_mod sp md)) (SB.sandbox img msk scp (SModTr.HoareCall fn varg fspo))
  =
  (* head *)
  '(x,x0,arg):_ <- elim_precond (fspo_pre fspo) (fspo_pre fspo0) varg ;;
  (* body *)
  vret0 <- inline_body (sandboxed_prog (SMod.to_mod sp md)) 
                       (SB.sandbox img0 msk0 scp0 (SModTr.trans (if img0 then sp else sp_none) (bd0 arg)));;
  (* tail *)
  elim_postcond (fspo_post fspo) (fspo_post fspo0) x x0 vret0.
Proof using.
  unfold SModTr.HoareCall.
  rewrite /elim_precond /elim_postcond.
  destruct fspo eqn: E; subst; s; ired.
  { rewrite SBRed.bind SBRed.choose MIRed.core.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.choose MIRed.core.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.Guarantee MIRed.ag.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.call. destruct (msk fn); ss.
    rewrite MIRed.call {2}/sandboxed_prog.
    ired. rewrite alist_find_map_snd FIND. s. ired.
    rewrite /SB.sandbox_body /SModTr.trans_body. s. do 2 f_equal.
    rewrite /SModTr.HoareFun.
    destruct fspo0; ss; ired.
    { destruct img0; cycle 1.
      { exploit WF; et. ss. }
      rewrite SBRed.bind SBRed.take. s. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.take. s. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind. ired. rewrite MIRed.bind.
      f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.choose. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Guarantee. ired. rewrite MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret. ired. rewrite MIRed.tau. do 4 f_equal.
      rewrite SBRed.bind SBRed.take.    
      destruct img; ss. rewrite MIRed.core.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret MIRed.ret. et.
    }
    { rewrite MIRed.bind SBRed.tau MIRed.tau.
      ired; do 4 f_equal. f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.take. destruct img; ss.
      rewrite MIRed.tau MIRed.core. do 5 f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret MIRed.ret. et.
    }
  }
  {
    rewrite SBRed.call. destruct (msk fn); ss.
    rewrite -(bind_ret_r (trigger _)) MIRed.call {2}/sandboxed_prog.
    ired. rewrite alist_find_map_snd FIND. s. ired.
    rewrite /SB.sandbox_body /SModTr.trans_body /SModTr.HoareFun.
    s. do 2 f_equal.
    destruct fspo0; ss; ired.
    { destruct img0; cycle 1.
      { exploit WF; et. ss. }
      rewrite SBRed.bind SBRed.take. s. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.take. s. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind. ired. rewrite MIRed.bind.
      f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.choose. ired. rewrite MIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Guarantee. ired. rewrite MIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret. ired. rewrite MIRed.tau. do 4 f_equal.
      rewrite MIRed.ret. et.
    }
    { rewrite MIRed.bind SBRed.tau MIRed.tau ?bind_tau.
      do 5 f_equal. extensionalities. ired.
      rewrite MIRed.tau MIRed.ret. et.
    }
  }
(*SLOW*)Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto 6 with paco.

Lemma elim_rel_cancel (md: SMod.t) T sp img msk scp (itr: itree _ T)
  (WF: SMod.wf md)
  (VP: valid_sp md sp)
  (PARAM: ∃ fno, has_param md fno img msk scp)
  :
  @elim_rel sp T ε
    (inline_body (sandboxed_prog (SMod.to_mod sp_none (SMod.cancel md))) 
      (SB.sandbox img msk scp (SModTr.trans sp_none itr)))
    (inline_body (sandboxed_prog (SMod.to_mod sp md)) 
      (SB.sandbox img msk scp (SModTr.trans (if img then sp else sp_none) itr))).
Proof using.
  ginit. revert T itr img msk scp VP PARAM. gcofix CIH. i.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SBRed.ret !MIRed.ret. estep 1.
  - rewrite !SRed.tau !SBRed.tau !MIRed.tau. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Assume. des_ifs; ired.
    + rewrite !MIRed.ag. estep 2; edone.
    + rewrite !MIRed.core. estep 1.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.AssumePrecise.
    rewrite !MIRed.ag. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Guarantee !MIRed.ag.
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
      erewrite MIRed_HoareCall; et; cycle 1.
      { destruct img; et. }
      rewrite SBRed.call E -(bind_ret_r (trigger _)) MIRed.call.
      rewrite {2}/sandboxed_prog. s. rewrite !alist_find_map_snd E0. s. ired.
      rewrite /SB.sandbox_body /SModTr.trans_body. s.
      rewrite SBRed.tau bind_tau MIRed.tau ?bind_tau.
      rewrite !if_simpl. s. rewrite MIRed.bind. ired.
      gstep. eapply elim_rel_precond; et.
      exists (precond (fspec_flat ((if img then sp else sp_none) fn))). split.
      { destruct img; et. destruct (sp fn); et. }
      exists (precond (fspec_flat fsp0)). split.
      { destruct fsp0; et. }
      assert (I: fspec_imply (fspec_flat (sp_from md fn)) (fspec_flat ((if img then sp else sp_none) fn))).
      { etrans; [eapply VP|]. destruct img; try refl. eapply VP; eauto 6. }
      i. specialize (I x). des.
      revert x0 PRE POST.
      rewrite {1 2 3}/sp_from /to_sp !alist_find_map_snd !E0. s. i.
      exists x0. split; et.
      rewrite ?SBRed.tau ?MIRed.tau ?bind_tau.

      ired. guclo elim_rel_bindC_spec. econs.
      { edone. }

      i. ired. rewrite MIRed.tau MIRed.ret. ired.
      gstep. eapply elim_rel_postcond; et.
      exists (postcond (fspec_flat ((if img then sp else sp_none) fn))). split.
      { destruct img; et. destruct (sp fn); et. }
      exists (postcond (fspec_flat fsp0)). split.
      { destruct fsp0; et. }
      split.
      { i. rewrite -POST. et. }

      edone.
    }
    
    (* spawn case *)
    {
      rewrite !SRed.bind !SBRed.bind !SRed.spawn !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. rewrite SBRed_NativeSpawn. estep 2.
      destruct (msk fn) eqn: E; cycle 1.
      { rewrite /triggerUB // MIRed.core. ired. estep 1. }
      rewrite MIRed_NativeSpawn SBRed_HoareSpawn; et; cycle 1.
      { i. destruct img; ss. }
      rewrite MIRed_HoareSpawn.
      gstep. eapply elim_rel_spawn; et.
      { i. subst. eapply VP. eauto 6. }
      i. edone.
    }

    (* yield case *)
    { rewrite !SRed.bind !SRed.yield !SBRed.bind !SBRed.tau !SBRed.yield. ired.
      rewrite !MIRed.tau !MIRed.yield. estep 4.
      edone.
    }

  - rewrite !SRed.bind !SRed.pg !SBRed.bind. destruct s.
    + rewrite SBRed.put. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2. edone.
    + rewrite SBRed.get. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2. edone.
  - rewrite !SRed.bind !SRed.core !SBRed.bind. destruct e.
    + rewrite SBRed.choose !MIRed.core. estep 2. edone.
    + rewrite SBRed.take. destruct (_ || _) eqn: E; cycle 1.
      { ired. rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2. edone.
    + rewrite SBRed.io !MIRed.core. estep 2. edone.
(*SLOW*)Qed.

End ELIM_REL.
Hint Resolve cpn4_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Section CancelDef.
  Context `{Σ: GRA}.

  Variant thread_rel sp : nat → Σ → itree lmodE Any.t → itree lmodE Any.t → Prop :=
  | thread_rel_body itrS itrT src tgt r_diff tid (k: Any.t → itree lmodE Any.t)
      (RET: tid = 0 -> k = λ x, Ret x)
      (REL: @elim_rel Σ sp Any.t r_diff itrS itrT)
      (SRC: src = ModTr.trans itrS)
      (TGT: tgt = ModTr.trans itrT >>= k) :
     thread_rel sp tid r_diff src tgt
  | thread_rel_spawn src tgt r_diff tid itrS fspo varg arg bd x :
     tid ≠ 0 →
     src = ModTr.trans (tau;; tau;; itrS) →
     tgt = ModTr.trans (
       x <- elim_spawnee_precond (fspo_pre fspo) arg;;
       let (m, varg) := x in
       vret <- bd varg;;
       elim_spawnee_postcond (fspo_post fspo) m vret) →
     (Own r_diff ⊢
       |==> match fspo_pre fspo with | inl P => P x varg arg | inr x' => ⌜arg = varg⌝ end)%I →
     elim_rel sp ε itrS (bd varg) →
     thread_rel sp tid r_diff src tgt.

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
      (WFS: SMod.wf md)
      (VP: valid_sp md sp)
      (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
      (CIH :
        ∀ (r_s r_t : Σ) (rs_diff : list Σ) (srcs tgts : list (itree lmodE Any.t)) 
          (cid : nat) (st : list (key * Any.t)) (ps pt : smj)
          (REL : Forall3i (thread_rel sp) rs_diff srcs tgts)
          (WFR: ✓ r_s)
          (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t),
        r (Any.t * Any.t)%type (Any.t * Any.t)%type cancel_eq ps pt
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp_none (SMod.cancel md))) r_i))) (cid, srcs))
              (Any.pair (ModTr.alist_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i))) (cid, tgts))
              (Any.pair (ModTr.alist_encode st) r_t ↑)))
      (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ) tid
              (WFR: ✓ r_s)
              (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t)
              (LEN: cid < List.length srcs)
              (REL: thread_rel sp cid r_diff itr_s itr_t),
              (* (REL: elim_rel sp r_diff itr_s itr_t), *)
        gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
          (Any.t * Any.t)%type cancel_eq smj_top smj_top
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp_none (SMod.cancel md))) r_i)))
                    (tid, <[cid:=itr_s]> srcs))
              (Any.pair (ModTr.alist_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i)))
                    (tid, <[cid:=itr_t]> tgts))
              (Any.pair (ModTr.alist_encode st) r_t ↑)))
      (EQLEN : length srcs = length tgts)
      (EQLEN2 : length rs_diff = length srcs)
      (REL : ∀ i x y z, srcs !! i = Some x → tgts !! i = Some y → rs_diff !! i = Some z →
        thread_rel sp i z x y)
      (WFR : ✓ r_s)
      (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t)
      (LEN : cid < length srcs)
      (x0 : srcs !! cid = Some (ModTr.trans (x <- it_src;; ktrS x)))
      (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- it_tgt;; ktrT x);; k x))
      (x2 : rs_diff !! cid = Some ε)
      (RET : cid = 0 → k = λ x : Any.t, Ret x)
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

Require Import Common Sp.
Require Import SMod HMod Mod SModTr HModTr ModTr.
Require Import HModInline Tactics SimGlobal.
From iris.proofmode Require Export proofmode.

Set Implicit Arguments.

Section CancelLib.
  Context `{Σ: GRA}.

  Definition sp_from (md: SMod.t) : sp_type :=
    to_sp (List.map (map_snd (fst ∘ snd)) md.(SMod.fnsems)).

  Definition smod_wf (md: SMod.t) :=
    ∀ fno img msk scp fspo bd
        (FIND: alist_find fno (SMod.fnsems md) = Some (img, msk, scp, (fspo, bd)))
        (COND: fno = None ∨ img = false),
      fspo = None.

  Definition valid_param (md: SMod.t) img msk scp :=
    ∃ fno sbd, alist_find fno (SMod.fnsems md) = Some (img, msk, scp, sbd).

  Definition has_trivial_spec (md: SMod.t) (fn: string) : Prop :=
    ∃ msk scp, valid_param md false msk scp ∧ msk fn.

  Definition valid_sp (md: SMod.t) (sp: sp_type) : Prop :=
    sp_imply (sp_from md) sp ∧
    ∀ fn (NS: has_trivial_spec md fn), fspec_imply (fspec_flat (sp fn)) fspec_trivial.
  
  Definition Forall2i X Y (R: nat -> X -> Y -> Prop) (xs: list X) (ys: list Y) :=
    length xs = length ys ∧
    ∀ i x y (EQx: xs !! i = Some x) (EQy: ys !! i = Some y),
      R i x y.

  Lemma Forall2i_nth
    X Y (xs: list X) (ys: list Y) (R: nat -> X -> Y -> Prop) i
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

  Lemma list_lookup_length {X} (x: X) l:
    (l ++ [x]) !! (base.length l) = Some x.
  Proof using.
    eapply lookup_snoc_Some; right; eauto.
  Qed.

End CancelLib.

Section ELIM_REL.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Definition NativeSpawnE (fn: string) (arg: Any.t) : itree hmodE nat :=
  tid <- trigger (Spawn fn arg);; tau;;
  trigger (Yield tid);;; tau;;
  Ret tid.

Definition HoareSpawnE fn varg (fspo: option fspec) : itree hmodE nat :=
  match fspo with
  | Some fsp =>
    x <- trigger (Choose (meta fsp));; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (precond fsp x varg arg));;; tau;;
    tid <- trigger (Spawn fn arg);; tau;;
    trigger (Yield tid);;; tau;;
    Ret tid
  | None =>
    NativeSpawnE fn varg
  end.

Definition NativeYieldE tid : itree hmodE nat :=
  my_tid <- trigger (Yield tid);; tau;;
  Ret my_tid.

Definition elim_precond {X X': Type} Po Po' varg : itree hmodE (X * X' * Any.t)
  :=
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
      Ret (x, x', arg)
  end.

Definition elim_postcond X Qo X' Qo' (x: X) (x': X') vret' : itree hmodE Any.t
  :=
  ret <-
  match Qo' with
  | Some Q' =>
    ret <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (Q' x' vret' ret));;; tau;; tau;; tau;;
    Ret ret
  | None  =>
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

Variant elim_rel_def (sp: sp_type)
  (self: ∀ T, itree hmodE T -> itree hmodE T -> Prop)
  T : itree hmodE T -> itree hmodE T -> Prop
:=

(* handling void cases *)

| elim_choose_false itrS ktrT
  :
  elim_rel_def sp self (itrS)
                       (trigger (Choose False) >>= ktrT)

| elim_take_false ktrS itrT
  :
  elim_rel_def sp self (trigger (Take False) >>= ktrS)
                       (itrT)

| elim_tau_take_false ktrS itrT
  :
  elim_rel_def sp self (tau;; trigger (Take False) >>= ktrS)
                       (itrT)
                       
(* handling normal cases *)

| elim_rel_ret v
  :
  elim_rel_def sp self  (Ret v) (Ret v)

| elim_rel_tau itrS itrT
    (ITR: self _ itrS itrT)
  :
  elim_rel_def sp self (tau;; itrS) (tau;; itrT)

| elim_rel_core {R} (e: coreE R) ktrS ktrT
    (KTR: forall (x: R), self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

| elim_rel_pg {R} (e: pgE R) ktrS ktrT
    (KTR: forall (x: R), self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

| elim_rel_ag {R} (e: agE R) ktrS ktrT
    (KTR: forall (x: R), self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

| elim_rel_yield tid ktrS ktrT
    (KTR: forall x, self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self (trigger (Yield tid) >>= ktrS)
                       (trigger (Yield tid) >>= ktrT)

(* handling cancellation *)

| elim_rel_spawn fn args img ktrS ktrT itrS itrT
    (IMG: img = false → fspec_imply (fspec_flat (sp fn)) fspec_trivial)
    (EQS: itrS = NativeSpawnE fn args >>= ktrS)
    (EQT: itrT = HoareSpawnE fn args ((if img then sp else sp_none) fn) >>= ktrT)
    (KTR: forall x, self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self itrS itrT

| elim_rel_precond (X X': Type) Po Po' varg itrS itrT ktrT
    (KTR:
      ∃ P, (Po = inl P ∨ (∃ x, X = unit ∧ Po = inr x ∧ P = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
      ∃ P', (Po' = inl P' ∨ (∃ x', X' = unit ∧ Po' = inr x' ∧ P' = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
      ∀ x:X, ∃ x':X',
        (∀ arg, P x varg arg ⊢ |==> P' x' varg arg) ∧
        self _ itrS (ktrT (x, x', varg)))
    (TGT: itrT = elim_precond Po Po' varg >>= ktrT)
  :
  elim_rel_def sp self (tau;; itrS) itrT

| elim_rel_postcond (X X': Type) Qo Qo' (x: X) (x': X') vret itrS itrT ktrT
    (KTR:
      ∃ Q, (Qo = Some Q ∨ (Qo = None ∧ Q = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
      ∃ Q', (Qo' = Some Q' ∨ (Qo' = None ∧ Q' = λ _ varg arg, ⌜varg = arg⌝%I)) ∧
      (∀ ret, Q' x' vret ret ⊢ |==> Q x vret ret) ∧
      self _ itrS (ktrT vret))
    (TGT: itrT = elim_postcond Qo Qo' x x' vret >>= ktrT)
  :
  elim_rel_def sp self (tau;; tau;; itrS) itrT
.

Definition elim_rel sp T itrS itrT :=
  paco3 (@elim_rel_def sp) bot3 T itrS itrT.

Lemma elim_rel_def_mon sp r1 r2
  (REL: r1 <3= r2)
:
@elim_rel_def sp r1 <3= elim_rel_def sp r2.
Proof.
  i. destruct PR; eauto using @elim_rel_def.
  - eapply elim_rel_precond; et; des_safe.
    esplits; et. i. specialize (KTR1 x). des; et.
  - eapply elim_rel_postcond; et; des_safe.
    esplits; et.
Qed.

Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Variant elim_rel_bindC
  (r: ∀ T, itree hmodE T -> itree hmodE T -> Prop)
  T : itree hmodE T -> itree hmodE T -> Prop
  :=
| elim_rel_bindC_intro R
    itrS itrT ktrS ktrT
    (REL: r R itrS itrT)
    (RELK: ∀v, r T (ktrS v) (ktrT v))
  :
  elim_rel_bindC r (itrS >>= ktrS) (itrT >>= ktrT)
.

Lemma elim_rel_bindC_mon:
  monotone3 elim_rel_bindC.
Proof.
  ii. destruct IN; econs; eauto.
Qed.

Lemma elim_rel_bindC_spec sp:
  elim_rel_bindC <4= gupaco3 (@elim_rel_def sp) (cpn3 (@elim_rel_def sp)).
Proof.
  eapply wrespect3_uclo; eauto with paco.
  econs; [apply elim_rel_bindC_mon|].
  i. inv PR. apply GF in REL.
  inv REL; grind; eauto 7 using rclo3, elim_rel_def, elim_rel_bindC with paco.
  - eapply elim_rel_precond; i; et.
    des_safe. esplits; et. i. specialize (KTR1 x).
    des_safe. esplits; et.
    eapply rclo3_clo'; cycle 1.
    + econs; [eapply KTR2|]; et.
    + eauto using rclo3.
  - eapply elim_rel_postcond; i; et.
    des_safe. esplits; et.
    eapply rclo3_clo'; cycle 1.
    + econs; [eapply KTR2|]; et.
    + eauto using rclo3.
Qed.

Lemma SBRed_NativeSpawn
  img msk scp fn varg
  :
  SB.sandbox img msk scp (SModTr.NativeSpawn fn varg) =
    if msk fn then SModTr.NativeSpawn fn varg else triggerUB.
Proof.
  rewrite /SModTr.NativeSpawn SBRed.bind SBRed.spawn.
  des_ifs; cycle 1.
  { rewrite /triggerUB. s. ired. f_equal. extensionalities. ss. }
  f_equal; extensionalities; rewrite SBRed.bind SBRed.yield SBRed.ret; et.
Qed.

Lemma SBRed_HoareSpawn (img: bool) (msk: _→bool) scp fn varg fspo
  (MSK: msk fn)
  (IMG: (negb img) → fspo = None)
  :
  SB.sandbox img msk scp (SModTr.HoareSpawn fn varg fspo) =
    SModTr.HoareSpawn fn varg fspo.
Proof.
  rewrite /SModTr.HoareSpawn. destruct fspo; cycle 1.
  { rewrite SBRed_NativeSpawn MSK. et. }
  destruct img; cycle 1.
  { exploit IMG; et. i. ss. }
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.spawn.
  rewrite MSK. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.yield. f_equal. extensionalities.
  rewrite SBRed.ret. ss.
Qed.

Lemma HIRed_NativeSpawn
  prog fn varg
  :
  inline_body prog (SModTr.NativeSpawn fn varg) = NativeSpawnE fn varg.
Proof.
  rewrite /SModTr.NativeSpawn /NativeSpawnE. ired.
  rewrite HIRed.spawn. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.yield HIRed.ret. et.
Qed.

Lemma HIRed_HoareSpawn
  prog fspo fn varg
  :
  inline_body prog (SModTr.HoareSpawn fn varg fspo) = HoareSpawnE fn varg fspo.
Proof.
  destruct fspo; cycle 1.
  { s. rewrite HIRed_NativeSpawn. et. }
  rewrite /SModTr.HoareSpawn /HoareSpawnE. ired.
  rewrite HIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.spawn. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.yield. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.ret. et.
Qed.

Lemma HIRed_NativeYield
  prog tid
  :
  inline_body prog (trigger (Yield tid)) = NativeYieldE tid.
Proof.
  rewrite -(bind_ret_r (trigger _)) /NativeYieldE.
  rewrite HIRed.yield. f_equal. extensionalities. do 2 f_equal.
  rewrite HIRed.ret. et.
Qed.

Definition fspo_pre (fspo: option fspec) : ((meta (fspec_flat fspo))→_) + (meta (fspec_flat fspo)):=
  match fspo with
  | Some fsp => inl (precond fsp)
  | None => inr ()
  end.

Definition fspo_post (fspo: option fspec) : option ((meta (fspec_flat fspo))→_) :=
  match fspo with
  | Some fsp => Some (postcond fsp)
  | None => None
  end.

Lemma if_simpl X (b: bool) (x: X):
  (if b then x else x) = x.
Proof. destruct b; et. Qed.

Lemma HIRed_HoareCall md sp fn varg
  (img img0: bool) (msk msk0:_→bool) scp scp0 fspo fspo0 bd0
  (WF: smod_wf md)
  (VP: valid_sp md sp)
  (IN: msk fn)
  (SP: fspo = if img then sp fn else None)
  (FIND: alist_find (Some fn) (SMod.fnsems md) = Some (img0, msk0, scp0, (fspo0, bd0)))
  :
  inline_body (sandboxed_prog (SMod.to_hmod sp md)) (SB.sandbox img msk scp (SModTr.HoareCall fn varg fspo))
  =
  (* head *)
  '(x,x0,arg):_ <- elim_precond (fspo_pre fspo) (fspo_pre fspo0) varg ;;
  (* body *)
  vret0 <- inline_body (sandboxed_prog (SMod.to_hmod sp md)) 
                       (SB.sandbox img0 msk0 scp0 (SModTr.trans (if img0 then sp else sp_none) (bd0 arg)));;
  (* tail *)
  elim_postcond (fspo_post fspo) (fspo_post fspo0) x x0 vret0.
Proof.
  unfold SModTr.HoareCall.
  rewrite /elim_precond /elim_postcond.
  destruct fspo eqn: E; subst; s; ired.
  { rewrite SBRed.bind SBRed.choose HIRed.core.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.choose HIRed.core.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.Guarantee HIRed.ag.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite SBRed.bind SBRed.call. destruct (msk fn); ss.
    rewrite HIRed.call {2}/sandboxed_prog.
    ired. rewrite alist_find_map_snd FIND. s. ired.
    rewrite /SB.sandbox_body /SModTr.trans_body. s. do 2 f_equal.
    rewrite /SModTr.HoareFun.
    destruct fspo0; ss; ired.
    { destruct img0; cycle 1.
      { exploit WF; et. ss. }
      rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind. ired. rewrite HIRed.bind.
      f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.choose. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Guarantee. ired. rewrite HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret. ired. rewrite HIRed.tau. do 4 f_equal.
      rewrite SBRed.bind SBRed.take.    
      destruct img; ss. rewrite HIRed.core.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret HIRed.ret. et.
    }
    { rewrite HIRed.bind.
      f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.take. destruct img; ss.
      rewrite HIRed.tau HIRed.core. do 5 f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret HIRed.ret. et.
    }
  }
  {
    rewrite SBRed.call. destruct (msk fn); ss.
    rewrite -(bind_ret_r (trigger _)) HIRed.call {2}/sandboxed_prog.
    ired. rewrite alist_find_map_snd FIND. s. ired.
    rewrite /SB.sandbox_body /SModTr.trans_body /SModTr.HoareFun.
    s. do 2 f_equal.
    destruct fspo0; ss; ired.
    { destruct img0; cycle 1.
      { exploit WF; et. ss. }
      rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.bind. ired. rewrite HIRed.bind.
      f_equal. extensionalities. ired.
      rewrite SBRed.bind SBRed.choose. ired. rewrite HIRed.core.
      f_equal. extensionalities. ired. do 2 f_equal.
      rewrite SBRed.bind SBRed.Guarantee. ired. rewrite HIRed.ag.
      f_equal. extensionalities. do 2 f_equal.
      rewrite SBRed.ret. ired. rewrite HIRed.tau. do 4 f_equal.
      rewrite HIRed.ret. et.
    }
    { rewrite HIRed.bind.
      f_equal. extensionalities. ired.
      rewrite HIRed.tau HIRed.ret. et.
    }
  }
(*SLOW*)Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto 6 with paco.

Hint Unfold valid_param has_trivial_spec: core.

Lemma elim_rel_cancel (md: SMod.t) T sp img msk scp (itr: itree _ T)
  (WF: smod_wf md)
  (VP: valid_sp md sp)
  (PARAM: valid_param md img msk scp)
  :
  @elim_rel sp T
    (inline_body (sandboxed_prog (SMod.to_hmod sp_none (SMod.cancel md))) 
      (SB.sandbox img msk scp (SModTr.trans sp_none itr)))
    (inline_body (sandboxed_prog (SMod.to_hmod sp md)) 
      (SB.sandbox img msk scp (SModTr.trans (if img then sp else sp_none) itr))).
Proof.
  ginit. revert T itr img msk scp VP PARAM. gcofix CIH. i.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SBRed.ret !HIRed.ret. estep 1.
  - rewrite !SRed.tau !SBRed.tau !HIRed.tau. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Assume. des_ifs; ired.
    + rewrite !HIRed.ag. estep 2. edone.
    + rewrite !HIRed.core. estep 1.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.AssumePrecise.
    rewrite !HIRed.ag. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Guarantee !HIRed.ag.
    estep 2. edone.
  - depdes c; s.
    (* call case *)
    {
      rewrite !SRed.bind !SBRed.bind !SRed.call !SBRed.tau !HIRed.bind !HIRed.tau.
      ired. estep 2. destruct (msk fn) eqn: E; cycle 1.
      { rewrite SBRed.call E /triggerUB // HIRed.core. ired. estep 1. }
      destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: E0; cycle 1.
      { rewrite SBRed.call E -(bind_ret_r (trigger _)) HIRed.call
                {2}/sandboxed_prog // !alist_find_map_snd E0 //.
        ired. rewrite HIRed.core. ired. estep 1. }
      destruct f as [[[img0 msk0] scp0] [fsp0 bd0]].
      erewrite HIRed_HoareCall; et; cycle 1.
      { destruct img; et. }
      rewrite SBRed.call E -(bind_ret_r (trigger _)) HIRed.call.
      rewrite {2}/sandboxed_prog. s. rewrite !alist_find_map_snd E0. s. ired.
      rewrite /SB.sandbox_body /SModTr.trans_body. s.
      rewrite !if_simpl. s. rewrite HIRed.bind. ired.
      gstep. eapply elim_rel_precond; et.
      exists (precond (fspec_flat ((if img then sp else sp_none) fn))). split.
      { destruct img; et. destruct (sp fn); et. }
      exists (precond (fspec_flat fsp0)). split.
      { destruct fsp0; et. }
      assert (I: fspec_imply (fspec_flat (sp_from md fn)) (fspec_flat ((if img then sp else sp_none) fn))).
      { etrans; [eapply VP|]. destruct img; try refl. eapply VP; et. }
      i. specialize (I x). des.
      revert x0 PRE POST.
      rewrite {1 2 3}/sp_from /to_sp !alist_find_map_snd !E0. s. i.
      exists x0. split; et.
      ired. guclo elim_rel_bindC_spec. econs.
      { edone. }

      i. ired. rewrite HIRed.tau HIRed.ret. ired.
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
      rewrite !SRed.bind !SBRed.bind !SRed.spawn !SBRed.tau !HIRed.bind !HIRed.tau.
      ired. rewrite SBRed_NativeSpawn. estep 2.
      destruct (msk fn) eqn: E; cycle 1.
      { rewrite /triggerUB // HIRed.core. ired. estep 1. }
      rewrite HIRed_NativeSpawn SBRed_HoareSpawn; et; cycle 1.
      { i. destruct img; ss. }
      rewrite HIRed_HoareSpawn.
      gstep. eapply elim_rel_spawn; et.
      { i. subst. eapply VP. et. }
      i. edone.
    }

    (* yield case *)
    { rewrite !SRed.bind !SRed.yield !SBRed.bind !SBRed.tau !SBRed.yield. ired.
      rewrite !HIRed.tau !HIRed.yield. estep 4.
      edone.
    }

  - rewrite !SRed.bind !SRed.pg !SBRed.bind. destruct s.
    + rewrite SBRed.put. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite HIRed.core. estep 1. }
      rewrite !HIRed.pg. estep 2. edone.
    + rewrite SBRed.get. destruct (existsb _ _) eqn: E; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite HIRed.core. estep 1. }
      rewrite !HIRed.pg. estep 2. edone.
  - rewrite !SRed.bind !SRed.core !SBRed.bind. destruct e.
    + rewrite SBRed.choose !HIRed.core. estep 2. edone.
    + rewrite SBRed.take. destruct (_ || _) eqn: E; cycle 1.
      { ired. rewrite HIRed.core. estep 1. }
      rewrite !HIRed.core. estep 2. edone.
    + rewrite SBRed.io !HIRed.core. estep 2. edone.
(*SLOW*)Qed.

End ELIM_REL.
Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Section CancelDef.
  Context `{Σ: GRA}.

  Variant thread_rel sp tid src tgt : Prop :=
  | thread_rel_body itrS itrT (k: Any.t → itree modE Any.t)
      (RET: tid = 0 -> k = λ x, Ret x)
      (REL: @elim_rel Σ sp Any.t itrS itrT)
      (SRC: src = HModTr.trans itrS)
      (TGT: tgt = HModTr.trans itrT >>= k)
  .

  Definition cancel_eq (x y: Any.t * Any.t) : Prop :=
    ∃ st r_s r_t,
    Any.split x.1 = Some (st,r_s) ∧ Any.split y.1 = Some (st,r_t) ∧
    x.2 = y.2.

  Definition CANCEL_GOAL md sp R (it_src it_tgt: itree hmodE R)
  :=
  ∀ (rs0: Σ) r_s r_t srcs tgts cid st ps pt ktrS k ktrT
    (r: ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: smod_wf md)
    (VP: valid_sp md sp)
    (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
    (CIH :
     ∀ (r_s r_t : Σ) (srcs tgts : list (itree modE Any.t)) 
       (cid : nat) (st : list (key * Any.t)) (ps pt : smj)
       (REL: Forall2i (thread_rel sp) srcs tgts)
       (WFR: ✓ r_s)
       (RS: Own r_s ⊢ |==> Own r_t),
     r (Any.t * Any.t)%type (Any.t * Any.t)%type cancel_eq ps pt
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
          (Any.pair (HModTr.alist_encode st) r_s ↑))
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp md)) rs0))) (cid, tgts))
          (Any.pair (HModTr.alist_encode st) r_t ↑)))
    (KEY: ∀ itrS' itrT' st (r_s r_t: Σ) tid
             (WFR: ✓ r_s)
             (RS: Own r_s ⊢ |==> Own r_t)
             (LEN: cid < List.length srcs)
             (REL: elim_rel sp itrS' itrT'),
     gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type
       (Any.t * Any.t)%type cancel_eq smj_top smj_top
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp_none (SMod.cancel md))) rs0)))
                 (tid, <[cid:=interpV HModTr.handle_hmodE itrS']> srcs))
          (Any.pair (HModTr.alist_encode st) r_s ↑))
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp md)) rs0)))
                 (tid, <[cid:=x_ <- interpV HModTr.handle_hmodE itrT';; k x_]> tgts))
          (Any.pair (HModTr.alist_encode st) r_t ↑)))
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i x y, srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> Own r_t)
    (LEN : cid < length srcs)
    (x0 : srcs !! cid = Some (HModTr.trans (x <- it_src;; ktrS x)))
    (x1 : tgts !! cid = Some (x <- HModTr.trans (x <- it_tgt;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR : ∀ x, paco3 (elim_rel_def sp) bot3 Any.t (ktrS x) (ktrT x)),

  gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (HModTr.alist_encode st) r_s ↑))
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp md)) rs0))) (cid, tgts))
       (Any.pair (HModTr.alist_encode st) r_t ↑)).

End CancelDef.

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

Definition HoareSpawnE (fspo: option fspec) (sspo: bool) fn varg N : itree crisE nat :=
  match fspo, sspo with
  | Some fsp, true =>
      x <- trigger (Choose (meta fsp));; tau;;
      arg <- trigger (Choose Any.t);; tau;;
      tid <- trigger (Spawn fn arg);; tau;;
      trigger (Assume (YIELD tid));;; tau;;
      trigger (Guarantee (YIELD tid -∗ TID tid -∗ winv (↑N, ↑N) -∗ precond fsp (N, tid) x varg arg));;; tau;;
      Ret tid
  | None, true =>
      tid <- trigger (Spawn fn varg);; tau;;
      trigger (Assume (YIELD tid));;; tau;;
      Ret tid
  | _, false =>
      tid <- trigger (Spawn fn varg);; tau;;
      Ret tid
  end.

Definition HoareYieldE (sspo: bool) N stid ntid : itree crisE () :=
  if sspo
  then
      trigger (Guarantee (TID stid ∗ YIELD ntid ∗ winv (↑N, ↑N)));;; tau;;
      trigger (Yield ntid);;; tau;;
      trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;; tau;;
      Ret tt
  else
      trigger (Yield ntid);;; tau;; Ret tt.

Lemma HoareYieldE_indep N0 N1 stid0 stid1 ntid :
  HoareYieldE false N0 stid0 ntid = HoareYieldE false N1 stid1 ntid.
Proof using. ss. Qed.

Definition HoareGetTidE (sspo: bool) stid : itree crisE nat :=
  if sspo
  then
      trigger (Guarantee (TID(stid)));;; tau;;
      tid <- trigger GetTid;; tau;;
      trigger (Assume (⌜tid = stid⌝ ∗ TID(stid)));;; tau;;
      Ret tid
  else
      tid <- trigger GetTid;; tau;; Ret tid.

Lemma HoareGetTidE_indep stid0 stid1 :
  HoareGetTidE false stid0 = HoareGetTidE false stid1.
Proof using. ss. Qed.

Definition elim_precond {X X' : Type} P P' (N: namespace) (stid: nat) (varg: Any.t) : itree crisE (namespace * nat * X * X' * Any.t) :=
  x <- trigger (Choose X);; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  (* trigger (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;; tau;; *)
  trigger (Guarantee (P (N, stid) x varg arg));;; tau;; tau;;
  '(N', stid') : _ <- trigger (Take (namespace * nat));; tau;;
  x' <- trigger (Take X');; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  (* trigger (Assume (TID stid' ∗ YIELD stid' ∗ winv (↑(N'), ↑(N'))));;; tau;; *)
  trigger (Assume (P' (N', stid') x' varg' arg));;; tau;;
  Ret (N', stid', x, x', varg').

Definition elim_postcond {X X' : Type} Q Q' (N N': namespace) (stid stid': nat) (x : X) (x' : X') (vret': Any.t) : itree crisE Any.t :=
  ret <- trigger (Choose Any.t);; tau;;
  (* trigger (Guarantee (TID stid' ∗ YIELD stid' ∗ winv (↑N', ↑N')));;; tau;; *)
  trigger (Guarantee (Q' (N', stid') x' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  (* trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;; tau;; *)
  trigger (Assume (Q (N, stid) x vret ret));;; tau;;
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

Definition elim_spawnee_precond (X : Type) P (arg : Any.t) : itree crisE (namespace * nat * X * Any.t) :=
  '(N, stid) : _ <- trigger (Take (namespace * nat));; tau;;
  x <- trigger (Take X);; tau;;
  varg <- trigger (Take Any.t);; tau;;
  (* trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;; tau;; *)
  trigger (Assume (P (N, stid) x varg arg));;; tau;;
  Ret (N, stid, x, varg).

Definition elim_spawnee_postcond {X : Type} Q (N: namespace) (stid : nat) (x : X) (vret : Any.t) : itree crisE Any.t :=
  ret <- trigger (Choose Any.t);; tau;;
  (* trigger (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;; tau;; *)
  trigger (Guarantee (Q (N, stid) x vret ret));;; tau;;
  Ret ret.

Variant elim_rel_def
    (N: namespace) (sp : specmap)
    (self : ∀ T, Σ → itree crisE T → itree crisE T → Prop) (T : Type)
  : Σ → itree crisE T → itree crisE T → Prop :=

(* handling void cases *)
| elim_take_false ktrS itrT :
   elim_rel_def N sp self ε (trigger (Take False) >>= ktrS) itrT
| elim_tau_take_false ktrS itrT :
   elim_rel_def N sp self ε (tau;; trigger (Take False) >>= ktrS) itrT
| elim_choose_false itrS ktrT :
   elim_rel_def N sp self ε itrS (trigger (Choose False) >>= ktrT)
(* handling normal cases *)
| elim_rel_ret v :
   elim_rel_def N sp self ε (Ret v) (Ret v)
| elim_rel_tau itrS itrT :
   self _ ε itrS itrT →
   elim_rel_def N sp self ε (tau;; itrS) (tau;; itrT)
| elim_rel_core {R} (e : coreE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def N sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
| elim_rel_pg {R} (e : pgE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def N sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
| elim_rel_ag {R} (e : agE R) ktrS ktrT :
   (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def N sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
(* handling cancellation *)
| elim_rel_yield tid ntid ktrS ktrT itrS itrT :
    itrS = HoareYieldE false N tid ntid >>= ktrS →
    itrT = HoareYieldE true N tid ntid >>= ktrT →
    (∀ x, self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def N sp self ε itrS itrT
| elim_rel_spawn fn args ktrS ktrT itrS itrT :
   (* (img = false → fspec_imply (fspec_flat (sp fn)) fspec_trivial) → *)
   itrS = HoareSpawnE None false fn args N >>= ktrS →
   itrT = HoareSpawnE (sp !! (speckey_fn fn)) true fn args N >>= ktrT →
   (∀ x, self _ ε (ktrS x) (ktrT x)) →
   elim_rel_def N sp self ε itrS itrT
| elim_rel_precond (X X' : Type) P P' stid varg itrS itrT ktrT :
   (∀ (x : X), ∃ (x' : X'),
     (∀ arg, P (N, stid) x varg arg ⊢ |==> P' (N, stid) x' varg arg) ∧ self _ ε itrS (ktrT (N, stid, x, x', varg))) →
   itrT = elim_precond P P' N stid varg >>= ktrT →
   elim_rel_def N sp self ε (tau;; tau;; tau;; itrS) itrT
| elim_rel_postcond (X X': Type) Q Q' (stid: nat) (x: X) (x': X') vret itrS itrT ktrT :
   ((∀ ret, Q' (N, stid) x' vret ret ⊢ |==> Q (N, stid) x vret ret) ∧ self _ ε itrS (ktrT vret)) →
   itrT = elim_postcond Q Q' N N stid stid x x' vret >>= ktrT →
   elim_rel_def N sp self ε (tau;; tau;; itrS) itrT
| elim_rel_gettid tid ktrS ktrT itrS itrT :
   itrS = HoareGetTidE false tid >>= ktrS ->
   itrT = HoareGetTidE true tid >>= ktrT ->
   (∀ x, self _ ε (ktrS x) (ktrT x)) ->
   elim_rel_def N sp self ε itrS itrT
.

Definition elim_rel N sp T r_diff itrS itrT :=
  paco4 (@elim_rel_def N sp) bot4 T r_diff itrS itrT.

Lemma elim_rel_def_mon N sp r1 r2 :
  r1 <4= r2 →
  @elim_rel_def N sp r1 <4= elim_rel_def N sp r2.
Proof using.
  intros ??????PR; destruct PR; eauto using @elim_rel_def.
  - eapply elim_rel_precond; eauto; des_safe.
    i. specialize (H0 x). des; esplits; eauto.
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

Lemma elim_rel_bindC_spec N sp :
  elim_rel_bindC <5= gupaco4 (@elim_rel_def N sp) (cpn4 (@elim_rel_def N sp)).
Proof using.
  eapply wrespect4_uclo; eauto with paco.
  econs; [apply elim_rel_bindC_mon|].
  i. inv PR. apply GF in H.
  inv H; grind; eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
  - ired. eapply elim_rel_yield with (ktrS := λ z, (x <- ktrS0 z;; ktrS x)) (ktrT := λ z, (x <- ktrT0 z;; ktrT x)); eauto.
    { ired; ss. } { ired; ss. }
    eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
  - eapply elim_rel_spawn with (ktrS := λ z, (x <- ktrS0 z;; ktrS x)) (ktrT := λ z, (x <- ktrT0 z;; ktrT x)); eauto.
    { ired; ss. }
    eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
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
  - ired. eapply elim_rel_gettid with (ktrS := λ z, (x <- ktrS0 z;; ktrS x)) (ktrT := λ z, (x <- ktrT0 z;; ktrT x)); eauto.
    { ired; ss. } { ired; ss. }
    eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
Unshelve. all: eauto.
Qed.

Lemma SBRed_NativeSpawn msk fn varg :
  SB.sandbox msk (trigger (Spawn fn varg)) =
    if msk _ (subevent _ (Spawn fn varg)) then trigger (Spawn fn varg) else triggerUB.
Proof using.
  rewrite SBRed.vis. des_ifs.
  { rewrite vis_trigger. rewrite -{2}(bind_ret_r (trigger (Spawn fn varg))).
    f_equal. extensionalities. rewrite SBRed.ret. refl. }
  { rewrite /triggerUB. ss. rewrite vis_trigger. f_equal. extensionalities. ss. }
Qed.

Lemma SBRed_HoareSpawn (msk : emask) fn varg sspo fspo N
  (MSK: ∀ x, msk _ (subevent _ (Spawn fn x)) = true)
  (IMG: img_msk msk)
  :
  SB.sandbox msk (SModTr.HoareSpawn fspo sspo fn varg N) =
    SModTr.HoareSpawn fspo sspo fn varg N.
Proof using.
  r in IMG; des.
  rewrite /SModTr.HoareSpawn. destruct fspo, sspo; cycle 1.
  { rewrite SBRed_NativeSpawn MSK. et. }
  { rewrite SBRed.bind SBRed.vis MSK vis_trigger. ired. f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l SBRed.bind SBRed.vis IMG1 vis_trigger. ired.
    f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l SBRed.ret //. }
  { rewrite SBRed_NativeSpawn MSK. et. }
  destruct f; ss.
  rewrite SBRed.bind SBRed.vis !vis_trigger IMG0. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis !vis_trigger IMG0. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis !vis_trigger MSK. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis !vis_trigger IMG1. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis !vis_trigger IMG3. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l. rewrite SBRed.ret //.
Qed.

Lemma MIRed_HoareSpawn prog fspo sspo fn varg N :
  inline_body prog (SModTr.HoareSpawn fspo sspo fn varg N) = HoareSpawnE fspo sspo fn varg N.
Proof using.
  destruct sspo; ss; cycle 1.
  { destruct fspo; ss; cycle 1.
    { rewrite -{1}(bind_ret_r (trigger (Spawn fn varg))). rewrite MIRed.spawn.
      f_equal. extensionalities. do 2 f_equal. by rewrite MIRed.ret. }
    { rewrite -{1}(bind_ret_r (trigger (Spawn fn varg))). rewrite MIRed.spawn.
      f_equal. extensionalities. do 2 f_equal. by rewrite MIRed.ret. }
  }
  destruct fspo; ss; cycle 1.
  { rewrite MIRed.bind -{1}(bind_ret_r (trigger (Spawn fn varg))) MIRed.spawn. ired.
    f_equal. extensionalities. ired. do 2 f_equal.
    rewrite MIRed.ret bind_ret_l MIRed.ag. ired.
    f_equal. extensionalities. by rewrite MIRed.ret. }
  destruct f; des; ss.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.spawn. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  by rewrite MIRed.ret.
Qed.

Lemma SBRed_HoareYield (msk: emask) sspo N stid ntid
  (MSK: msk _ (subevent _ (Yield ntid)) = true)
  (IMG: img_msk msk) :
  SB.sandbox msk (SModTr.HoareYield sspo N stid ntid) =
    SModTr.HoareYield sspo N stid ntid.
Proof using.
  r in IMG; des.
  rewrite /SModTr.HoareYield. destruct sspo; cycle 1.
  { rewrite SBRed.vis MSK vis_trigger. rewrite -{2}(bind_ret_r (trigger (Yield _))).
    f_equal. extensionalities. rewrite SBRed.ret //. }
  rewrite SBRed.bind SBRed.vis IMG3 vis_trigger. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis MSK vis_trigger. ired. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.vis IMG1 vis_trigger -{2}(bind_ret_r (trigger (Assume _))). f_equal. extensionalities.
  rewrite SBRed.ret //.
Qed.

Lemma MIRed_HoareYield prog sspo N stid ntid :
  inline_body prog (SModTr.HoareYield sspo N stid ntid) = HoareYieldE sspo N stid ntid.
Proof using.
  rewrite /SModTr.HoareYield /HoareYieldE. destruct sspo; cycle 1.
  { rewrite -{1}(bind_ret_r (trigger (Yield _))) MIRed.yield.
    f_equal. extensionalities. do 2 f_equal. rewrite MIRed.ret.
    by destruct H. }
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.yield. f_equal. extensionalities. do 2 f_equal.
  rewrite -{1}(bind_ret_r (trigger _)).
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  destruct H1. by rewrite MIRed.ret.
Qed.

Lemma SBRed_HoareGetTid (msk : emask) sspo stid
  (MSK: msk _ (subevent _ GetTid) = true)
  (IMG: img_msk msk) :
  SB.sandbox msk (SModTr.HoareGetTid sspo stid) =
    SModTr.HoareGetTid sspo stid.
Proof using.
  r in IMG. des.
  rewrite /SModTr.HoareGetTid. destruct sspo; cycle 1.
  { rewrite SBRed.vis MSK vis_trigger. rewrite -{2}(bind_ret_r (trigger _)).
    f_equal. extensionalities. rewrite SBRed.ret //. }
  rewrite SBRed.bind SBRed.vis IMG3 vis_trigger bind_bind. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis MSK vis_trigger bind_bind. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis IMG1 vis_trigger bind_bind. f_equal. extensionalities.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.ret //.
Qed.

Lemma MIRed_HoareGetTid prog sspo stid :
  inline_body prog (SModTr.HoareGetTid sspo stid) = HoareGetTidE sspo stid.
Proof using.
  rewrite /SModTr.HoareGetTid /HoareGetTidE. destruct sspo; cycle 1.
  { rewrite -{1}(bind_ret_r (trigger GetTid)) MIRed.gettid.
    f_equal. extensionalities. do 2 f_equal. rewrite MIRed.ret.
    by destruct H. }
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.gettid. f_equal. extensionalities. do 2 f_equal.
  rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
  by rewrite MIRed.ret.
Qed.

Lemma if_simpl X (b: bool) (x: X):
  (if b then x else x) = x.
Proof using. destruct b; et. Qed.

Lemma MIRed_HoareFun
    (md : SMod.t) (sp : specmap) (msk : emask)
    (bd : fbody) (fspo : option fspec) (arg : Any.t)
    (fno : option string) meta pre post:
  (SMod.fnsems md) !! fno = Some (Some (msk, (fspo, bd))) →
  img_msk msk →
  fspo = Some (@fspec_mk _ meta pre post) →
  inline_body
    (sandboxed_prog (SMod.to_mod sp md))
    (SB.sandbox_body (msk, SModTr.HoareFun fspo (λ N tid, (SModTr.trans sp N tid ∘ bd))) arg) =
  '(N, tid, x, varg) : _ <- @elim_spawnee_precond _ pre arg;;
  vret <-
    inline_body
      (sandboxed_prog (SMod.to_mod sp md))
      (SB.sandbox msk (SModTr.trans sp N tid (bd varg)));;
  elim_spawnee_postcond post N tid x vret.
Proof using.
  intros Hfind Himg Hst. r in Himg. des.
  rewrite /SModTr.HoareFun /elim_spawnee_precond /elim_spawnee_postcond /=.
  destruct fspo; ss. destruct f; ss. depdes Hst.
  rewrite /SB.sandbox_body SBRed.bind SBRed.vis /= Himg vis_trigger !bind_bind MIRed.core.
  ired; f_equal. extensionalities x; ired; do 2 f_equal.
  destruct x. ired. do 2 f_equal.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis /= Himg vis_trigger !bind_bind MIRed.core.
  ired; f_equal. extensionalities x; ired; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis /= Himg vis_trigger !bind_bind MIRed.core.
  ired; f_equal. extensionalities y; ired; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis /= Himg1 vis_trigger !bind_bind MIRed.ag.
  ired; f_equal. extensionalities P; ired; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l /precond.
  (* rewrite SBRed.bind SBRed.vis /= Himg1 vis_trigger !bind_bind MIRed.ag.
  ired; f_equal. extensionalities P'; ired; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l. *)
  
  rewrite SBRed.bind MIRed.bind; f_equal.
  extensionalities vret.
  rewrite SBRed.bind SBRed.vis /= Himg0 vis_trigger !bind_bind MIRed.core; f_equal.
  extensionalities ret; ired; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l.
  rewrite SBRed.bind SBRed.vis /= Himg3 vis_trigger !bind_bind MIRed.ag; f_equal.
  extensionalities b; destruct b; do 2 f_equal.
  rewrite SBRed.ret bind_ret_l.
  (* rewrite SBRed.bind SBRed.vis /= Himg3 vis_trigger !bind_bind MIRed.ag; f_equal.
  extensionalities c; destruct c; do 2 f_equal. *)
  (* rewrite SBRed.ret bind_ret_l. *)
  rewrite SBRed.ret MIRed.ret //.
Qed.

Lemma MIRed_HoareCall md sp fn varg
  (msk msk0: emask) fspo fspo0 bd0 m m0 pre pre0 post post0 N stid
  (WF: SMod.cancellable md)
  (* (SPWF: speckey_concE ∈ dom sp) *)
  (IN: ∀ x, msk _ (subevent _ (Call fn x)) = true)
  (IMG: img_msk msk)
  (SP: sp !! (speckey_fn fn) = fspo)
  (FIND: (SMod.fnsems md) !! (Some fn) = Some (Some (msk0, (fspo0, bd0))))
  (ST: fspo = Some (@fspec_mk _ m pre post))
  (ST0: fspo0 = Some (@fspec_mk _ m0 pre0 post0))
  :
  inline_body (sandboxed_prog (SMod.to_mod sp md)) (SB.sandbox msk (SModTr.HoareCall fspo fn varg N stid))
  =
  (* head *)
  '(N', stid', x,x0,arg):_ <- elim_precond pre pre0 N stid varg ;;
  (* body *)
  vret0 <- inline_body (sandboxed_prog (SMod.to_mod sp md)) 
                       (SB.sandbox msk0 (SModTr.trans sp N' stid' (bd0 arg)));;
  (* tail *)
  elim_postcond post post0 N N' stid stid' x x0 vret0.
Proof using.
  r in IMG. des.
  r in WF. hexploit WF; eauto. intros [IM [_ _]]. r in IM. des.
  destruct fspo; ss. destruct f; ss. depdes ST.
  destruct fspo0; ss. destruct f; ss. depdes ST0.
  rewrite /elim_precond /elim_postcond. ired.
  rewrite !SBRed.bind !SBRed.vis /= IMG0 vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= IMG0 vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind SBRed.vis /= IMG3 vis_trigger !bind_bind MIRed.ag. do 2 f_equal.
  extensionalities. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  (* rewrite /precond SBRed.vis /= IMG3 vis_trigger !bind_bind MIRed.ag. do 2 f_equal.
  extensionalities. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l. *)
  rewrite SBRed.vis IN vis_trigger !bind_bind MIRed.call. do 2 f_equal.
  rewrite {2}/sandboxed_prog. rewrite lookup_omap {2}/SMod.to_mod /= lookup_fmap FIND /= bind_ret_l.
  rewrite /SB.sandbox_body /SModTr.trans_fnsem. s.
  rewrite !SBRed.bind SBRed.vis /= IM vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. destruct H2. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= IM vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= IM vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= !IM1 !vis_trigger !bind_bind MIRed.ag. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  (* rewrite /precond MIRed.ag. ired. do 2 f_equal. *)
  (* extensionalities. ired. do 2 f_equal. *)
  (* rewrite !SBRed.ret bind_ret_l. *)
  rewrite MIRed.bind. ired. do 2 f_equal.
  extensionalities. ired.
  rewrite !SBRed.bind !SBRed.vis /= !IM0 !vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= !IM3 !vis_trigger !bind_bind MIRed.ag. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  (* rewrite MIRed.ag /precond. ired. do 2 f_equal. *)
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l MIRed.tau. ired. do 4 f_equal.
  rewrite !SBRed.bind SBRed.vis /= IMG vis_trigger !bind_bind MIRed.core. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  rewrite !SBRed.bind !SBRed.vis /= !IMG1 !vis_trigger !bind_bind MIRed.ag. do 2 f_equal.
  extensionalities. ired. do 2 f_equal.
  rewrite !SBRed.ret bind_ret_l.
  (* rewrite MIRed.ag /precond. ired. do 2 f_equal. *)
  extensionalities. ired.
  by rewrite MIRed.ret.
(*SLOW*)Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto 6 with paco.

Lemma elim_rel_cancel (md: SMod.t) T msk sN tN stid ttid (itr: itree _ T)
  (WF: SMod.cancellable md)
  (IMG: img_msk msk)
  (CALL: call_msk msk)
  :
  @elim_rel tN (SMod.conc_sp_from md) T ε
    (inline_body (sandboxed_prog (SMod.to_mod ∅ (SMod.cancel md))) 
      (SB.sandbox msk (SModTr.trans ∅ sN stid itr)))
    (inline_body (sandboxed_prog (SMod.to_mod (SMod.conc_sp_from md) md)) 
      (SB.sandbox msk (SModTr.trans (SMod.conc_sp_from md) tN ttid itr))).
Proof using.
  ginit. revert IMG CALL. revert T itr sN stid ttid msk. gcofix CIH. i.
  dup WF. red in WF. dup IMG. red in IMG. des.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SBRed.ret !MIRed.ret. estep 1.
  - rewrite !SRed.tau !SBRed.tau !MIRed.tau. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.vis IMG2 vis_trigger !bind_bind.
    rewrite !MIRed.ag. estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind !SBRed.vis IMG3 vis_trigger !bind_bind.
    rewrite !MIRed.ag. estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind !SBRed.vis IMG4 vis_trigger !bind_bind !MIRed.ag.
    estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - depdes c; s.
    (* call case *)
    { 
      rewrite !SRed.bind !SBRed.bind !SRed.call !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. estep 2. rewrite lookup_empty. destruct (msk _ (subevent _ (Call fn args))) eqn: E; cycle 1.
      { rewrite SBRed.vis E vis_trigger // MIRed.core. ired. estep 1. }
      destruct ((SMod.fnsems md) !! (Some fn)) eqn: E0; cycle 1.
      { rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
        rewrite {4}/SMod.conc_sp_from. rewrite lookup_insert_ne //. rewrite (lookup_sp_from _ _ None) //.
        ired. rewrite SBRed.vis E vis_trigger !MIRed.bind. ired.
        rewrite -(bind_ret_r (trigger _)) !MIRed.call. ired.
        estep 1. rewrite !MIRed.bind. rewrite !lookup_omap /= !lookup_fmap E0 /=. ired.
        rewrite !MIRed.bind /=. rewrite -(bind_ret_r (trigger _)) MIRed.core. ired.
        estep 1. }
      destruct o; cycle 1.
      { rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
        rewrite {4}/SMod.conc_sp_from. rewrite lookup_insert_ne //. rewrite (lookup_sp_from _ _ (Some None)) //.
        ired. rewrite SBRed.vis E vis_trigger !MIRed.bind. ired.
        rewrite -(bind_ret_r (trigger _)) !MIRed.call. ired.
        estep 1. rewrite !MIRed.bind. rewrite !lookup_omap /= !lookup_fmap E0 /=. ired.
        rewrite !MIRed.bind /=. rewrite -(bind_ret_r (trigger _)) MIRed.core. ired.
        estep 1. }
      destruct p as [img0 [fsp0 bd0]].
      destruct fsp0; [destruct f|]; cycle 1.
      { rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
        rewrite {4}/SMod.conc_sp_from. rewrite lookup_insert_ne //. rewrite (lookup_sp_from _ _ (Some (Some (img0, (None, bd0))))) //.
        ired. rewrite SBRed.vis E vis_trigger !MIRed.bind. ired.
        rewrite -(bind_ret_r (trigger _)) !MIRed.call. ired.
        estep 1. rewrite !MIRed.bind. rewrite !lookup_omap /= !lookup_fmap E0 /=. ired.
        rewrite !MIRed.ret. ired. guclo elim_rel_bindC_spec. econs.
        { r in WF0. hexploit WF0; eauto. i; des. r in H1. des; ss. }
        i. rewrite !MIRed.tau. ired. estep 2. rewrite !MIRed.ret !bind_ret_l.
        rewrite !SBRed.ret !MIRed.ret !bind_ret_l. gbase. eapply CIH; eauto. }

      set (fsp := fspec_mk _ _) in E0.
      rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
      rewrite {4}/SMod.conc_sp_from. rewrite lookup_insert_ne //.
      rewrite (lookup_sp_from _ _ (Some (Some (img0, (Some fsp, bd0))))) //.
      
      erewrite MIRed_HoareCall; et; cycle 1.
      { i. r in CALL. hexploit (CALL fn args x); i; des; eauto. }
      { rewrite /SMod.conc_sp_from. rewrite lookup_insert_ne //.
        rewrite (lookup_sp_from _ _ (Some (Some (img0, (Some fsp, bd0))))) //. }

      rewrite MIRed.bind MIRed.call MIRed.bind.
      rewrite {2}/sandboxed_prog. s. 
      rewrite lookup_omap !lookup_fmap E0 /= MIRed.bind MIRed.ret bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans_fnsem /= SBRed.tau MIRed.tau. ired.

      gstep. eapply elim_rel_precond; eauto. i.
      exists x. split; eauto.

      ired. guclo elim_rel_bindC_spec. econs.
      { gbase. eapply CIH; eauto.
        { r in WF0. hexploit WF0; eauto. i; des; eauto. }
        { r in WF0. hexploit WF0; eauto. i; des; eauto. }
      }

      i. ired. rewrite !MIRed.tau MIRed.ret. ired.
      rewrite SBRed.ret MIRed.ret bind_ret_l.
      gstep. eapply elim_rel_postcond; et.
      split; eauto.
      gbase. eapply CIH; eauto.
    }
    
    (* spawn case *)
    {
      rewrite !SRed.bind !SBRed.bind !SRed.spawn !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. estep 2. rewrite lookup_empty.
      rewrite dom_empty_L. destruct (decide (speckey_concE ∈ ∅)); [ss|].
      destruct (decide (speckey_concE ∈ dom (SMod.conc_sp_from md))); cycle 1.
      { exfalso. eapply n0. rewrite /SMod.conc_sp_from.
        rewrite dom_insert. set_solver. }

      destruct (msk _ (subevent _ (Spawn fn args))) eqn: M; cycle 1.
      { rewrite SBRed.vis M vis_trigger MIRed.core. ired. estep 1. }
      rewrite !SBRed_HoareSpawn //; cycle 1.
      { i. r in CALL. hexploit (CALL fn x args). i; des; eauto. }
      { i. r in CALL. hexploit (CALL fn args x). i; des; eauto. }
      rewrite !MIRed_HoareSpawn.
      gstep. eapply elim_rel_spawn; eauto.
      i. ss. edone.
    }

    (* yield case *)
    {
      rewrite !SRed.bind !SRed.yield !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau. estep 2.
      destruct (decide (speckey_concE ∈ dom ∅)); [ss|].
      destruct (decide (speckey_concE ∈ dom (SMod.conc_sp_from md))); cycle 1.
      { exfalso. eapply n0. rewrite /SMod.conc_sp_from. rewrite dom_insert. set_solver. }
      destruct (msk _ (subevent _ (Yield tid))) eqn:Y; cycle 1.
      { ss. rewrite SBRed.vis Y vis_trigger bind_bind MIRed.core. estep 1. }
      rewrite !MIRed.bind !SBRed_HoareYield // !MIRed_HoareYield.
      gstep. eapply elim_rel_yield; eauto.
      i; s. edone.
    }

    (* get tid case *)
    {
      rewrite !SRed.bind !SRed.gettid !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau. estep 2.
      destruct (decide (speckey_concE ∈ dom ∅)); [ss|].
      destruct (decide (speckey_concE ∈ dom (SMod.conc_sp_from md))); cycle 1.
      { exfalso. eapply n0. rewrite /SMod.conc_sp_from. rewrite dom_insert. set_solver. }
      destruct (msk _ (subevent _ GetTid)) eqn:Y; cycle 1.
      { ss. rewrite SBRed.vis Y vis_trigger bind_bind MIRed.core. estep 1. }
      rewrite !MIRed.bind !SBRed_HoareGetTid // !MIRed_HoareGetTid.
      gstep. rewrite (HoareGetTidE_indep stid ttid).
      eapply elim_rel_gettid; eauto.
      i; s. edone.
    }

  - rewrite !SRed.bind !SRed.pg !SBRed.bind. destruct s.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.core !SBRed.bind. destruct e.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
(*SLOW*)Qed.

End ELIM_REL.
Hint Resolve cpn4_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Section CancelDef.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

  (* Definition main_post : Any.t → itree lmodE Any.t := *)
  (*   λ vret, *)
  (*     ModTr.trans *)
  (*       (ret <- trigger (Choose Any.t);; tau;; *)
  (*        trigger (Guarantee ⌜vret = ret⌝);;; tau;; Ret ret). *)

  Definition main_post {X} (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ))
    (N: namespace) (x: X): Any.t → itree lmodE Any.t :=
    λ vret,
      ModTr.trans
        (ret <- trigger (Choose Any.t);; tau;;
         trigger (Guarantee (TID 0 ∗ YIELD 0 ∗ winv (↑N, ↑N)));;; tau;;
         trigger (Guarantee (⌜vret = ret⌝ ∗ (PQ x).2 vret));;; tau;;
         Ret ret).

  (* thread_rel (main spec) (main namespace) (main meta) cid tid ... *)
  Variant thread_rel {X: Type} (PQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm
    sp cid : nat → Σ → itree lmodE Any.t → itree lmodE Any.t → Prop :=
  | thread_rel_body itrS itrT src tgt r_diff tid (k: Any.t → itree lmodE Any.t)
      (MAIN: sp !! speckey_entry = Some (fspec_simple PQ))
      (RET: tid = 0 -> k = main_post PQ N mm)
      (TEQ: cid = tid)
      (REL: elim_rel N sp r_diff itrS itrT)
      (SRC: src = ModTr.trans itrS)
      (TGT: tgt = ModTr.trans itrT >>= k) :
     thread_rel PQ N mm sp cid tid r_diff src tgt
  | thread_rel_spawn src tgt r_diff tid itrS fspo m pre post varg arg bd x :
     tid ≠ 0 →
     cid ≠ tid →
     fspo = Some (@fspec_mk _ m pre post) →
     src = ModTr.trans (tau;; tau;; itrS) →
     tgt = ModTr.trans (
       '(N', tid, m, varg):_ <- elim_spawnee_precond pre arg;;
       vret <- bd N' tid varg;;
       elim_spawnee_postcond post N' tid m vret) →
     (Own r_diff ⊢ |==> pre (N, tid) x varg arg)%I →
     elim_rel N sp ε itrS (bd N tid varg) →
     thread_rel PQ N mm sp cid tid r_diff src tgt
  | thread_rel_yield src tgt r_diff tid itrS itrT (k: Any.t → itree lmodE Any.t) :
     sp !! speckey_entry = Some (fspec_simple PQ) →
     (tid = 0 -> k = main_post PQ N mm) →
     cid ≠ tid →
     src = ModTr.trans (tau;; itrS) →
     tgt = ModTr.trans (tau;; trigger (Assume (TID(tid) ∗ YIELD(tid) ∗ winv(↑N, ↑N)));;; tau;; itrT) >>= k →
     elim_rel N sp ε itrS itrT →
     thread_rel PQ N mm sp cid tid r_diff src tgt
  .
  
  Definition cancel_eq (x y: Any.t * Any.t) : Prop :=
    ∃ st r_s r_t,
    Any.split x.1 = Some (st,r_s) ∧ Any.split y.1 = Some (st,r_t) ∧
    x.2 = y.2.

  Definition CANCEL_GOAL md sp R
    {X: Type} (PQ: X → (Any.t →  iProp Σ) * (Any.t →  iProp Σ)) N (mm: X)
    (it_src it_tgt: itree crisE R) :=
    ∀ (r_i r_s r_t : Σ)
      (rs_diff : list Σ) (srcs tgts : list (itree lmodE Any.t))
      (cid : nat)
      (st : gmap key (option Any.t))
      (ps pt : smj)
      ktrS k ktrT
      (r : ∀ x x0, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
      (WFS: SMod.cancellable md)
      (VP: sp = SMod.conc_sp_from md)
      (MAIN: sp !! speckey_entry = Some (fspec_simple PQ))
      (* (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md))) *)
      (CIH :
        ∀ (r_s r_t : Σ) (rs_diff : list Σ) (srcs tgts : list (itree lmodE Any.t)) 
          (cid : nat) (st : gmap key (option Any.t)) (ps pt : smj)
          (REL : Forall3i (thread_rel PQ N mm sp cid) rs_diff srcs tgts)
          (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
          (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
                 TIDAUTH cid ∗ YIELDAUTH (length rs_diff)),
        r (Any.t * Any.t)%type (Any.t * Any.t)%type cancel_eq ps pt
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
              (Any.pair (ModTr.state_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i))) (cid, tgts))
              (Any.pair (ModTr.state_encode st) r_t ↑)))
      (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
              (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
              (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                     TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
              (LEN: cid < List.length srcs)
              (REL: thread_rel PQ N mm sp cid cid r_diff itr_s itr_t),
        gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
          (Any.t * Any.t)%type cancel_eq smj_top smj_top
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod ∅ (SMod.cancel md))) r_i)))
                    (cid, <[cid:=itr_s]> srcs))
              (Any.pair (ModTr.state_encode st) r_s ↑))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod sp md)) r_i)))
                    (cid, <[cid:=itr_t]> tgts))
              (Any.pair (ModTr.state_encode st) r_t ↑)))
      (EQLEN : length srcs = length tgts)
      (EQLEN2 : length rs_diff = length srcs)
      (REL : ∀ i x y z, srcs !! i = Some x → tgts !! i = Some y → rs_diff !! i = Some z →
        thread_rel PQ N mm sp cid i z x y)
      (WFR : ✓ r_s)
      (WFST: map_Forall (const is_Some) st)
      (RS : Own r_s ⊢
              |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗ 
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
      (LEN : cid < length srcs)
      (x0 : srcs !! cid = Some (ModTr.trans (x <- it_src;; ktrS x)))
      (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- it_tgt;; ktrT x);; k x))
      (x2 : rs_diff !! cid = Some ε)
      (RET : cid = 0 → k = main_post PQ N mm)
      (KTR : ∀ x, paco4 (elim_rel_def N sp) bot4 Any.t ε (ktrS x) (ktrT x)),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
       (Any.pair (ModTr.state_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp md)) r_i))) (cid, tgts))
       (Any.pair (ModTr.state_encode st) r_t ↑)).

End CancelDef.

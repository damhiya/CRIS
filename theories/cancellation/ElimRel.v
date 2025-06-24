Require Import Common Sp.
Require Import SMod HMod SModTr.
Require Import HModInline CancelLib Tactics.

Set Implicit Arguments.

Section ELIM_REL.

Context `{Σ: GRA}.

Definition NativeSpawnE (fn: string) (varg: Any.t) : itree hmodE nat :=
  tid <- trigger (Spawn fn varg);; tau;;
  trigger (Yield tid);;; tau;;
  Ret tid.

Definition HoareSpawnE fn varg (fsp: _fspec) : itree hmodE nat :=
  x <- trigger (Choose (_meta fsp));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (_precond fsp x varg arg));;; tau;;
  NativeSpawnE fn varg.

Definition elim_precond X P varg : itree hmodE (X * X * Any.t) :=
  x <- trigger (Choose X);; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (P x varg arg));;; tau;; tau;;
  x' <- trigger (Take X);; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  trigger (Assume (P x' varg' arg));;; tau;;
  Ret (x, x', varg').

Definition elim_postcond X Q (x x': X) vret' : itree hmodE Any.t :=
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (Q x' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  trigger (Assume (Q x vret ret));;; tau;;
  Ret vret.

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

| elim_rel_spawn_none fn args ktrS ktrT itrS itrT
    (STB: sp fn = None2)
    (EQS: itrS = NativeSpawnE fn args >>= ktrS)
    (EQT: itrT = NativeSpawnE fn args >>= ktrT)
    (KTR: forall x, self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self itrS itrT

| elim_rel_spawn_some fn args fsp ktrS ktrT itrS itrT
    (STB: sp fn = Some2 fsp)
    (EQS: itrS = NativeSpawnE fn args >>= ktrS)
    (EQT: itrT = HoareSpawnE fn args fsp >>= ktrT)
    (KTR: forall x, self _ (ktrS x) (ktrT x))
  :
  elim_rel_def sp self itrS itrT

| elim_rel_precond X P varg itrS itrT ktrT
    (KTR: ∀ x:X, self _ itrS (ktrT (x, x, varg)))
    (TGT: itrT = elim_precond P varg >>= ktrT)
  :
  elim_rel_def sp self (tau;; itrS) itrT

| elim_rel_postcond X Q (x: X) vret itrS itrT ktrT
    (KTR: self _ itrS (ktrT vret))
    (TGT: itrT = elim_postcond Q x x vret >>= ktrT)
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
  - eapply elim_rel_precond; i; [|f_equal].
    s. eapply rclo3_clo'; cycle 1.
    + econs; [eapply KTR|]; et.
    + eauto using rclo3.
  - eapply elim_rel_postcond; i; [|f_equal].
    s. eapply rclo3_clo'; cycle 1.
    + econs; [eapply KTR|]; et.
    + eauto using rclo3.
Qed.

Lemma HIRed_NativeSpawn
  prog fn args
  :
  inline_hp prog (SModTr.NativeSpawn fn args) = NativeSpawnE fn args.
Proof.
  rewrite /SModTr.NativeSpawn /NativeSpawnE. ired.
  rewrite HIRed.spawn. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.yield HIRed.ret. et.
Qed.

Lemma SBRed_NativeSpawn
  msk scp img fn args
  :
  SB.sandbox msk scp img (SModTr.NativeSpawn fn args) =
    if msk fn
    then SModTr.NativeSpawn fn args
    else tid <- triggerUB;;
         trigger (Yield tid);;;
         Ret tid.
Proof.
  rewrite /SModTr.NativeSpawn SBRed.bind SBRed.spawn. des_ifs.
  - f_equal. extensionalities. rewrite SBRed.bind SBRed.yield SBRed.ret. et.
  - f_equal. extensionalities. rewrite SBRed.bind SBRed.yield SBRed.ret. et.
Qed.

Lemma SBRed_HoareSpawn
  msk scp img fn args fsp
  :
  SB.sandbox msk scp img (SModTr.HoareSpawn fn args fsp) =
    if msk fn
    then SModTr.HoareSpawn fn args fsp
    else
      x <- trigger (Choose (_meta fsp));;
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (_precond fsp x args arg));;;
      tid <- triggerUB;;
      trigger (Yield tid);;;
      Ret tid.
Proof.
  rewrite /SModTr.HoareSpawn /SModTr.NativeSpawn. des_ifs.
  - rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.spawn Heq. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.yield. f_equal. extensionalities.
    rewrite SBRed.ret. ss.
  - rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.spawn Heq. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.yield. f_equal. extensionalities.
    rewrite SBRed.ret. ss.
Qed.

Lemma HIRed_HoareSpawn
  prog fsp fn args
  :
  inline_hp prog (SModTr.HoareSpawn fn args fsp) = HoareSpawnE fn args fsp.
Proof.
  rewrite /SModTr.HoareSpawn /HoareSpawnE. ired.
  rewrite HIRed.core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.ag. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed_NativeSpawn. et.
Qed.

Lemma HIRed_HoareCall md sp fn varg
  (msk msk0:_→bool) scp scp0 fsp fsp0 bd0
  (IN: msk fn)
  (SP: sp fn = Some2 fsp)
  (FIND: alist_find fn (SMod.fnsems md) = Some (msk0, scp0, (Some2 fsp0, bd0)))
  :
  inline_hp (sandboxed_prog (SMod.to_hmod sp md)) (SB.sandbox msk scp true (SModTr.HoareCall fn varg fsp))
  =
  (* head *)
  m <- trigger (Choose (_meta fsp));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (_precond fsp m varg arg));;; tau;; tau;;
  m' <- trigger (Take (_meta fsp0));; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  trigger (Assume (_precond fsp0 m' varg' arg));;; tau;;
  (* body *)
  vret' <- inline_hp (sandboxed_prog (SMod.to_hmod sp md)) 
                     (SB.sandbox msk0 scp0 true (SModTr.trans sp (bd0 varg')));;
  (* tail *)
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (_postcond fsp0 m' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  trigger (Assume (_postcond fsp m vret ret));;; tau;;
  Ret vret.
Proof.
  unfold SModTr.HoareCall.
  (* head *)
  rewrite SBRed.bind SBRed.choose HIRed.core.
  f_equal. extensionality m. do 2 f_equal.
  rewrite SBRed.bind SBRed.choose HIRed.core.
  f_equal. extensionality arg. do 2 f_equal.
  rewrite SBRed.bind SBRed.Guarantee HIRed.ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.bind SBRed.call. des_ifs; cycle 1.
  rewrite HIRed.call.
  do 2 f_equal. ired. rewrite {2}/sandboxed_prog.
  rewrite alist_find_map_snd FIND. ired.
  unfold SB.sandbox_body, SModTr.trans_ktree, SModTr.HoareFun. s.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
  f_equal. extensionality m'. do 2 f_equal.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
  f_equal. extensionality varg'. do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.ag.
  f_equal. extensionalities. do 2 f_equal. 
  (* body *)
  rewrite SBRed.bind. ired. rewrite HIRed.bind.
  f_equal. extensionality vret'.
  rewrite SBRed.bind SBRed.choose. ired. rewrite HIRed.core.
  f_equal. extensionality ret. do 2 f_equal. 
  rewrite SBRed.bind SBRed.Guarantee. ired. rewrite HIRed.ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret. ired. rewrite HIRed.tau.
  do 4 f_equal.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.core.
  f_equal. extensionality vret. do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret HIRed.ret. ss.
Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto with paco.

Lemma elim_rel_refl img (md: SMod.t) T msk scp (itr: itree _ T)
  (WF: sp_wf md)
  (VP: valid_params md msk scp img)
  :
  @elim_rel (sp_from md) T
    (inline_hp (sandboxed_prog (SMod.to_hmod sp_none (SMod.cancel md))) 
        (SB.sandbox msk scp img (SModTr.trans sp_none itr)))
    (inline_hp (sandboxed_prog (SMod.to_hmod (sp_from md) md)) 
        (SB.sandbox msk scp img (SModTr.trans (if img then sp_from md else sp_none) itr))).
Proof.
  ginit. revert T itr msk scp img VP. gcofix CIH. i.
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
    { rewrite !SRed.bind !SBRed.bind !SRed.call.
      ired. rewrite !SBRed.tau. ired. rewrite !HIRed.tau. estep 2.
      destruct ((if img then _ else _) fn) eqn: E; cycle 1.
      { s. ired. rewrite !SBRed.bind !SBRed.choose. ired.
        rewrite !HIRed.core. estep 1. }
      s. ired. rewrite SBRed.call. destruct (msk fn) eqn: E0; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite HIRed.core. estep 1. }

      destruct f; ss; cycle 1.

      (* case with no decoration *)
      {
        rewrite SBRed.call E0 !HIRed.call !HIRed.bind. estep 1.
        guclo elim_rel_bindC_spec. econs; cycle 1.
        { i. rewrite !subst_bind !HIRed.tau. ired. estep 2. edone. }
        rewrite {2 4}/sandboxed_prog. ired. rewrite !alist_find_map_snd.
        destruct (alist_find fn _) eqn: E1; s; ired; cycle 1.
        { rewrite HIRed.core. ired. estep 1. }
        rewrite !HIRed.ret. ired.
        destruct p as [[msk0 scp0][img0 bd]].
        rewrite /SB.sandbox_body /SModTr.trans_ktree. s.
        destruct img0; s; cycle 1.
        { gbase. eapply CIH; et. right; esplits; et. }
        destruct f; s; cycle 1.
        { gbase. eapply CIH; et. right; esplits; et. }
        exfalso. destruct img.
        - rewrite /sp_from /to_sp !alist_find_map_snd E1 in E. inv E.
        - exploit (WF fn); rr; et.
          rewrite /sp_from /to_sp !alist_find_map_snd E1. ss.
      }

      (* case with decoration *)
      { rewrite !HIRed.bind.
        guclo elim_rel_bindC_spec. econs; cycle 1.
        { eauto with paco. }
        destruct img; ss.
        rewrite -(bind_ret_r (trigger (Call fn args))).
        rewrite HIRed.call {2}/sandboxed_prog !alist_find_map_snd.
        destruct (alist_find fn (SMod.fnsems md)) eqn: E1; rewrite E1; cycle 1.
        { s. ired. rewrite HIRed.core. estep 1. }
        s. ired. destruct f as [[msk0 scp0][fspo bd0]].
        dup E. rewrite /sp_from /to_sp !alist_find_map_snd E1 in E. ss. depdes E.
        destruct fspo; ss. destruct f; ss. depdes x.
        erewrite HIRed_HoareCall; et.

        gstep. eapply elim_rel_precond; cycle 1.
        { rewrite /elim_precond. ired. f_equal. extensionalities. ired.
          do 3 f_equal. extensionalities. ired.
          do 3 f_equal. extensionalities.
          do 5 f_equal. extensionalities. ired.
          do 3 f_equal. extensionalities. ired.
          do 3 f_equal. extensionalities.
          do 2 f_equal. instantiate (1:= λ '(_,_,_), _). s. et.
        }

        i. ired. rewrite /SB.sandbox_body. s. rewrite HIRed.bind.
        guclo elim_rel_bindC_spec. econs.
        { gbase. eapply CIH. right. esplits; et. }

        i. rewrite subst_bind. ired. rewrite HIRed.tau HIRed.ret.
        gstep. eapply elim_rel_postcond; cycle 1.
        { rewrite /elim_postcond. ired. f_equal. extensionalities. ired.
          do 3 f_equal.
        }
        s. estep 1.
      }
    }
    
    (* spawn case *)
    { rewrite !SRed.bind !SRed.spawn.
      ired. rewrite !SBRed.tau. ired. rewrite !HIRed.tau. estep 2.
      destruct ((if img then _ else _) fn) eqn: E; cycle 1.
      { s. ired. rewrite !SBRed.bind !SBRed.choose. ired.
        rewrite !HIRed.core. estep 1. }
      s. ired. rewrite SBRed.bind SBRed_NativeSpawn.
      destruct (msk fn) eqn: E0; cycle 1.
      { rewrite /triggerUB. s. ired. rewrite HIRed.core. estep 1. }
      rewrite HIRed.bind HIRed_NativeSpawn SBRed.bind HIRed.bind.
      
      destruct f; ss; cycle 1.

      (* case with no decoration *)
      {
        rewrite SBRed_NativeSpawn E0 HIRed_NativeSpawn.
        gstep. eapply elim_rel_spawn_none; et.
        - destruct img; et. eapply WF. r; et.
        - edone.
      }

      (* case with decoration *)
      {
        rewrite SBRed_HoareSpawn E0 HIRed_HoareSpawn.
        gstep. eapply elim_rel_spawn_some; et.
        - destruct img; et. ss.
        - edone.
      }
    }

    (* yield case *)
    { rewrite !SRed.bind !SRed.yield !SBRed.bind SBRed.yield !HIRed.yield.
      estep 2. edone.
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
(*SLOW*)Admitted.

End ELIM_REL.
Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

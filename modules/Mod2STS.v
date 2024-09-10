Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Events.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Program.
Require Import Red IRed.

Section EXEC.

  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
    interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

  Definition handle_stateE {E}: stateE ~> stateT Any.t (itree E) :=
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {E}: itree (stateE +' E) ~> stateT Any.t (itree E) :=
    State.interp_state (case_ handle_stateE pure_state).

  Definition ths_state : Type := nat * list (itree modE Any.t).

  Definition handle_schE_callE (prog: callE ~> itree modE):
    ths_state -> itree (stateE +' coreE) (ths_state + Any.t) :=
    fun '(tid, ths) =>
      itr <- (base.lookup tid ths)? ;;
      match observe (itr: itree modE Any.t) with
      | RetF rv =>
          if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB
      | TauF itr' =>
          tau;; Ret (inl (tid, base.insert tid itr' ths))
      | VisF (inr1 (inr1 e)) k =>
          v <- trigger e;;
          Ret (inl (tid, base.insert tid (k v) ths))
      | VisF (inr1 (inl1 e)) k =>
          Ret (inl (tid, base.insert tid (x <- prog _ e;; tau;; k x) ths))
      | VisF (inl1 e) k =>
          match e in schE T return (T -> _) -> _ with
          | Spawn fn arg => fun k =>
                              Ret (inl (tid, (base.insert tid (k (List.length ths)) ths) ++ [prog _ (Call fn arg)]))
          | Yield tid' => fun k =>
                            Ret (inl (tid', base.insert tid (k tt) ths))
          | Tid => fun k =>
                     Ret (inl (tid, base.insert tid (k tid) ths))
          end k
      end.

  Definition interp_schE_callE (prog: callE ~> itree modE) (itr0: itree modE Any.t)
    : itree (stateE +' coreE) Any.t
    :=
    ITree.iter (handle_schE_callE prog) (0, [itr0]).

  Definition interp_modE (prog: callE ~> itree modE) (itr0: itree modE Any.t) (st0: Any.t): itree coreE _ :=
    interp_stateE Any.t (interp_schE_callE prog itr0) st0.

End EXEC.

(*
Opaque interp_modE.

Section RED.

  Variable prog: callE ~> itree modE.

  Lemma interp_modE_bind
        A
        (itr: itree modE A) (ktr: A -> itree modE Any.t)
        st0
    :
      interp_modE prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_modE prog (itr) st0 ;; interp_modE prog (ktr v) st1.

  Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

  Lemma interp_modE_tau
        (prog: callE ~> itree modE)
        A
        (itr: itree modE A)
        st0
    :
      interp_modE prog (tau;; itr) st0 = tau;; interp_modE prog itr st0.
  Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

  Lemma interp_modE_ret
        T
        prog st0 (v: T)
    :
      interp_modE prog (Ret v: itree modE _) st0 = Ret (st0, v).
  Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

  Lemma interp_modE_callE
        p st0 T
        (* (e: modE Σ) *)
        (e: callE T)
    :
      interp_modE p (trigger e) st0 = tau;; (interp_modE p (p _ e) st0).
  Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

  Lemma interp_modE_stateE
        p st0
        (* (e: modE Σ) *)
        T
        (e: stateE T)
    :
      interp_modE p (trigger e) st0 =
      '(st1, r) <- handle_stateE e st0;;
      tau;; tau;;
      Ret (st1, r).
  Proof.
    unfold interp_modE, interp_stateE. grind.
  Qed.

  Lemma interp_modE_coreE
        p st0
        T
        (e: coreE T)
    :
      interp_modE p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r).
  Proof.
    unfold interp_modE, interp_stateE. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_modE_triggerUB
        (prog: callE ~> itree modE)
        st0
        A
    :
      (interp_modE prog (triggerUB) st0: itree coreE (_ * A)) = triggerUB.
  Proof.
    unfold interp_modE, interp_stateE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_modE_triggerNB
        (prog: callE ~> itree modE)
        st0
        A
    :
      (interp_modE prog (triggerNB) st0: itree coreE (_ * A)) = triggerNB.
  Proof.
    unfold interp_modE, interp_stateE, pure_state, triggerNB. grind.
  Qed. 
  
  Lemma interp_modE_unwrapU
        prog R st0 (r: option R)
    :
      interp_modE prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_modE_ret. grind.
    - rewrite interp_modE_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma interp_modE_unwrapN
        prog R st0 (r: option R)
    :
      interp_modE prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_modE_ret. grind.
    - rewrite interp_modE_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma interp_modE_assume
        prog st0 (P: Prop)
    :
      interp_modE prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt).
  Proof.
    unfold assume.
    repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
    rewrite interp_modE_coreE.
    repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
    rewrite interp_modE_ret.
    refl.
  Qed.

  Lemma interp_modE_guarantee
        prog st0 (P: Prop)
    :
      interp_modE prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt).
  Proof.
    unfold guarantee.
    repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
    rewrite interp_modE_coreE.
    repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
    rewrite interp_modE_ret.
    refl.
  Qed.    

  Lemma interp_modE_ext
        prog R (itr0 itr1: itree _ R) st0
    : 
      itr0 = itr1 -> interp_modE prog itr0 st0 = interp_modE prog itr1 st0.
  Proof. i; subst; refl. Qed.    

End RED.

Global Program Instance interp_modE_rdb: red_database (mk_box (@interp_modE)) :=
  mk_rdb
    1
    (mk_box interp_modE_bind)
    (mk_box interp_modE_tau)
    (mk_box interp_modE_ret)
    (mk_box interp_modE_stateE)
    (mk_box interp_modE_stateE)
    (mk_box interp_modE_callE)
    (mk_box interp_modE_coreE)
    (mk_box interp_modE_triggerUB)
    (mk_box interp_modE_triggerNB)
    (mk_box interp_modE_unwrapU)
    (mk_box interp_modE_unwrapN)
    (mk_box interp_modE_assume)
    (mk_box interp_modE_guarantee)
    (mk_box interp_modE_ext).

 *)

Section SEMANTICS.
  Let state: Type := itree coreE Any.t.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv => final rv
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (IO fn args) k => STS.vis
    end.

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_io
      fn I O (args: I) (rv: O) k
    :
      step (Vis (subevent _ (IO fn args)) k) (Some (event_io fn args rv)) (k rv).

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_trigger_take_iff X k itr e
        (STEP: step (trigger (Take X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_tau_iff itr0 itr1 e
        (STEP: step (Tau itr0) e itr1)
    :
      e = None /\ itr0 = itr1.
  Proof.
    inv STEP. et.
  Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr)
    :
      False.
  Proof.
    inv STEP.
  Qed.

  Lemma step_trigger_io_iff fn I O args k e itr
        (STEP: step (trigger (@IO I O fn args) >>= k) e itr)
    :
      exists rv, itr = k rv /\ e = Some (event_io fn args rv).
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et. }
  Qed.

  Let itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1)
    :
      itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x
    :
      step (trigger (Choose X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Choose X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_take X k x
    :
      step (trigger (Take X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Take X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_io I O fn (args: I) k (rv: O)
    :
      step (trigger (IO fn args) >>= k) (Some (event_io fn args rv)) (k rv).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (IO fn args) k)
    end; ss.
    { econs; et. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.


  Program Definition compile_itree: itree coreE Any.t -> semantics :=
    fun itr =>
      {|
        STS.state := state;
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := state_sort;
      |}.
  Next Obligation. inv STEP; inv STEP0; ss. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  
End SEMANTICS.

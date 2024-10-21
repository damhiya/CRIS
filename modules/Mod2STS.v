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

  Definition handle_schE_callE (prog: callE ~> itree modE)
      : ths_state -> itree (stateE +' coreE) (ths_state + Any.t) :=
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
      : itree (stateE +' coreE) Any.t :=
    ITree.iter (handle_schE_callE prog) (0, [itr0]).

  Definition interp_modE (prog: callE ~> itree modE) (itr0: itree modE Any.t) (st0: Any.t)
      : itree coreE _ :=
    interp_stateE Any.t (interp_schE_callE prog itr0) st0.

End EXEC.

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
  | step_tau itr :
      step (Tau itr) None itr
  | step_choose X k (x : X) :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take X k (x : X) :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_io fn I O (args: I) (rv: O) k :
      step (Vis (subevent _ (IO fn args)) k) (Some (event_io fn args rv)) (k rv).

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr) :
    exists x, e = None /\ itr = k x.
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
        (STEP: step (trigger (Take X) >>= k) e itr) :
    exists x, e = None /\ itr = k x.
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
        (STEP: step (Tau itr0) e itr1) :
    e = None /\ itr0 = itr1.
  Proof. inv STEP. et. Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr) :
    False.
  Proof. inv STEP. Qed.

  Lemma step_trigger_io_iff fn I O args k e itr
        (STEP: step (trigger (@IO I O fn args) >>= k) e itr) :
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

  Local Lemma itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1) :
    itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x :
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

  Lemma step_trigger_take X k x :
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

  Lemma step_trigger_io I O fn (args: I) k (rv: O) :
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

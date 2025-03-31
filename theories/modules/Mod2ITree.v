Require Import Common.

Section EXEC.

  Definition pure_state {S E} : E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
    interp_state h t s = _interp_state h (observe t) s.
  Proof using. i. f. apply unfold_interp_state. Qed.

  Definition handle_stateE {E} : stateE ~> stateT Any.t (itree E) :=
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {E} : itree (stateE +' E) ~> stateT Any.t (itree E) :=
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
          end k
      end.

  Definition interp_schE_callE (prog: callE ~> itree modE) (itr0: itree modE Any.t)
      : itree (stateE +' coreE) Any.t :=
    ITree.iter (handle_schE_callE prog) (0, [itr0]).

  Definition interp_modE (prog: callE ~> itree modE) (itr0: itree modE Any.t) (st0: Any.t): itree coreE _ :=
    interp_stateE Any.t (interp_schE_callE prog itr0) st0.

End EXEC.

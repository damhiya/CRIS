Require Import Common.

Module ModTr.
Section EXEC.

  Definition pure_state {S E} : E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Definition handle_stateE {E} : stateE ~> stateT Any.t (itree E) :=
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {E} : itree (stateE +' E) ~> stateT Any.t (itree E) :=
    State.interp_state (case_ handle_stateE pure_state).

  Definition ths_state : Type := nat * list (itree modE Any.t).

  Definition handle_callE (prog: string -> option (Any.t -> itree modE Any.t))
      : ths_state -> itreeV (stateE +' coreE) (ths_state + Any.t) :=
    fun '(tid, ths) =>
      match base.lookup tid ths with
      | None => inl (triggerUB)
      | Some itr =>
          match observe (itr: itree modE Any.t) with
          | RetF rv =>
              inl (if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB)
          | TauF itr' =>
              inl (Ret (inl (tid, base.insert tid itr' ths)))
          | VisF (inr1 e) k =>
              inr (existT _ (subevent _ e, fun v => Ret (inl (tid, base.insert tid (k v) ths))))
          | VisF (inl1 e) k =>
              inl
                (match e in callE T return (T -> _) -> _ with
                 | Call fn arg => fun k =>
                                    bd <- (prog fn)? ;;
                                    Ret (inl (tid, base.insert tid (x <- bd arg;; tau;; k x) ths))
                 | Spawn fn arg => fun k => let new_tid := List.length ths in
                                     bd <- (prog fn)? ;;
                                     Ret (inl (tid, (base.insert tid (k new_tid) ths) ++ [bd arg]))
                 | Yield tid' => fun k =>
                                    Ret (inl (tid', base.insert tid (k tt) ths))
                 end k)
          end
      end.

  Definition interp_callE prog (itr0: itree modE Any.t)
      : itree (stateE +' coreE) Any.t :=
    iterV (handle_callE prog) (0, [itr0]).

  Definition trans prog (itr0: itree modE Any.t) (st0: Any.t): itree coreE _ :=
    interp_stateE Any.t (interp_callE prog itr0) st0.

End EXEC.
End ModTr.

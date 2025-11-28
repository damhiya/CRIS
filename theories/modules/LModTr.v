Require Import Common.

Module LModTr.
  Definition pure_state {S E} : E ~> stateT S (itree E) := λ _ e s, x <- trigger e;; Ret (s, x).

  Definition handle_stateE {E} : stateE ~> stateT Any.t (itree E) :=
    λ _ e glob,
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {E} : itree (stateE +' E) ~> stateT Any.t (itree E) :=
    State.interp_state (case_ handle_stateE pure_state).

  Definition ths_state : Type := nat * list (itree lmodE Any.t).

  Definition handle_callE (prog: string → option (Any.t → itree lmodE Any.t))
      : ths_state → itreeV (stateE +' coreE) (ths_state + Any.t) :=
    λ '(tid, ths),
      match base.lookup tid ths with
      | None => inl (triggerUB)
      | Some itr =>
          match observe (itr: itree lmodE Any.t) with
          | RetF rv =>
              inl (if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB)
          | TauF itr' =>
              inl (Ret (inl (tid, <[tid := itr']> ths)))
          | VisF (inr1 e) k =>
              inr (existT _ (subevent _ e, λ v, Ret (inl (tid, <[tid := k v]> ths))))
          | VisF (inl1 e) k =>
              inl
                (match e in callE T return (T → _) → _ with
                 | Call fn arg =>
                    λ k,
                      bd <- (prog fn)? ;;
                      Ret (inl (tid, <[tid := x <- bd arg;; tau;; k x]> ths))
                 | Spawn fn arg =>
                    λ k, let new_tid := List.length ths in
                      bd <- (prog fn)? ;;
                      Ret (inl (tid, (<[tid := k new_tid]> ths) ++ [bd arg]))
                 | Yield tid' =>
                    λ k, Ret (inl (tid', <[tid := k tt]> ths))
                 | GetTid =>
                    λ k, Ret (inl (tid, <[tid:=k tid]> ths))
                 end k)
          end
      end.

  Definition interp_callE prog (itr : itree lmodE Any.t) : itree (stateE +' coreE) Any.t :=
    iterV (handle_callE prog) (0, [itr]).

  Definition trans prog (itr : itree lmodE Any.t) (st : Any.t): itree coreE _ :=
    interp_stateE Any.t (interp_callE prog itr) st.
End LModTr.

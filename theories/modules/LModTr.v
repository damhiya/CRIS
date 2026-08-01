From CRIS.common Require Import Common.

Module LModTr.
  Definition pure_state {S E} : E ~> stateT S (itree E) := λ _ e s, x <- trigger e;; Ret (s, x).

  Definition handle_stateE {Σ E} : lstateE Σ ~> stateT (lstateT Σ) (itree E) :=
    λ _ e glob,
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {Σ E} : itree (lstateE Σ +' E) ~> stateT (lstateT Σ) (itree E) :=
    State.interp_state (case_ handle_stateE pure_state).

  Definition ths_state {Σ} : Type := nat * list (itree (lmodE Σ) Any.t).

  Definition handle_callE {Σ} (prog: string → option (Any.t → itree (lmodE Σ) Any.t))
      : ths_state → itreeV (lstateE Σ +' coreE) (ths_state + Any.t) :=
    λ '(tid, ths),
      match base.lookup tid ths with
      | None => itreeV_nvis (triggerUB)
      | Some itr =>
          match observe (itr: itree (lmodE Σ) Any.t) with
          | RetF rv =>
              itreeV_nvis (if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB)
          | TauF itr' =>
              itreeV_nvis (Ret (inl (tid, <[tid := itr']> ths)))
          | VisF (inr1 e) k =>
              itreeV_vis (subevent _ e) (λ v, Ret (inl (tid, <[tid := k v]> ths)))
          | VisF (inl1 e) k =>
              itreeV_nvis
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

  Definition interp_callE {Σ} prog (itr : itree (lmodE Σ) Any.t) : itree (lstateE Σ +' coreE) Any.t :=
    iterV (handle_callE prog) (0, [itr]).

  Definition trans {Σ} prog (itr : itree (lmodE Σ) Any.t) (st : lstateT Σ): itree coreE _ :=
    interp_stateE Any.t (interp_callE prog itr) st.
End LModTr.

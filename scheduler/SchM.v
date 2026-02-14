(* Require Import CRIS.
Require Import SchHeader.

Definition thpool : Type := list (nat * option SAny.t).

Module SchM. Section SchM.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [SCH].
  Definition v_ths := SCH ↯ "ths".
  Definition v_tid := SCH ↯ "tid".

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'rv : SAny.t <- ccallU fn arg;;
      'ths : thpool <- cgetU v_ths;;
      'tid : nat <- cgetU v_tid;;
      match ths !! tid with
      | Some (stid, None) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;;
          Sch.terminate
      | _ => triggerUB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn SchHdr._spawn (fn, arg)↑);;
      let new_tid : nat := length ths in
      cput v_ths (<[new_tid := (new_stid, None)]> ths);;;
      Ret new_tid.

  Definition yield : unit → itree crisE unit :=
    λ _,
      'ths : thpool <- cgetU v_ths;;
      '(exist _ ntid _) :_ <- trigger (Choose {ntid : nat | ntid < length ths});;
      (* Sanity check *)
      tid <- trigger GetTid;;
      'mtid : nat <- cgetU v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerUB
      | None => triggerUB
      end;;;
      trigger (Yield ntid);;;
      cput v_tid mtid.

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetU v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => '() : _ <- ccallU SchHdr.yield tt;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetN v_tid.

  Definition fnsems : fnsems_type :=
    [(Some SchHdr._spawn,  (false, wmask_all, scopes, (None, cfunU inner_spawn)));
     (Some SchHdr.spawn,   (false, wmask_all, scopes, (None, cfunU spawn)));
     (Some SchHdr.yield,   (false, wmask_all, scopes, (None, cfunU yield)));
     (Some SchHdr.join,    (false, wmask_all, scopes, (None, cfunU join)));
     (Some SchHdr.get_tid, (false, wmask_all, scopes, (None, cfunU get_tid)))].

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_ths, ([(0, None)] : thpool)↑); (v_tid, 0↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End SchM. End SchM. *)

Require Import CRIS.
Require Import SchHeader.

Definition thpool : Type := list (nat * option SAny.t).
(* Definition tidslist : Type := list nat. *)

Module SchI. Section SchI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes := [SCH].
  Definition v_ths := SCH ↯ "ths".
  Definition v_tid := SCH ↯ "tid".
  (* Definition v_tids := SCH ↯ "tids". *)

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
      '(exist _ ntid _) : _ <- trigger (Choose {ntid : nat | ntid < length ths});;
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
    λ _, cgetU v_tid.

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
  (* Definition _spawn (check_internal : itree crisE unit) : (nat * string * SAny.t) -> itree crisE unit
    :=
    fun '(my_tid, fn, arg) =>
      (* check internal state (only for SRC) *)
      check_internal;;;
      (* set up tid for starting up *)
      cput v_tid my_tid;;;
      (* execute the spawnee *)
      'rv: SAny.t <- ccallU fn arg;;
      (* update the list of results after executing *)
      'ths: thslist <- cgetU v_ths;;
      let newths: thslist := alist_replace my_tid (Some rv) ths in
      cput v_ths newths;;;
      (* infinite loop for termination *)
      Sch.terminate
  . *)

  (* Definition spawn : (string * SAny.t) -> itree crisE nat :=
    fun '(fn, arg) =>
      (* get internal states *)
      'ths: thslist <- cgetU v_ths;;
      'my_tid: nat <- cgetU v_tid;;
      'tids: tidslist <- cgetU v_tids;;
      (* obtain next module-tid and give it to spawnee as an argument *)
      let new_mtid: nat := length tids in
      (* actual spawn using inner-spawn *)
      new_stid <- trigger (Spawn SchHdr._spawn (new_mtid, fn, arg)↑);;
      (* update internal states *)
      let newtids: tidslist := tids ++ [new_stid] in
      let newths: thslist := alist_add new_mtid None ths in
      cput v_ths newths;;;
      cput v_tids newtids;;;
      (* return module-tid *)
      Ret new_mtid
  . *)

  (* Definition yield (trigger_yield : nat -> itree crisE unit): unit -> itree crisE unit :=
    fun _ =>
      'tids: tidslist <- cgetU v_tids;;
      (* choose one of the tids which is managed by scheduler *)
      '(exist _ ntid _):_ <- trigger (Choose {ntid: nat | ntid < length tids});;
      trigger_yield ntid
  . *)

  (* Definition join: nat -> itree crisE (option SAny.t) :=
    fun tid =>
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (fun _ =>
        'ths: thslist <- cgetU v_ths;;
        match alist_find tid ths with
        | None => Ret (inr None)
        | Some (Some rv) => Ret (inr (Some rv))
        | Some None =>
            '(): _ <- ccallU SchHdr.yield tt;;
            Ret (inl tt)
        end
      ) tt);;
      Ret orv
  . *)

  (* Definition get_tid: unit -> itree crisE nat :=
    fun _ =>
      'my_tid : nat <- cgetU v_tid;;
      Ret my_tid
  . *)

  (* skip *)
  (* Definition check_internal : itree crisE unit := Ret tt. *)

  (* provide conversion between module-tid and system-tid *)
  (* Definition trigger_Yield (nxt_mtid : nat) : itree crisE unit :=
    'my_tid : nat <- cgetU v_tid;;
    'tids : tidslist <- cgetU v_tids;;
    match nth_error tids nxt_mtid with
    | Some nxt_stid => 
        trigger (Yield nxt_stid);;;
        cput v_tid my_tid
    | None => triggerUB
    end
  . *)
  
  (* Definition fnsems : fnsems_type :=
    [(Some SchHdr._spawn,  (false, wmask_all, scopes, (None, cfunU (_spawn check_internal))));
     (Some SchHdr.spawn,   (false, wmask_all, scopes, (None, cfunU spawn)));
     (Some SchHdr.yield,   (false, wmask_all, scopes, (None, cfunU (yield trigger_Yield))));
     (Some SchHdr.join,    (false, wmask_all, scopes, (None, cfunU join)));
     (Some SchHdr.get_tid, (false, wmask_all, scopes, (None, cfunU get_tid)))]. *)

  (* Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_ths, ([(0, None)]: thslist)↑); (v_tid, 0↑); (v_tids, ([0]: tidslist)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod). *)
End SchI. End SchI.

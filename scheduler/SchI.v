Require Import CRIS.

Require Import SchHeader.

Set Implicit Arguments.

Definition thslist: Type := list (nat * option SAny.t).
Definition tidslist: Type := list nat.

Module SchI. Section SchI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["Sch"].
  Definition v_ths := "Sch" ↯ "ths".
  Definition v_tid := "Sch" ↯ "tid".
  Definition v_tids := "Sch" ↯ "tids".

  Definition _spawn (check_internal : itree crisE unit) : (nat * string * SAny.t) -> itree crisE unit
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
  .

  Definition spawn : (string * SAny.t) -> itree crisE nat :=
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
  .

  Definition yield (trigger_yield : nat -> itree crisE unit): unit -> itree crisE unit :=
    fun _ =>
      'tids: tidslist <- cgetU v_tids;;
      (* choose one of the tids which is managed by scheduler *)
      '(exist _ ntid _):_ <- trigger (Choose {ntid: nat | ntid < length tids});;
      trigger_yield ntid
  .

  Definition join: nat -> itree crisE (option SAny.t) :=
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
  .

  Definition get_tid: unit -> itree crisE nat :=
    fun _ =>
      'my_tid : nat <- cgetU v_tid;;
      Ret my_tid
  .

  Definition check_internal : itree crisE unit := Ret tt. (* skip *)

  (* provide conversion between module-tid and system-tid *)
  Definition trigger_Yield (nxt_mtid : nat) : itree crisE unit :=
    'my_tid : nat <- cgetU v_tid;;
    'tids : tidslist <- cgetU v_tids;;
    match nth_error tids nxt_mtid with
    | Some nxt_stid => 
        trigger (Yield nxt_stid);;;
        cput v_tid my_tid
    | None => triggerUB
    end
  .
  
  Definition fnsems : fnsems_type :=
    [(Some SchHdr._spawn,  (false, wmask_all, scopes, (None, cfunU (_spawn check_internal))));
     (Some SchHdr.spawn,   (false, wmask_all, scopes, (None, cfunU spawn)));
     (Some SchHdr.yield,   (false, wmask_all, scopes, (None, cfunU (yield trigger_Yield))));
     (Some SchHdr.join,    (false, wmask_all, scopes, (None, cfunU join)));
     (Some SchHdr.get_tid, (false, wmask_all, scopes, (None, cfunU get_tid)))].

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_ths, ([(0, None)]: thslist)↑); (v_tid, 0↑); (v_tids, ([0]: tidslist)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).

End SchI. End SchI.

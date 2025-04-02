Require Import CRIS.

Require Import SchHeader.

Set Implicit Arguments.

Definition thstat : Type := nat * (option SAny.t).
Definition thslist: Type := list thstat.

Module SchI. Section SchI.
  Local Open Scope string_scope.
  Context `{!sinvG Γ Σ α β τ}.

  Definition scopes := ["Sch"; "Tid"].
  Definition v_ths := "Sch" ↯ "ths".
  Definition v_tid := "Tid" ↯ "tid".

  Definition trigger_Yield (nxt_tid : nat) : itree pmodE unit :=
    'my_tid: nat <- cgetU v_tid;;
    trigger (Yield nxt_tid);;;
    cput v_tid my_tid
  .

  Definition _spawn: (nat * string * SAny.t) -> itree pmodE unit :=
    fun '(pa_tid, fn, arg) =>
      trigger_Yield pa_tid;;;
      'rv: SAny.t <- ccallU fn arg;;
      'my_tid: nat <- cgetU v_tid;;
      'ths: thslist <- cgetU v_ths;;
      let newths: thslist := alist_replace my_tid (Some rv) ths in
      cput v_ths newths;;;
      Sch.terminate
  .

  Definition spawn: (string * SAny.t) -> itree pmodE nat :=
    fun '(fn, arg) =>
      'ths: thslist <- cgetU v_ths;;
      'my_tid: nat <- cgetU v_tid;;
      new_tid <- trigger (Spawn SchHdr._spawn (my_tid, fn, arg)↑);;
      let newths: thslist := alist_add new_tid None ths in
      cput v_ths newths;;;
      cput v_tid new_tid;;;
      trigger (Yield new_tid);;;
      cput v_tid my_tid;;;
      Ret new_tid
  .

  Definition yield: unit -> itree pmodE unit :=
    fun _ =>
      'ths: thslist <- cgetU v_ths;;
      'ntid: nat <- trigger (Choose nat);;
      guarantee (is_Some (alist_find ntid ths));;;
      trigger_Yield ntid
  .

  Definition join: nat -> itree pmodE (option SAny.t) :=
    fun tid =>
      orv <- (ITree.iter (fun _ =>
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

  Definition get_tid: unit -> itree pmodE nat :=
    fun _ =>
      'my_tid : nat <- cgetU v_tid;;
      Ret my_tid
  .

  Local Definition scopes_tid := ["Tid"].

  Definition fnsems :=
    [(SchHdr._spawn, (scopes, cfunU _spawn));
     (SchHdr.spawn, (scopes, cfunU spawn));
     (SchHdr.yield, (scopes, cfunU yield));
     (SchHdr.join, (scopes, cfunU join));
     (SchHdr.get_tid, (scopes_tid, cfunU get_tid))].
  
  Program Definition Mod: PMod.t :=
  {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [(v_ths, ([(0, None)]: thslist)↑); (v_tid, 0↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End SchI. End SchI.

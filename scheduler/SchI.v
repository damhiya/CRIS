Require Import CRIS.

Require Import SchHeader.

Set Implicit Arguments.

Definition thslist: Type := list (nat * option SAny.t).

Module SchI. Section SchI.
  Local Open Scope string_scope.

  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["Sch"].
  Definition v_ths := "Sch" ↯ "ths".
  Definition v_tid := "Sch" ↯ "tid".

  Definition _spawn (trigger_yield_half : nat -> itree hmodE unit) : (nat * string * SAny.t) -> itree hmodE unit
    :=
    fun '(pa_tid, fn, arg) =>
      trigger_yield_half pa_tid;;;
      'rv: SAny.t <- ccallU fn arg;;
      'ths: thslist <- cgetU v_ths;;
      'my_tid: nat <- cgetU v_tid;;
      let newths: thslist := alist_replace my_tid (Some rv) ths in
      cput v_ths newths;;;
      Sch.terminate
  .

  Definition spawn : (string * SAny.t) -> itree hmodE nat :=
    fun '(fn, arg) =>
      'ths: thslist <- cgetU v_ths;;
      'my_tid: nat <- cgetU v_tid;;
       new_tid <- trigger (Spawn SchHdr._spawn (my_tid, fn, arg)↑);;
      let newths: thslist := alist_add new_tid None ths in
      cput v_ths newths;;;
      Ret new_tid
  .

  Definition yield (trigger_yield : nat -> itree hmodE unit): unit -> itree hmodE unit :=
    fun _ =>
      'ths: thslist <- cgetU v_ths;;
      'ntid: nat <- trigger (Choose nat);;
      guarantee (is_Some (alist_find ntid ths));;;
      trigger_yield ntid
  .

  Definition join: nat -> itree hmodE (option SAny.t) :=
    fun tid =>
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

  Definition get_tid: unit -> itree hmodE nat :=
    fun _ =>
      'my_tid : nat <- cgetU v_tid;;
      Ret my_tid
  .

  Definition trigger_Yield (nxt_tid : nat) : itree hmodE unit :=
    my_tid <- trigger (Yield nxt_tid);;
    cput v_tid my_tid
  .
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some SchHdr._spawn,  (false, wmask_all, scopes, (None, cfunU (_spawn trigger_Yield))));
     (Some SchHdr.spawn,   (false, wmask_all, scopes, (None, cfunU spawn)));
     (Some SchHdr.yield,   (false, wmask_all, scopes, (None, cfunU (yield trigger_Yield))));
     (Some SchHdr.join,    (false, wmask_all, scopes, (None, cfunU join)));
     (Some SchHdr.get_tid, (false, wmask_all, scopes, (None, cfunU get_tid)))].

  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_ths, ([(0, None)]: thslist)↑); (v_tid, 0↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).

End SchI. End SchI.

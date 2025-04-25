Require Import CRIS SchHeader.
Require Import HelpingHeader.

Set Implicit Arguments.

Module HelpingOn.
Section HelpingOn.
  Context `{Σ: GRA}.

  Definition scopes := [Helping.mn].
  Definition v_reqs := Helping.mn ↯ "reqs".

  Definition joblist : Type := list (nat * (string * SAny.t)).

  Definition try_run tid : itree hmodE Any.t :=
    'reqs: joblist <- cgetU v_reqs;;
    match alist_find tid reqs with
    | None => Ret ()↑
    | Some (f,a) =>
        cput v_reqs (alist_remove tid reqs : joblist);;;
        trigger (Call f a↑);;;
        Ret ()↑
    end.

  Definition run: Any.t -> itree hmodE Any.t :=
    fun arg =>
      '(f,a): _ <- arg↓?;;
      'tid: nat <- ccallU SchHdr.get_tid ();;
      'reqs: joblist <- cgetU v_reqs;;
      cput v_reqs (alist_add tid (f,a) reqs : joblist);;;
      𝒴;;;
      try_run tid.        

  Definition help: Any.t -> itree hmodE Any.t :=
    fun _ =>
      𝒴;;;
      tid <- trigger (Choose nat);;
      try_run tid.
      
  Definition fnsems :=
    [(Helping.run,  (scopes, mk_specbody fspec_trivial run));
     (Helping.help, (scopes, mk_specbody fspec_trivial help))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_reqs, ([]: joblist)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).  
  
End HelpingOn.
End HelpingOn.

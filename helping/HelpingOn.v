Require Import CRIS SchHeader.
Require Import HelpingHeader.

Set Implicit Arguments.

Module HelpingOn.
Section HelpingOn.
  Context `{Σ: GRA}.

  Definition pureE := agE +' coreE.

  Definition trans {R} (itr: itree pureE R) : itree hmodE R
    :=
    interp (case_ (bif:=sum1) trivial_Handler
                              trivial_Handler)
      itr.  
  
  Variable mn: string.
  Variable jobID : Type.
  Variable jobcode : jobID -> itree pureE unit.

  Definition joblist : Type := list (nat * jobID).
  
  Definition scopes := [mn].
  Definition v_reqs := mn ↯ "reqs".

  Definition try_run tid : itree hmodE Any.t :=
    'reqs: joblist <- cgetU v_reqs;;
    match alist_find tid reqs with
    | None => Ret ()↑
    | Some jid =>
        cput v_reqs (alist_remove tid reqs : joblist);;;
        trans (jobcode jid);;;
        Ret ()↑
    end.

  Definition run: Any.t -> itree hmodE Any.t :=
    fun arg =>
      'jid: jobID <- arg↓?;;
      'tid: nat <- ccallU SchHdr.get_tid ();;
      'reqs: joblist <- cgetU v_reqs;;
      cput v_reqs (alist_add tid jid reqs : joblist);;;
      𝒴;;;
      try_run tid.

  Definition help: Any.t -> itree hmodE Any.t :=
    fun _ =>
      𝒴;;;
      tid <- trigger (Choose nat);;
      try_run tid.
      
  Definition fnsems :=
    [(Helping.run mn,  (scopes, mk_specbody fspec_trivial run));
     (Helping.help mn, (scopes, mk_specbody fspec_trivial help))].

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

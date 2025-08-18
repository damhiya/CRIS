Require Import CRIS SchHeader.
From CRIS.helping Require Import Header.

Module HelpingOn. Section HelpingOn.

  Context `{Σ : GRA}.

  Context (mn : string).
  Context {jobID : Type} (jobcode : jobID → itree Helping.pureE unit).

  Definition jobmap : Type := gmap nat jobID.

  Definition scopes := [mn].
  Definition v_reqs := mn ↯ "reqs".

  Definition try_run (tid : nat) : itree crisE Any.t :=
    'reqs : jobmap <- cgetU v_reqs;;
    match reqs !! tid with
    | None => Ret ()↑
    | Some jid =>
        cput v_reqs (delete tid reqs);;;
        Helping.trans (jobcode jid);;;
        Ret ()↑
    end.

  Definition run: Any.t → itree crisE Any.t :=
    λ arg,
      'jid : jobID <- arg↓?;;
      'tid : nat <- ccallU SchHdr.get_tid ();;
      'reqs : jobmap <- cgetU v_reqs;;
      cput v_reqs (<[tid := jid]> reqs);;;
      𝒴;;;
      try_run tid.

  Definition help: Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;;
      tid <- trigger (Choose nat);;
      try_run tid;;;
      𝒴;;;
      Ret ()↑.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some (Helping.run mn),  (false, wmask_all, scopes, (None, run)));
     (Some (Helping.help mn), (false, wmask_all, scopes, (None, help)))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_reqs, (∅ : jobmap)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp Mod).

End HelpingOn. End HelpingOn.

Require Import CRIS SchHeader.
From CRIS.helping Require Import Header.

Module HelpingOff. Section HelpingOff.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Context (mn : string).
  Context {jobID retID : Type}.
  Context (jobcode : jobID → itree Helping.pureE retID) (retcode : retID → Any.t).

  Definition scopes := [mn].

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      'jid : jobID <- arg↓?;;
      𝒴;;; ret <- Helping.trans (jobcode jid);;
      𝒴;;; Ret (retcode ret).

  Definition help : Any.t → itree crisE Any.t :=
    λ _, 𝒴;;; Ret ()↑.
      
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some (Helping.run mn),  (true, wmask_all, scopes, (None, run)));
     (Some (Helping.help mn), (true, wmask_all, scopes, (None, help)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp Mod).  
End HelpingOff. End HelpingOff.

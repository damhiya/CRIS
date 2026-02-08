Require Import CRIS SchHeader.
From CRIS.helping Require Import Header HelpingOn.

Module HelpingOff. Section HelpingOff.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  Context (mn : string).
  Context {jobID retID : Type}.
  Context (jobcode : jobID → itree crisE retID).

  Definition scopes : gmultiset string := {[+mn+]}.

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      'jid : jobID <- arg↓?;;
      𝒴;;; ret <- SB.sandbox (HelpingOn.msk_pure) (jobcode jid);;
      𝒴;;; Ret ret↑.

  Definition help : Any.t → itree crisE Any.t :=
    λ _, 𝒴;;; Ret ()↑.
      
  Definition fnsems : fnsemmap :=
    {[Some (Helping.run mn) := Some (msk_scp scopes msk_true, (None, run));
      Some (Helping.help mn) := Some (msk_scp scopes msk_true, (None, help))
    ]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End HelpingOff. End HelpingOff.

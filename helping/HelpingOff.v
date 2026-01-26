Require Import CRIS SchHeader.
From CRIS.helping Require Import Header HelpingOn.

Module HelpingOff. Section HelpingOff.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

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
      
  Definition fnsems : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some (Helping.run mn) := Some (msk_scp scopes msk_true, (Some fspec_trivial, run));
      Some (Helping.help mn) := Some (msk_scp scopes msk_true, (Some fspec_trivial, help));
      Some (Helping.yield mn) := Some (msk_scp scopes msk_true, (None, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try done.
  Next Obligation. rewrite ?omap_insert omap_empty /=. mod_tac scope_solver. Qed.

  Definition t sp := SMod.to_mod sp Mod.
End HelpingOff. End HelpingOff.

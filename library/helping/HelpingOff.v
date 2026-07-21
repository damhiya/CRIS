From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader.
From CRIS.helping Require Export HelpingHeader.

Module HelpingOff. Section HelpingOff.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Context (mn : string).
  Context (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)).

  Definition scopes : list string := [mn].

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      '(N, arg) : option namespace * SAny.t <- arg↓?;;
      ret <- ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobcode arg)) arg;;
      𝒴@{N};;; Ret ret↑.

  Definition help : Any.t → itree crisE Any.t :=
    λ arg, N <- arg↓?;; 𝒴@{N};;; Ret ()↑.
      
  Definition fnsems : fnsemmap :=
    {[funid (Helping.run mn) # (msk_scp scopes msk_true, (None, run));
      funid (Helping.help mn) # (msk_scp scopes msk_true, (None, help))
    ]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HelpingOff. End HelpingOff.

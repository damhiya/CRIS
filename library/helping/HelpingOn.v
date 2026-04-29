Require Import CRIS SchHeader SchI.
Require Export HelpingHeader.

(* Helping module *)
Module HelpingOn. Section HelpingOn.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).
  Context (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)).

  Definition scopes : list string := [mn].
  Definition v_reqs : key := (mn, "reqs").

  Definition try_run (reqid : nat) : itree crisE Any.t :=
    'reqs : gmap nat help_state <- cgetU v_reqs;;
    match reqs !! reqid with
    | Some (Pend N arg) =>
        cput v_reqs (<[reqid := InProgress]> reqs);;;
        ret <- ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobcode arg)) arg;;
        'reqs : gmap nat help_state <- cgetU v_reqs;;
        cput v_reqs (<[reqid := Done ret]> reqs);;;
        Ret ret↑
    | Some (Done ret) => Ret ret↑
    | _ => triggerNB
    end.

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      '(N, arg) : option namespace * SAny.t <- arg↓?;;
      'reqs : gmap nat help_state <- cgetU v_reqs;;
      let reqid := fresh (dom reqs) in
      cput v_reqs (<[reqid := Pend N arg]> reqs);;;
      𝒴@{N};;; 
      try_run reqid.

  Definition help : Any.t → itree crisE Any.t :=
    λ arg,
      'Nhelp : option namespace <- arg↓?;;
      reqid <- trigger (Choose nat);;
      'reqs : gmap nat help_state <- cgetU v_reqs;;
      match reqs !! reqid with
      | Some (Pend N arg) =>
          cput v_reqs (<[reqid := InProgress]> reqs);;;
          option_Guarantee Nhelp;;;
          option_Assume N;;;
          ret <- ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobcode arg)) arg;;
          option_Guarantee N;;;
          option_Assume Nhelp;;;
          'reqs : gmap nat help_state <- cgetU v_reqs;;
          cput v_reqs (<[reqid := Done ret]> reqs);;;
          Ret tt↑
      | Some (Done ret) => Ret tt↑
      | _ => triggerNB
      end.

  Definition fnsems : fnsemmap :=
    {[funid (Helping.run mn) # (msk_scp scopes msk_true, (None, run));
      funid (Helping.help mn) # (msk_scp scopes msk_true, (None, help))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_reqs # (∅ : gmap nat help_state)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End HelpingOn. End HelpingOn.

Module HelpingDummy. Section HelpingDummy.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).
  Definition scopes : list string := [mn].

  Definition fnsems : fnsemmap :=
    {[funid (Helping.run mn) # (msk_real (msk_scp scopes msk_true), (None, λ _, triggerNB));
      funid (Helping.help mn) # (msk_real (msk_scp scopes msk_true), (None, λ _, triggerNB))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End HelpingDummy. End HelpingDummy.

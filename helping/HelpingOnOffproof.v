Require Import CRIS.
Require Import SchHeader SchA.
Require Import HelpingHeader HelpingOn HelpingOff.
Require Import CallFilter.

Section Helping.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_schG: !schG}.

  Theorem helping_onoff_correct mn jobID (jobs: jobID -> _) msk u sp sp_s sp_u
    (UserInSp: sp_sub sp_u sp_s)
    (SchInSp : sp_incl (SchAS.sp u sp_u) sp_s)
    :
    ctx_refines
      ((HelpingOff.t mn jobs sp) ★ (SchAPure.t u sp_s) ★ (CFilter.filter msk (SchA.t u sp_s sp_u)), emp%I)
      ((HelpingOn.t  mn jobs sp) ★ (SchAPure.t u sp_s) ★ (CFilter.filter msk (SchA.t u sp_s sp_u)), emp%I).
  Proof.
  Admitted.

End Helping.

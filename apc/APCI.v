Require Import CRIS.
Require Import APCHeader.

Set Implicit Arguments.

Module APCI. Section APCI.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  Definition scp : list string := ["APC"].

  Definition fnsems : fnsemmap :=
    {[Some APCHdr.apc # (msk_real (msk_scp scp msk_true), (None, fbody_trivial))]}.
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End APCI. End APCI.

Require Import CRIS.

Require Import APCHeader APC APCI APCA.

Set Implicit Arguments.

Module APCC. Section APCC.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.
  Import APC APCI APCA.

  Definition Sp : specmap :=
    {[speckey_fn APCHdr.apc := fspec_to_rel APCA.apc_spec]}.

  Definition fnsems : fnsemmap :=
    {[Some APCHdr.apc := Some (msk_scp scp msk_true, (fsp_some APCA.apc_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := SMod.to_mod Sp smod.
End APCC. End APCC.

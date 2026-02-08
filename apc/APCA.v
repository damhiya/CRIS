Require Import CRIS.

Require Import APCHeader APC APCI.

Set Implicit Arguments.

Module APCA. Section APCA.
  Import APC APCI.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  Definition apc_body SpPure : Ord.t → itree crisE () :=
    λ dep_ord, APC dep_ord SpPure.

  Definition apc_spec : fspec :=
    fspec_mk
      (λ (o: Ord.t) varg arg, ⌜varg = o↑ ∧ arg = varg⌝)%I
      (λ _ _ _, True)%I.

  Definition Sp : specmap :=
    {[speckey_fn APCHdr.apc := fspec_to_rel apc_spec]}.

  Definition fnsems (SpPure: specmap) : fnsemmap :=
    {[Some APCHdr.apc := Some (msk_scp scp msk_true, (fsp_some apc_spec, (cfunN (apc_body SpPure))))]}.

  Program Definition smod SpPure : SMod.t := {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems SpPure;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with rewrite /APCI.smod /=; mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t SpPure Sp := SMod.to_mod Sp (smod SpPure).
End APCA. End APCA.

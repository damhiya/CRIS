Require Import CRIS.
Require Import APCHeader.

Set Implicit Arguments.

Module APCI. Section APCI.
  Context `{Σ: GRA}.

  Definition scopes := ["APC"].

  Definition fnsems : fnsems_type :=
    [(Some APCHdr.apc, (false, wmask_all, scopes, (None, fbody_trivial)))].
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End APCI. End APCI.

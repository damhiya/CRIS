Require Import CRIS.
Require Import APCHeader.

Set Implicit Arguments.

Module APCI. Section APCI.
  Context `{Σ: GRA}.

  Definition scopes := ["APC"].

  Definition fnsems :=
    [(APCHdr.apc, (wmask_all, scopes, @fbody_trivial pmodE _))].
  
  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End APCI. End APCI.

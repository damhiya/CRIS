Require Import CRIS.
Require Import APCHeader.

Set Implicit Arguments.

Module APCI. Section APCI.
  Context `{Σ: GRA}.

  Definition scopes := ["APC"].

  Definition trivial_body : Any.t → itree pmodE Any.t :=
    λ _, trigger (Choose _).

  Definition fnsems :=
    [(APCName.apc, (scopes, trivial_body))].
  
  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End APCI. End APCI.
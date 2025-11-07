Require Import CRIS.
Require Import CallFilter.
Require Import NDSMainI.
Set Implicit Arguments.

Module NDSMainA. Section NDSMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.

  Definition fnsems : fnsems_type :=
    [(None, (true, wmask_all, [], (None, NDSMainI.main)))].

  Program Definition smod: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems;
      SMod.initial_st := [];
    |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp smod).

End NDSMainA. End NDSMainA.

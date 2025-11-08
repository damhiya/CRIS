Require Import CRIS.
Require Import CallFilter.
Require Import SchHeader SchA.
Require Import RRSHeader RRSA.
Require Import RRSNodeHeader RRSNodeA.
Require Import MemHeader MemA.
Require Import NDSMainI.
Set Implicit Arguments.

Module NDSMainA. Section NDSMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Definition main_spec E : fspec :=
    fspec_winv E
      (fspec_simple (λ (_: unit),
           (λ varg, ⌜varg = tt↑⌝ ∗ RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0),
           λ vret, ⌜vret = tt↑⌝)%I)).

  Definition fnsems E : fnsems_type :=
    [(None, (true, wmask_all, [], (Some (main_spec E), NDSMainI.main)))].

  Program Definition smod E: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems E;
      SMod.initial_st := [];
    |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t E sp := Seal.sealing CRIS (SMod.to_mod sp (smod E)).

End NDSMainA. End NDSMainA.

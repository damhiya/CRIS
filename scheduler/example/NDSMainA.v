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

  Definition sp : spl_type :=
    Seal.sealing CRIS [(None, Some fspec_trivial)].

  Definition fnsems : fnsems_type :=
    [(None, (true, wmask_all, [], (Some fspec_trivial, NDSMainI.main)))].

  Program Definition smod: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems;
      SMod.initial_st := [];
    |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0).

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp smod).

End NDSMainA. End NDSMainA.

Require Import CRIS.
Require Import SchHeader SchA.
Require Import RRSHeader RRSA.
Require Import RRSNodeHeader RRSNodeA.
Set Implicit Arguments.

Module NDSMainI. Section NDSMainI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.

  Definition main : Any.t → itree crisE Any.t :=
    λ _, trigger (Call SchHdr.spawn (RRSHdr.init, RRSNodeHdr.f_main↑↑)↑);;; Ret tt↑. 

  Definition fnsems : fnsems_type :=
    [(None, (false, wmask_all, [], (None, main)))].

  Program Definition smod: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems;
      SMod.initial_st := [];
    |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).

End NDSMainI. End NDSMainI.


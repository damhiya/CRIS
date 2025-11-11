Require Import CRIS.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.
Require Import FaaHeader.

Module FaaI. Section FaaI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : list string := [].

  Definition faa2 : list val → itree crisE unit :=
    λ arg,
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition fnsems : fnsems_type :=
    [(Some FaaHdr.faa2, (false, wmask_all, scopes, (None, cfunU faa2)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End FaaI. End FaaI.
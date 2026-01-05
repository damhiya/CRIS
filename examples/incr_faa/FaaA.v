Require Import CRIS.
Require Export ImpPrelude MemHeader MemA SchHeader.
Require Export FaaHeader.

Module FaaA. Section FaaA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG}.

  Definition scopes : gmultiset string := ∅.

  Definition faa2 : list val → itree crisE unit :=
    λ arg,
      '(b, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;; Ret tt.

  Definition fnsems : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some FaaHdr.faa2 := Some (msk_scp scopes msk_true, (None, cfunU faa2))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try done.
  Next Obligation. rewrite ?omap_insert /= omap_empty. mod_tac scope_solver. Qed.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End FaaA. End FaaA.
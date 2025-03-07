Require Import CRIS.
Require Import InputHeader.

Set Implicit Arguments.

Module InputAS.
Section InputAS.
  Context `{Σ: GRA}.

  Definition spc: alist string fspec :=
    Seal.sealing CRIS [(InputName.input, fspec_trivial)].
  
  Lemma spc_nodup: List.NoDup (List.map fst spc).
  Proof.
    unfold spc. unseal CRIS. prove_nodup.
  Qed.

End InputAS. End InputAS.

Module InputA. Section InputA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition input: Any.t -> itree hmodE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input" tt);;
      trigger (@IO _ unit "Print" i);;;
      Ret i↑.

  Definition scopes := [InputName.mn].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(InputName.input, (scopes, mk_specbody fspec_trivial input))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.
    
  Definition InitRes : Σ := ε.

  Definition t spc := Seal.sealing CRIS (SMod.to_hmod emp spc Mod).
End InputA. End InputA.

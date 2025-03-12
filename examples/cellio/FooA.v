Require Import CRIS.
Require Import MainHeader CellioHeader InputHeader FooHeader.

Require Import CellioA MainA InputA.

Set Implicit Arguments.

Module FooAS.
Section FooAS.
  Context `{Σ: GRA}.

  Definition spc: alist string fspec :=
    Seal.sealing CRIS [(FooName.foo, fspec_trivial)].
  
  Lemma spc_nodup: List.NoDup (List.map fst spc).
  Proof.
    unfold spc. unseal CRIS. prove_nodup.
  Qed.

End FooAS. End FooAS.

Module FooA. Section FooA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.  

  (* Don't need to restrict unknown functions not to call myself anymore. *)
  Variable foo: Any.t -> itree hmodE Any.t.
  
  Definition scopes := [FooName.mn].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(FooName.foo, (scopes, mk_specbody fspec_trivial foo))].

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
End FooA. End FooA.

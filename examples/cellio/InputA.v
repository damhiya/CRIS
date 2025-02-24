Require Import CRIS.
Require Import InputHeader.

Set Implicit Arguments.

Module InputAS.
Section InputAS.
  Context `{Σ: GRA}.

  Definition Spc: alist string fspec :=
    Seal.sealing CRIS [(InputName.input, fspec_trivial)].
  
  Lemma Spc_nodup: List.NoDup (List.map fst Spc).
  Proof.
    unfold Spc. unseal CRIS. prove_nodup.
  Qed.

End InputAS. End InputAS.

Module InputA. Section InputA.
  Context `{Σ: GRA}.

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

  Definition t Spc := Seal.sealing CRIS (SMod.to_hmod ginv_emp Spc Mod).
End InputA. End InputA.

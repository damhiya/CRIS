Require Import CRIS.
Require Import InputHeader.

Set Implicit Arguments.

Module InputAS.
Section InputAS.
  Context `{Σ: GRA}.

  Definition Stb: alist string fspec :=
    Seal.sealing CRIS [(InputName.input, fspec_trivial)].
  
  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal CRIS. prove_nodup.
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

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := InputSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp Σ :=
    λ _, emp%I.
    
  Definition InitRes : Σ := ε.

  Definition t ginv Stb := Seal.sealing CRIS (SMod.to_hmod ginv Stb Mod).
End InputA. End InputA.

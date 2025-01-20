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

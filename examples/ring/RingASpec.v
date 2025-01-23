Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader.

Set Implicit Arguments.

Module RingAS. Section RingAS.
  Context `{Σ : GRA}.

  Definition Stb : alist string fspec :=
    Seal.sealing CRIS [(RingName.init, fspec_trivial);
                       (RingName.get_size, fspec_trivial);
                       (RingName.enqueue, fspec_trivial);
                       (RingName.dequeue, fspec_trivial)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal CRIS. prove_nodup.
  Qed.
  
End RingAS.

Global Hint Unfold Stb : stb.

End RingAS.

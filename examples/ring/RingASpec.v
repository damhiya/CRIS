(* Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader.

Set Implicit Arguments.

Module RingAS. Section RingAS.
  Context `{Σ : GRA}.

  Definition Stb : alist string fspec :=
    Seal.sealing "ccr" [(RingName.init, fspec_trivial);
                          (RingName.get_size, fspec_trivial);
                          (RingName.enqueue, fspec_trivial);
                          (RingName.dequeue, fspec_trivial)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.
  
End RingAS.

Global Hint Unfold Stb : stb.

End RingAS. *)

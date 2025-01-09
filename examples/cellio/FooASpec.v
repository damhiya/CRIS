(* Require Import CRIS.

Require Import FooHeader.

Set Implicit Arguments.

Module FooAS.
Section FooAS.
  Context `{Σ: GRA}.

  Definition Stb: alist string fspec :=
    Seal.sealing "ccr" [(FooName.foo, fspec_trivial)].
  
  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End FooAS. End FooAS. *)

Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonASpec.

Set Implicit Arguments.

Module CannonMainAS.
Section Main.
  Import CannonAS.
  Context `{!sinvGS Σ Γ α β τ, !CannonAS.GS Γ}.

  Definition main_spec: fspec :=
    fspec_simple (fun (_: unit) =>
        ((fun varg => (⌜varg = ([]: list val)↑⌝ ∗ Ball)%I),
        (fun vret => (⌜vret = tt↑⌝)%I))).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(MainName.main, main_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End Main.
End CannonMainAS.

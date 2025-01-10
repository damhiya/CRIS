Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonASpec.

Set Implicit Arguments.

Module CannonMainAS. Section CannonMainAS.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Definition main_spec: fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, ⌜arg = ([]: list val)↑⌝ ∗ Ball),
      (λ ret, ⌜ret = tt↑⌝))
    )%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr" [(MainName.main, main_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof. unfold Stb. unseal "ccr". prove_nodup. Qed.
End CannonMainAS. End CannonMainAS.
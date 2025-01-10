Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonASpec.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.
  Local Existing Instance cannon_inG.
  Definition init_res : Σ := CRIS.own.iRes_singleton 1%positive (◯E tt).

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, ⌜arg = tt↑⌝ ∗ Ball),
      (λ ret, ⌜ret = tt↑⌝))
    )%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr" [(MainName.main, main_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof. unfold Stb. unseal "ccr". prove_nodup. Qed.
End MainAS. End MainAS.
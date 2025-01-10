Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.


Set Implicit Arguments.

Local Definition RA : ucmra := excl_authR unitO.
Class CannonAGΓ (Γ : HRA) := {
  #[local] map_inG :: inG (excl_authR unitO) Γ;
}.
Definition CannonAΓ : HRA := #[excl_authR unitO].
Global Instance subG_GΓ {Γ : HRA} : subG CannonAΓ Γ → CannonAGΓ Γ.
Proof. solve_inG. Qed.

Module CannonAS. Section CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.
  
  Definition Ready : iProp Σ := own 1%positive (●E tt).
  Definition Ball : iProp Σ := own 1%positive (◯E tt).
  Definition Fired : iProp Σ := own 1%positive ((●E tt) ⋅ (◯E tt)).

  Lemma ReadyBall : Ready ∗ Ball ⊢ Fired.
  Proof. rewrite /Ready /Ball /Fired. iIntros "[B W]". iSplitL "B"; iFrame. Qed.

  Lemma FiredReady : Ready ∗ Fired ⊢ False.
  Proof.
    rewrite /Ready /Fired. iIntros "[B0 [B1 W]]". iCombine "B0 B1" as "X" gives %FALSE.
    rewrite excl_auth_auth_op_valid // in FALSE.
  Qed.

  Lemma FiredBall : Ball ∗ Fired ⊢ False.
  Proof.
    rewrite /Ball /Fired. iIntros "[W0 [B W1]]". iCombine "W0 W1" as "X" gives %FALSE.
    rewrite excl_auth_frag_op_valid // in FALSE.
  Qed.

  Definition fire_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, (⌜arg = ([]: list val)↑⌝ ∗ Ball)),
      (λ ret, (⌜ret = (1: Z)%Z↑⌝)))
    )%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr" [(CannonName.fire, fire_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof. unfold Stb. unseal "ccr". prove_nodup. Qed.
End CannonAS. End CannonAS.

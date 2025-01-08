Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.


Set Implicit Arguments.

Module CannonAS.
Section CannonAS.
  Local Definition RA : ucmra :=
    excl_authR unitO.
  Class GpreΓ (Γ : HRA) := {
    #[global] map_inG :: inG (excl_authR unitO) Γ;
  }.
  Class GS (Γ: HRA) := {
    #[global] RA_inG :: inG CannonAS.RA Γ;
    map_name : positive;
  }.
  Definition GΓ : HRA := #[excl_authR unitO].
  Global Instance subG_GΓ {Γ} : subG GΓ Γ → GpreΓ Γ.
  Proof. solve_inG. Qed.

  Context `{!sinvGS Σ Γ α β τ, !CannonAS.GS Γ}.

  
  Definition Ready: iProp Σ := own map_name (●E tt).
  Definition Ball: iProp Σ := own map_name (◯E tt).
  Definition Fired: iProp Σ := own map_name ((●E tt) ⋅ (◯E tt)).

  Lemma ReadyBall: 
    Ready ∗ Ball ⊢ Fired.
  Proof.
    rewrite /Ready /Ball /Fired. unseal "CannonA".
    iIntros "[B W]". iSplitL "B"; iFrame.
  Qed.

  Lemma FiredReady: 
    Ready ∗ Fired ⊢ False.
  Proof. 
    rewrite /Ready /Fired. unseal "CannonA".
    iIntros "[B0 [B1 W]]". iCombine "B0 B1" as "X" gives %FALSE.
    rewrite excl_auth_auth_op_valid // in FALSE.
  Qed.

  Lemma FiredBall: 
    Ball ∗ Fired ⊢ False.
  Proof.
    rewrite /Ball /Fired. unseal "CannonA".
    iIntros "[W0 [B W1]]". iCombine "W0 W1" as "X" gives %FALSE.
    rewrite excl_auth_frag_op_valid // in FALSE.
  Qed.

  Definition fire_spec: fspec :=
    fspec_simple (fun (_: unit) =>
        ((fun varg => (⌜varg = ([]: list val)↑⌝ ∗ Ball)%I),
        (fun vret => (⌜vret = (1: Z)%Z↑⌝)%I))).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(CannonName.fire, fire_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End CannonAS.
End CannonAS.

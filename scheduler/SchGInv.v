Require Import CRIS.

Require Import SchInvariants.

Set Implicit Arguments.

Section GINV.

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition sch_ginv (univ: positive): invspec :=
    fun _ => (∃ n, wsats univ n ⊤)%I.

End GINV.

From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod.

From CRIS.iris_system Require Import lib.allocs.
From iris.proofmode Require Import proofmode.

Definition refines_lmod (ms_tgt ms_src: LMod.t) : Prop :=
  Beh.of_itree (LMod.compile ms_tgt tt↑) <1=
  Beh.of_itree (LMod.compile ms_src tt↑).

Section MOD_BEHAVIOR.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Program Definition Beh_def (M : Mod.t) (t : Tr.t) : iProp Σ :=
    {| uPred_holds :=
        fun r => forall r', ✓ r' ->
                    r ≼ r' ->
                    Beh.of_itree (LMod.compile (Mod.to_lmod M r') tt↑) t
    |}.
  Next Obligation.
    intros ???? H ????. eapply H; et. etrans; et.
  Qed.
  Definition Beh_aux : seal (@Beh_def). Proof. by eexists. Qed.
  Definition Beh := Beh_aux.(unseal).
  Definition Beh_unseal : @Beh = @Beh_def := Beh_aux.(seal_eq).

End MOD_BEHAVIOR.

Section REFINEMENT.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition refines (Mt Ms : Mod.t) : iProp Σ :=
      ⌜ Mod.wf Mt ⌝ → ⌜ Mod.wf Ms ⌝ ∧ (winv (∅,∅) -∗ ∀ t, Beh Mt t -∗ Beh Ms t).

  Definition ctx_refines (Mt Ms : Mod.t) : iProp Σ :=
    ∀ (Ctx : Mod.t), refines (Mt ★ Ctx) (Ms ★ Ctx).

End REFINEMENT.

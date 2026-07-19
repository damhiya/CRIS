From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod.

From CRIS.iris_system Require Import lib.allocs.
From iris.proofmode Require Import proofmode.

Definition refines_lmod (ms_tgt ms_src: LMod.t) : Prop :=
  Beh.of_itree (LMod.compile ms_tgt tt↑) <1=
  Beh.of_itree (LMod.compile ms_src tt↑).

Section REFINEMENT.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition _refines (Mt Ms : Mod.t) : Σ -> Prop :=
    fun r => Mod.wf Mt ->
          Mod.wf Ms /\
            forall rt rs,
              (Own rs ⊢ Own rt ∗ Own r ∗ winv (∅,∅)) ->
              ✓ rs -> refines_lmod (Mod.to_lmod Mt rt) (Mod.to_lmod Ms rs).

  Lemma _refines_mono Mt Ms
    : ∀ (x1 x2 : Σ), _refines Mt Ms x1 → x1 ≼ x2 → _refines Mt Ms x2.
  Proof.
    unfold _refines.
    intros x1 x2 M_LE x_LE WFT.
    specialize (M_LE WFT). destruct M_LE as [WFS M_LE]. split; et.
    intros rt rs SPLIT V. eapply M_LE; et.
    iIntros "H".
    iPoseProof (SPLIT with "H") as "($ & H & $)".
    iApply Own_extends; et.
  Qed.

  Definition refines_def (Mt Ms : Mod.t) : iProp Σ :=
    {| uPred_holds := _refines Mt Ms; uPred_mono := _refines_mono Mt Ms |}.
  Definition refines_aux : seal (@refines_def). Proof. by eexists. Qed.
  Definition refines := refines_aux.(unseal).
  Definition refines_unseal : @refines = @refines_def := refines_aux.(seal_eq).

  Definition ctx_refines (Mt Ms : Mod.t) : iProp Σ :=
    ∀ (Ctx : Mod.t), refines (Mt ★ Ctx) (Ms ★ Ctx).

End REFINEMENT.

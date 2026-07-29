From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import Mod.
From CRIS.simulations.lsim Require Import LSim.

Section LSIM_MOD.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Program Definition lsim_mod_def (Ms Mt : Mod.t) : iProp Σ :=
    {| uPred_holds := fun r =>
        Mod.wf Mt ->
        Mod.wf Ms /\
          forall rt rs,
            ✓ rs ->
            (Own rs ⊢ Own rt ∗ Own r ∗ winv (∅,∅)) ->
            ∃ lw, LSim.lsim_lmod
              (Mod.to_lmod Ms rs) (Mod.to_lmod Mt rt) lw
    |}.
  Next Obligation.
    intros Ms Mt x1 x2 H LE WFT. specialize (H WFT).
    destruct H as [WFS H]. split; et.
    intros rt rs VALID SPLIT. eapply H; et.
    rewrite SPLIT.
    iIntros "($ & H & $)". iApply Own_extends; et.
  Qed.
  Definition lsim_mod_aux : seal (@lsim_mod_def). Proof. by eexists. Qed.
  Definition lsim_mod := lsim_mod_aux.(unseal).
  Definition lsim_mod_unseal : @lsim_mod = @lsim_mod_def := lsim_mod_aux.(seal_eq).

  Lemma lsim_mod_intro
    Ms Mt P
    (SIM : Mod.wf Mt ->
      Mod.wf Ms /\
        forall rt rs,
          ✓ rs ->
          (Own rs ⊢ Own rt ∗ P ∗ winv (∅,∅)) ->
          ∃ lw, LSim.lsim_lmod
            (Mod.to_lmod Ms rs) (Mod.to_lmod Mt rt) lw)
    : P ⊢ lsim_mod Ms Mt.
  Proof.
    rewrite lsim_mod_unseal.
    eapply entails_pointwise. intros r VALID HP.
    eapply Own_general_completeness. cbn.
    intros WFT. specialize (SIM WFT). destruct SIM as [WFS SIM].
    split; et.
    intros rt rs VRS SPLIT. eapply SIM; et.
    rewrite SPLIT.
    iIntros "($ & R & $)". iApply HP. done.
  Qed.

End LSIM_MOD.

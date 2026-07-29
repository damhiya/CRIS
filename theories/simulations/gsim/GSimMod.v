From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import LMod Mod.
From CRIS.simulations.gsim Require Import GSimAdequacy.

Section GSIM_MOD.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Program Definition gsim_mod_def (Ms Mt : Mod.t) : iProp Σ :=
    {| uPred_holds := fun r =>
                        Mod.wf Mt -> Mod.wf Ms /\
                                      forall rt rs,
                                        ✓ rs ->
                                        (Own rs ⊢ Own rt ∗ Own r ∗ winv (∅,∅)) ->
                                        gsim eq smj_bot smj_bot
                                          (LMod.compile (Mod.to_lmod Ms rs) ()↑)
                                          (LMod.compile (Mod.to_lmod Mt rt) ()↑)
    |}.
  Next Obligation.
    intros Ms Mt x1 x2 H LE WFT. specialize (H WFT).
    destruct H as [WFS H]. split; et.
    intros rt rs VALID SPLIT. eapply H; et.
    rewrite SPLIT.
    iIntros "($ & H & $)". iApply Own_extends; et.
  Qed.
  Definition gsim_mod_aux : seal (@gsim_mod_def). Proof. by eexists. Qed.
  Definition gsim_mod := gsim_mod_aux.(unseal).
  Definition gsim_mod_unseal : @gsim_mod = @gsim_mod_def := gsim_mod_aux.(seal_eq).

  Lemma gsim_mod_intro
    Ms Mt P
    (SIM : Mod.wf Mt -> Mod.wf Ms /\
                         forall rt rs,
                           ✓ rs ->
                           (Own rs ⊢ Own rt ∗ P ∗ winv (∅,∅)) ->
                           gsim eq smj_bot smj_bot
                             (LMod.compile (Mod.to_lmod Ms rs) ()↑)
                             (LMod.compile (Mod.to_lmod Mt rt) ()↑))
    : P ⊢ gsim_mod Ms Mt.
  Proof.
    rewrite gsim_mod_unseal.
    eapply entails_pointwise. intros r VALID HP.
    eapply Own_general_completeness. cbn.
    intros WFT. specialize (SIM WFT). destruct SIM as [WFS SIM].
    split; et.
    intros rt rs VRS SPLIT. eapply SIM; et.
    rewrite SPLIT.
    iIntros "($ & R & $)". iApply HP. done.
  Qed.

End GSIM_MOD.

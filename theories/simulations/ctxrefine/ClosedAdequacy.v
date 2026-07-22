From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.

From CRIS.modules Require Import Mod.
From CRIS.simulations.gsim Require Import GSimAdequacy.
From CRIS.simulations.lsim Require Import LSimAdequacy.
From CRIS.simulations.msim Require Import MSimCommon ISim ISimAdequacy.
From CRIS.simulations.ctxrefine Require Import CtxRefine.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem gsim_closed_adequacy
    (Mt Ms : Mod.t) (IC : iProp Σ)
    (SIM : Mod.wf Mt ->
           Mod.wf Ms /\
             forall rt rs,
               ✓ rs ->
               (Own rs ⊢ Own rt ∗ IC ∗ winv (∅,∅)) ->
               gsim
                 eq smj_bot smj_bot
                 (LMod.LMod.compile (Mod.to_lmod Ms rs) () ↑)
                 (LMod.LMod.compile (Mod.to_lmod Mt rt) () ↑))
    : IC ⊢ refines Mt Ms.
  Proof.
    eapply entails_pointwise. intros x Vx Hx.
    eapply Own_general_completeness. rewrite refines_unseal.
    intros WFT. specialize (SIM WFT). destruct SIM as [WFS SIM].
    split; et. intros rt rs Hrs Vrs.
    unfold refines_lmod. eapply gsim_adequacy.
    eapply SIM; et. rewrite Hrs Hx; et.
  Qed.

  Theorem lsim_closed_adequacy
    (Mt Ms : Mod.t) (IC : iProp Σ)
    (SIM : Mod.wf Mt ->
           Mod.wf Ms /\
             forall rt rs,
               ✓ rs ->
               (Own rs ⊢ Own rt ∗ IC ∗ winv (∅,∅)) ->
               inhabited (LSim.lsim_mod (Mod.to_lmod Ms rs) (Mod.to_lmod Mt rt)))
    : IC ⊢ refines Mt Ms.
  Proof.
    eapply gsim_closed_adequacy.
    intros WFT. specialize (SIM WFT). destruct SIM as [WFS SIM]. split; et.
    intros rt rs Vrs Hrs. specialize (SIM rt rs Vrs Hrs). destruct SIM.
    eapply lsim_adequacy. et.
  Qed.

  Theorem ISim_closed_adequacy
    (Mt Ms : Mod.t) IC Ist
    (SIM : ISim.t closed Ms Mt IC Ist)
    : IC ⊢ refines Mt Ms.
  Proof.
    eapply lsim_closed_adequacy. intros WFT.
    split. { eapply ISim_wf; et. }
    intros rt rs VALID SPLIT. econs.
    eapply ISim_adequacy; et.
    rewrite SPLIT; et.
  Qed.

End ADEQUACY.

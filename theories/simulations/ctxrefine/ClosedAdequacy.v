From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.

From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon.
From CRIS.simulations.lsim Require Import LSim LSimAdequacy.
From CRIS.simulations.msim Require Import ISim ISimFacts ISimAdequacy.
From CRIS.simulations.ctxrefine Require Import CtxRefine.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem closed_adequacy (Mt Ms : Mod.t) IC Ist :
    ISim.t closed Ms Mt IC Ist ->
    IC ⊢ refines Mt Ms.
  Proof.
    intros SIM.
    eapply entails_pointwise. intros x _ x_IC.
    eapply Own_general_completeness.
    rewrite refines_unseal.
    intros WF. split. { eapply ISim_wf; et. }
    intros rt rs SPLIT VALID.
    unfold refines_lmod. eapply lsim_adequacy.
    eapply ISim_adequacy; et.
    iIntros "H". iModIntro.
    iDestruct (SPLIT with "H") as "($ & H & $)".
    iApply x_IC. done.
  Qed.

End ADEQUACY.

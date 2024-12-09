Require Import Coqlib ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import IPM STB sProp sWorld.
Require Import Events Behavior.

Require Import ISim ITactics SMod HMod PMod Events STB.
Require Import Mod ModSim ModSimFacts.
Require Import CellioHeader CellioA CellioI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!Inv.t Σ Γ α β τ, !G Γ, !CellioA.G Γ}.
  Notation iProp := (iProp Σ).

  Variable ginv: Sk.t -> invspec.
  Variable StbG: Sk.t -> gname -> option fspec.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Notation CellioI := (CellioI.t).
  Local Notation CellioA := (CellioA.t ginv StbG).

  Lemma simF_set : HSim.sim_fun CellioA CellioI Ist CellioName.set.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%"; subst.
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    step.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    steps_r. hss. steps_l. forces_l.
    iSplitL "C"; eauto.
    
    steps_l. forces_l.
    iSplitL ""; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma simF_get:
    HSim.sim_fun CellioA CellioI Ist CellioName.get.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%"; subst.
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.

    steps_r. hss. steps_r. forces_l.
    iSplitL "ASM'"; eauto.
    
    steps_l. forces_l.
    iSplitL ""; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Theorem sim: HSim.t CellioA CellioI CellioA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set.
    - apply simF_get.
  Qed.

End CellioIA. End CellioIA.

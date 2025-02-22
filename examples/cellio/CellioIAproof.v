Require Import CRIS.
Require Import CellioHeader CellioA CellioI.
Require Import InputA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Variable SpcG: string -> option fspec.
  Hypothesis InputInSpcG: spc_incl InputAS.Spc SpcG.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Notation CellioI := (CellioI.t).
  Local Notation CellioA := (CellioA.t SpcG).

  Lemma simF_set : HSim.sim_fun open CellioA CellioI Ist CellioName.set.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%"; subst.

    force_l tt. forces_l. iSplitL ""; eauto.
    call "IST"; eauto.
    steps_l. iDestruct "ASM" as "%"; subst.

    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    forces_l. iSplitL "C"; eauto.

    steps_r. hss. steps_r. steps_l. forces_l.
    iSplitL ""; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma simF_get:
    HSim.sim_fun open CellioA CellioI Ist CellioName.get.
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
  
  Theorem sim: HSim.t open CellioA CellioI CellioA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CellioIA. End CellioIA.

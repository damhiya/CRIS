Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader CellI CellA.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Simulation Proof *)
Module CellIA. Section CellIA.
  Import CellAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellAGΓ Γ}.

  Variable idx : nat.

  Definition Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    (λ _ st_src st_tgt,
       ∃ vany v, 
        ⌜st_tgt = [(CellI.v_cv idx, vany)]⌝
        ∗ ((cell idx v ∗ auth idx v)
          ∨ (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  Variable ginv : invspec.
  Variable SpcCell : string -> option fspec.

  Local Notation CellA := (CellA.t idx ginv SpcCell).
  Local Notation CellI := (CellI.t idx).

  Lemma simF_get : HSim.sim_fun open CellA CellI Ist (CellName.get idx).
  Proof.
    init_simF.

    (* SRC: handle the IST of the Cell and the precond of get *)
    steps_l. iDestruct "ASM" as "((% & C) & %)". subst. hss.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss. rename q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    steps_r. hss. steps_r.    
    forces_l. steps_l. forces_l.
    iSplitL "C". { eauto. }

    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  Qed.

  Lemma simF_set:
    HSim.sim_fun open CellA CellI Ist (CellName.set idx).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & [P|C]) & %)";
      subst; hss; rename q1 into v, q2 into v'; unfold Ist.
    { iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. hss.

      iMod (cell_auth_set with "C A") as "(C & A)".

      steps_r. hss.
      forces_l. steps_l. forces_l.
      iSplitL "C". { eauto. }

      step.
      iSplit; eauto.
      iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
    }

    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    steps_r. hss.
    forces_l. steps_l. forces_l.
    iSplitL "C". { eauto. }

    step.
    iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  Qed.

  Theorem sim : HSim.t open CellA CellI (CellA.InitCond idx) Ist.
  Proof.
    init_sim.
    - iIntros "H". iDestruct "H" as (v) "(C & A)".
      repeat iExists _. iSplit; eauto. iLeft. iFrame.
    - apply simF_get; eauto.
    - apply simF_set; eauto.
  Qed.

End CellIA. End CellIA.

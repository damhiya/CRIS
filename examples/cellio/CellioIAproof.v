Require Import CRIS.
Require Import CellioHeader CellioA CellioI.
Require Import InputA.
Require Import wsim_tactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  (* 1) universe ids of src/tgt modules *)
  Context (u_s: univ_id).
  (* 2) spc for src module *)
  Context (Spc_s : string → option fspec).
  Context (InputInSpcG : spc_incl InputAS.Spc Spc_s).
  
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Notation CellioI := (CellioI.t).
  Local Notation CellioA := (CellioA.t u_s Spc_s).

  Lemma simF_set : HSim.sim_fun open CellioA CellioI Ist CellioName.set.
  Proof.
    init_wsim u_s 0.

    w_steps_l. iDestruct "ASM" as "->".
    w_force_l tt. w_forces_l. iSplit; first eauto.

    w_call "IST"; eauto.
    w_steps_l. iDestruct "ASM" as "->".

    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    w_forces_l. iSplitL "C"; eauto.

    w_steps_r. hss. w_steps_r. w_steps_l. w_forces_l.
    iSplit; eauto.

    w_step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma simF_get : HSim.sim_fun open CellioA CellioI Ist CellioName.get.
  Proof.
    init_wsim u_s 0.

    w_steps_l. iDestruct "ASM" as "->".
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.

    w_steps_r. hss. w_steps_r.
    w_forces_l. iSplitL "ASM'"; eauto.
    
    w_steps_l. w_forces_l. iSplit; eauto.

    w_step. iSplit; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma sim : HSim.t open CellioA CellioI CellioA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
  End CellioIA.

  Section CellioIA.
    Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.
    Lemma wctxr ginv Spc_s (InputInSpc : spc_incl InputAS.Spc Spc_s) :
      w_ctx_refines (λ _, CellioA.t ginv Spc_s, CellioA.InitCond) (λ _, CellioI.t, emp%I).
    Proof. exists 1; intros u v Huv; s; eapply main_adequacy, sim; ss. Qed.
End CellioIA. End CellioIA.

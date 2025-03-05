Require Import CRIS.
Require Import CellioHeader CellioA CellioI.
Require Import InputA.
(* Require Import wsim_tactics. *)

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  (* 1) universe ids of src/tgt modules *)
  Context (u_s: univ_id).
  (* 2) spc for src module *)
  Context (spc_s : string → option fspec).
  Context (InputInSpc : spc_incl InputAS.spc spc_s).
  
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Definition CellioI := (CellioI.t).
  Local Definition CellioA := (CellioA.t u_s spc_s).

  Lemma simF_set : HSim.sim_fun open CellioA CellioI Ist CellioName.set.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "->".
    wforce_l tt. wforces_l. iSplit; first eauto.

    wcall "IST"; eauto.
    wsteps_l. iDestruct "ASM" as "->".

    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    wforces_l. iSplitL "C"; eauto.

    wsteps_r. hss. wsteps_r. wsteps_l. wforces_l.
    iSplit; eauto.

    wstep.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma simF_get : HSim.sim_fun open CellioA CellioI Ist CellioName.get.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "->".
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.

    wsteps_r. hss. wsteps_r.
    wforces_l. iSplitL "ASM'"; eauto.
    
    wsteps_l. wforces_l. iSplit; eauto.

    wstep. iSplit; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma sim : HSim.t open CellioA CellioI CellioA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
  
  Theorem correct : 
    ctx_refines
      (CellioA, CellioA.InitCond)
      (CellioI, emp%I).
  Proof.
    eapply main_adequacy, sim.
  Qed.
End CellioIA. End CellioIA.

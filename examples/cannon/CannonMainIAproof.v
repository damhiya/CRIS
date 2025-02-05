Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.
Require Import CannonMainI CannonMainA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CannonMainIA. Section CannonMainIA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ _ _, (True)%I.

  Variable ginv : invspec.
  Variable SpcMain : string → option fspec.
  Hypothesis CannonInSpcMain : spc_incl CannonAS.Spc SpcMain.
  
  Local Notation MainAMod := (MainA.t 1 ginv SpcMain).
  Local Notation MainIMod := (MainI.t 1).
  
  Lemma simF_main : HSim.sim_fun MainAMod MainIMod Ist false MainName.main.
  Proof.
    init_simF.
    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.
    steps_r. 
    unfold HoareCall. force_l. instantiate (1:=()). force_l.
    force_l. iSplitL "B"; et.
    call "IST"; et. steps_l. iDestruct "ASM" as "[% %]"; des; subst. hss.
    steps_r. hss. steps_r. step. steps_l. steps_r. force_l. force_l. iSplitR; et.
    step. iFrame; et.
  Qed.

  Theorem sim : HSim.t MainAMod MainIMod MainA.init_cond Ist false.
  Proof.
    (* init_sim. *)
    econs;[i; s; repeat unfold_hmod; s|eauto|try prove_sub_perm|try prove_sub_perm|unfold_hmod; s; i; des; subst; ss].
    - iIntros "IC". et.
    - apply simF_main.
  Qed.

  Theorem correct :
    ctx_refines
      (MainAMod, (MainA.init_cond))
      (MainIMod, (emp%I)).
  Proof.
    eapply main_adequacy.
    apply sim; et.
  Qed.
End CannonMainIA. End CannonMainIA.

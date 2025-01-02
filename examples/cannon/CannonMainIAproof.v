Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA CannonASpec.
Require Import CannonMainI CannonMainA CannonMainASpec.

(* Require Import MainAdequacy CtxRefine. *)

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CannonMainIA.
Section SIMMODSEM.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).
  
  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ _ _ _ => (True)%I.

  Variable ginv: Sk.t -> invspec.
  Variable StbMain: Sk.t -> gname -> option fspec.
  Hypothesis CannonInStbMain: forall sk, stb_incl CannonAS.Stb (StbMain sk).
  
  Local Notation MainAMod := (MainA.t 1 ginv StbMain).
  Local Notation MainIMod := (MainI.t 1).
  
  (*************)

  Lemma simF_main:
    HSim.sim_fun MainAMod MainIMod Ist MainName.main.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.
    steps_r. unfold ccallU. steps_l.
    unfold HoareCall. force_l. instantiate (1:=()). force_l.
    force_l. iSplitL "B"; et.
    call "IST"; et. iModIntro. steps_l. iDestruct "ASM" as "[% %]"; des; subst. hss.
    steps_r. hss. steps_r. step. steps_l. steps_r. force_l. force_l. iSplitR; et.
    step. iFrame; et.
  Qed.

  Theorem sim:
    HSim.t MainAMod MainIMod MainA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "IC". et.
    - apply simF_main.
  Qed.

End SIMMODSEM.

Section PROOF.

  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.

  Theorem correct gi StbMain
    (CannonInStbMain: forall sk, stb_incl CannonAS.Stb (StbMain sk))
    :
    ctx_refines
      ((MainA.t 1 gi StbMain), (MainA.InitCond))
      ((MainI.t 1), const(emp%I)).
  Proof.
    eapply main_adequacy.
    apply sim; et.
  Qed.

End PROOF.
End CannonMainIA.

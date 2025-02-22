Require Import CRIS.

Require Import MutFA MutGA.
Require Import MutHeader MutMainHeader MutMainI MutMainA.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  (* Import MutAUX. *)
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, (True)%I.

  Variable Spc: string -> option fspec.
  Hypothesis FInSpc: spc_incl MutFA.SpcF Spc.

  Local Notation MutMainAMod := ((MutMainA.t Spc) ★ (MutFA.t Spc)).
  Local Notation MutMainIMod := ((MutMainI.t) ★ (MutFA.t Spc)).
  Local Notation IstFull := (IstProd (IstSB (MutMainA.t Spc).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    HSim.sim_fun open MutMainAMod MutMainIMod IstFull MutMainName.main.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". des; subst; hss.

    steps_r. inline_r. steps_r.
    force_r 10. force_r ([Vint 10]↑). force_r. iSplitR.
    { iSplit; iPureIntro; et. esplits; et. unfold MutAUX.mut_max. nia. }
    steps_r. iDestruct "GRT" as "%"; des; subst; hss.
    steps_r. force_l. steps_l. forces_l. iSplit; et. steps_l.
    step. iFrame; et.
  Qed.

  Theorem sim:
    HSim.t open MutMainAMod MutMainIMod MutMainA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "IC". iExists [], [], [], []. iSplitR; et.
      iSplit; et. iSplit; et. iPureIntro. esplits; ss.
    - apply simF_main; eauto.
  Qed.

  Theorem correct:
    ctx_refines
    (MutMainAMod, emp%I)
    (MutMainIMod, emp%I).
  Proof.
    eapply main_adequacy.
    eapply sim.
  Qed.

End MutMainIA. End MutMainIA.

Require Import CRIS.

Require Import NormITree.
Require Import APCHeader APC APCI APCA.

Set Implicit Arguments.

Module APCIA. Section APCIA.
  Import APCA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  
  Context (SpA : string → option fspec).
  Context (SpPure : string → option fspec).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ _ _, True)%I.

  Local Definition APCAMod := (APCA.t SpPure SpA).
  Local Definition APCIMod := (APCI.t).

  Local Transparent _APC.

  Lemma simF_apc :
    HSim.sim_fun open APCAMod APCIMod Ist APCHdr.apc.
  Proof using _sinvG.
    init_simF 0 0.
    
    steps_l. iDestruct "ASM" as "[-> ->]"; hss.
    steps_r. steps_l. rewrite /APC. force_l. steps_l.
    rewrite unfold_APC. force_l true. steps_l.
    forces_l. iSplitR; first done. step. iFrame; eauto.
    Unshelve. all: ss.
  Qed.

  Theorem sim : HSim.t open APCAMod APCIMod emp%I Ist.
  Proof using _sinvG.
    init_sim.
    - eauto.
    - eapply simF_apc.
  Qed.
End APCIA.

Section ctxr.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Theorem ctxr (SpA SpPure: string → option fspec):
    ctx_refines
      (APCA.t SpPure SpA, emp%I)
      (APCI.t, emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End ctxr. End APCIA.

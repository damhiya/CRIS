Require Import CRIS.
Require Import APCHeader APC APCI APCA.

Set Implicit Arguments.

Module APCIA. Section APCIA.
  Import APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  
  Context (SpA : sp_type).
  Context (SpPure : spl_type).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ _ _, True)%I.

  Local Definition APCAMod := (APCA.t SpPure SpA).
  Local Definition APCIMod := (APCI.t).

  Local Transparent _APC.

  Lemma simF_apc :
    ISim.sim_fun open APCAMod APCIMod APCA.init_cond Ist (Some APCHdr.apc).
  Proof using _crisG.
    init_simF.
    
    steps_l. iDestruct "ASM" as "[-> ->]"; hss.
    steps_r. steps_l. rewrite /APC. force_l. steps_l.
    rewrite unfold_APC. force_l true. steps_l.
    forces_l. iSplitR; first done. step. iFrame; eauto.
    Unshelve. all: ss.
  Qed.

  Theorem sim : ISim.t open APCAMod APCIMod emp%I Ist.
  Proof using _crisG.
    init_sim.
    - eauto.
    - eapply simF_apc.
  Qed.
End APCIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Theorem ctxr (SpA : sp_type) (SpPure : spl_type) :
    ctx_refines
      (APCA.t SpPure SpA, emp%I)
      (APCI.t, emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End ctxr. End APCIA.

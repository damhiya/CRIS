Require Import CRIS.
Require Import APCHeader APC APCI APCA.

Set Implicit Arguments.

Module APCIA. Section APCIA.
  Import APCA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  
  Context (SpA SpPure: specmap).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.

  Local Definition APCAMod := (APCA.t SpPure SpA).
  Local Definition APCIMod := (APCI.t).

  Local Transparent _APC.

  Lemma simF_apc : ISim.sim_fun open APCAMod APCIMod Ist (fid APCHdr.apc).
  Proof using.
    cStartFunSim. rewrite /apc_body.
    
    cStepsS. iDestruct "ASM" as "[-> ->]"; cSimpl.
    cStepsT. cStepsS. rewrite /APC. cForceS. cStepsS.
    rewrite unfold_APC. cForceS true. cStepsS.
    cForcesS. iSplitR; first done. cStep. iFrame; eauto.
    Unshelve. all: ss.
  Qed.

  Lemma sim : ISim.t open APCAMod APCIMod emp%I Ist.
  Proof using.
    cStartModSim; eauto.
    - eapply simF_apc.
  Qed.
End APCIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (SpA SpPure : specmap) :
    ctx_refines
      (APCA.t SpPure SpA, emp%I)
      (APCI.t, emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End ctxr. End APCIA.

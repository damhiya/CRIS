Require Import CRIS.

Require Import NormITree.
Require Import APCHeader APC APCI APCA.

Set Implicit Arguments.

Module APCIA. Section APCIA.
  Import APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  
  Context (u: univ_id).
  Context (SpcA : string → option fspec).
  Context (SpcPure : string → option fspec).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ _ _, True)%I.

  Local Definition APCAMod := (APCA.t u SpcPure SpcA).
  Local Definition APCIMod := (APCI.t).

  Local Transparent _APC.

  Lemma simF_apc :
    HSim.sim_fun open APCAMod APCIMod Ist APCName.apc.
  Proof.
    winit_simF u 0.
    
    wsteps_l. iDestruct "ASM" as "[-> ->]"; hss.
    wsteps_r. wsteps_l. rewrite /APC. wforce_l. wsteps_l.
    rewrite unfold_APC. wforce_l true. wsteps_l.
    wforces_l. iSplitR; first done. wstep. iFrame; eauto.
    Unshelve. all: ss.
  Qed.

  Theorem sim : HSim.t open APCAMod APCIMod emp%I Ist.
  Proof.
    init_sim.
    - eauto.
    - eapply simF_apc.
  Qed.
End APCIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem ctxr (u: univ_id) (SpcA SpcPure: string → option fspec):
    ctx_refines
      (APCA.t u SpcPure SpcA, emp%I)
      (APCI.t, emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End ctxr. End APCIA.

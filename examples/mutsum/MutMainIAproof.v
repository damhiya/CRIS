Require Import CRIS.

Require Import MutFA MutGA.
Require Import MutHeader MutMainHeader MutMainI MutMainA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Context (u_s u_apc: univ_id).
  Context (Spc SpcPure: string -> option fspec).
  Context (APCInSpc : spc_incl (APCA.Spc) Spc).
  Context (FInPure : spc_incl (MutFA.SpcF) SpcPure).
  Context (PureInSpc : spc_sub SpcPure Spc).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, (True)%I.

  Local Definition MutMainAMod := ((MutMainA.t u_s Spc) ★ APCA.t u_apc SpcPure Spc).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t u_apc SpcPure Spc).
  Local Definition IstFull := (IstProd (IstSB (MutMainA.t u_s Spc).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    HSim.sim_fun open MutMainAMod MutMainIMod IstFull MutMainName.main.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "%". des; subst; hss.
    rewrite /pure.
    wsteps_r. wforce_l 11. wsteps_l. wforces_l. iSplitR; eauto.
    wsteps_l. winline_l. wsteps_l. iDestruct "ASM" as "[-> <-]"; hss.
    wsteps_l. rewrite /APC. wforce_l 1. wsteps_l. rewrite unfold_APC.
    wforce_l false. wsteps_l. wforce_l 0. wsteps_l.
    assert (LT: (0 < 1)%ord). { eapply OrdArith.lt_from_nat. nia. }
    wforce_l LT. wsteps_l. wforce_l MutName.mutf. wsteps_l. wforce_l 10.
    wsteps_l. 
    assert (F: SpcPure MutName.mutf = Some MutFA.f_spec).
    { eapply FInPure. rewrite /MutFA.SpcF. unseal CRIS. ss. }
    assert (PO: is_Some (SpcPure MutName.mutf) ∧ (10 < 11)%ord).
    { split; eauto. eapply OrdArith.lt_from_nat; nia. }
    rewrite /guarantee. wforce_l PO. wsteps_l. wforces_l. iSplit; eauto.
    wsteps_l. wforce_l 10. wsteps_l. wforces_l. iSplitR.
    { iPureIntro. esplits; eauto. { unfold mut_max. nia. } { refl. } }
    wcall "IST". wsteps_l. iDestruct "ASM" as "->". wsteps_r.
    rewrite unfold_APC. wforce_l true. wsteps_l. wforces_l. iSplitR; first done.
    wsteps_l. hss. wsteps_r. wforces_l. wsteps_l. wforces_l. iSplitR; eauto.
    wstep. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  Qed.

  Theorem sim:
    HSim.t open MutMainAMod MutMainIMod MutMainA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "IC". iExists [], [], [], []. iSplitR; et.
      iSplit; et. iSplit; et. iPureIntro. esplits; ss.
    - apply simF_main; eauto.
  Qed.
End MutMainIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem ctxr (u_s u_apc: univ_id) (Spc SpcPure: string → option fspec)
    (APCInSpc : spc_incl (APCA.Spc) Spc)
    (FInPure : spc_incl (MutFA.SpcF) SpcPure)
    (PureInSpc : spc_sub SpcPure Spc)
  :
    ctx_refines
      (MutMainA.t u_s Spc ★ APCA.t u_apc SpcPure Spc, emp%I)
      (MutMainI.t ★ APCA.t u_apc SpcPure Spc, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutMainIA.

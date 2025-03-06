Require Import CRIS.

Require Import NormITree.
Require Import MutHeader MutFI MutFA MutGA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module MutFIA. Section MutFIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Context (u_s u_apc: univ_id).
  Context (Spc: string -> option fspec).
  Context (SpcPure: string -> option fspec).

  Context (APCInSpc : spc_incl (APCA.Spc) Spc).
  Context (GInPure : spc_incl (MutGA.SpcG) SpcPure).
  Context (PureInSpc : spc_sub SpcPure Spc).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutFAMod := (MutFA.t u_s Spc ★ APCA.t u_apc SpcPure Spc).
  Local Definition MutFIMod := (MutFI.t ★ APCA.t u_apc SpcPure Spc).
  Local Definition IstFull := (IstProd (IstSB (MutFA.t u_s Spc).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutf:
    HSim.sim_fun open MutFAMod MutFIMod IstFull MutName.mutf.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.
    wsteps_r. unfold assume. wforce_r. wsteps_r.
    
    destruct q; s.
    { (* f(0) *)
      wsteps_r. wforce_l. wsteps_l.
      wforces_l. iSplitR; et. wsteps_l. 
      winline_l. wsteps_l. iDestruct "ASM" as "[-> <-]"; hss. wsteps_l.
      rewrite /APC. wforce_l q. wsteps_l. rewrite unfold_APC.
      wforce_l true. wsteps_l. wforces_l. iSplitR; eauto.
      wsteps_l. wforces_l. iSplitR; eauto.
      wstep. iSplitR "IST"; iFrame; auto.
    }

    replace (S q - 1)%Z with (Z.of_nat q) by nia.
    wsteps_l. wforce_l vo. wsteps_l. wforces_l. iSplitR; eauto.
    winline_l. wsteps_l. iDestruct "ASM" as "[-> <-]"; hss. wsteps_l.
    rewrite /APC. wforce_l 1. wsteps_l. rewrite unfold_APC.
    wforce_l false. wsteps_l. wforce_l 0. wsteps_l.
    assert (LT: (0 < 1)%ord).
    { eapply OrdArith.lt_from_nat. nia. }
    wforce_l LT. wsteps_l. wforce_l MutName.mutg. wsteps_l. wforce_l q. wsteps_l.
    assert (is_Some (SpcPure MutName.mutg) ∧ (q < vo)%ord).
    { split. 
      { rewrite /is_Some. unfold MutGA.SpcG in GInPure.
        revert GInPure. unseal CRIS. i. unfold spc_incl in GInPure.
        destruct GInPure. rewrite /spc_sub /to_spc in H0.
        hexploit (H0 MutName.mutg MutGA.g_spec); [refl|]. i. eauto.
      }
      { eapply Ord.lt_le_lt; eauto. eapply OrdArith.lt_from_nat. nia. }
    }
    unfold guarantee. wforce_l H. wsteps_l. wforce_l. iSplitR.
    { iPureIntro. eapply PureInSpc. eapply GInPure. rewrite /MutGA.SpcG. unseal CRIS. ss. }
    wsteps_l. wforce_l q. wsteps_l. wforces_l. iSplitR; eauto.
    { iPureIntro. esplits; eauto.
      { nia. } { refl. }
    }
    wcall "IST". wsteps_l. iDestruct "ASM" as "->"; hss. wsteps_r. hss. wsteps_r.
    rewrite unfold_APC. wforce_l true. wsteps_l. wforces_l. iSplitR; first done.
    wsteps_l. wforces_l; iSplitR; eauto; iClear "ASM".
    wstep. iFrame. iPureIntro. do 2 f_equal. nia.
    Unshelve. all: ss.
    { eapply mut_max_intrange; eauto. }
    { exact (0↑). }
  Qed.

  Theorem sim:
    HSim.t open MutFAMod MutFIMod MutFA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "C". iExists [], [], [], []. do 2 iSplit; eauto. iFrame. iPureIntro.
      rewrite /MutFA.scopes /state_scopes /incl //.
    - eapply simF_mutf.
  Qed.
End MutFIA.

Section wctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem wctxr (u_s u_apc: univ_id) (Spc SpcPure: string → option fspec) 
    (APCInSpc : spc_incl (APCA.Spc) Spc)
    (GInPure : spc_incl (MutGA.SpcG) SpcPure)
    (PureInSpc : spc_sub SpcPure Spc)
  :
    ctx_refines
      (MutFA.t u_s Spc ★ APCA.t u_apc SpcPure Spc, MutFA.InitCond)
      (MutFI.t ★ APCA.t u_apc SpcPure Spc, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End wctxr. End MutFIA.

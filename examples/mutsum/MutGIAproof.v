Require Import CRIS.

Require Import NormITree.
Require Import MutHeader MutGI MutGA MutFA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module MutGIA. Section MutGIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Context (u_s u_apc: univ_id).
  Context (Spc: string -> option fspec).
  Context (SpcPure: string -> option fspec).

  Context (APCInSpc : spc_incl (APCA.Spc) Spc).
  Context (FInPure : spc_incl (MutFA.SpcF) SpcPure).
  Context (PureInSpc : spc_sub SpcPure Spc).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutGAMod := (MutGA.t u_s Spc ★ APCA.t u_apc SpcPure Spc).
  Local Definition MutGIMod := (MutGI.t ★ APCA.t u_apc SpcPure Spc).
  Local Definition IstFull := (IstProd (IstSB (MutGA.t u_s Spc).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutg:
    HSim.sim_fun open MutGAMod MutGIMod IstFull MutName.mutg.
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
    wforce_l LT. wsteps_l. wforce_l MutName.mutf. wsteps_l. wforce_l q. wsteps_l.
    assert (is_Some (SpcPure MutName.mutf) ∧ (q < vo)%ord).
    { split. 
      { rewrite /is_Some. unfold MutFA.SpcF in FInPure.
        revert FInPure. unseal CRIS. i. unfold spc_incl in FInPure.
        destruct FInPure. rewrite /spc_sub /to_spc in H0.
        hexploit (H0 MutName.mutf MutFA.f_spec); [refl|]. i. eauto.
      }
      { eapply Ord.lt_le_lt; eauto. eapply OrdArith.lt_from_nat. nia. }
    }
    unfold guarantee. wforce_l H. wsteps_l. wforce_l. iSplitR.
    { iPureIntro. eapply PureInSpc. eapply FInPure. rewrite /MutFA.SpcF. unseal CRIS. ss. }
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
    HSim.t open MutGAMod MutGIMod MutGA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "C". iExists [], [], [], []. do 2 iSplit; eauto. iFrame. iPureIntro.
      rewrite /MutGA.scopes /state_scopes /incl //.
    - eapply simF_mutg.
  Qed.
End MutGIA.

Section wctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem wctxr (u_s u_apc: univ_id) (Spc SpcPure: string → option fspec) 
    (APCInSpc : spc_incl (APCA.Spc) Spc)
    (FInPure : spc_incl (MutFA.SpcF) SpcPure)
    (PureInSpc : spc_sub SpcPure Spc)
  :
    ctx_refines
      (MutGA.t u_s Spc ★ APCA.t u_apc SpcPure Spc, MutGA.InitCond)
      (MutGI.t ★ APCA.t u_apc SpcPure Spc, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End wctxr. End MutGIA.

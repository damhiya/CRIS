Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockHeader SpinLockI SpinLockA SchA MemA wsim_tactics SchTactics.
Require Import SchHeader.

Module SpinLockIA. Section SpinLockIA.
  Import SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (spc_s spc_user_s spc_mem : string → option fspec). (* spcs of lock/sch/mem *)
  Context (SchInSpc : spc_incl (SchAS.spc u_a spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.spc spc_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t u_a spc_mem).
  Local Definition SpinLockA := (SpinLockA.t u_a spc_s).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (SpinLockA ★ MemA).
  Local Definition MI := (SpinLockI ★ MemA).

  Lemma newlock_simF : HSim.sim_fun open MA MI IstFull SpinLockName.newlock.
  Proof.
    winit_simF u_a 0.
    wsteps_l. rename q1 into tid. destruct q2 as [n P]; s. iDestruct "ASM" as "[[TID P] ->]". hss.
    wsteps_r. sch_yield_r. iFrame. clear nths; iIntros (nths st_s st_t) "IST TID".
    winline_r. wforce_r 1. wforces_r. iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[%blk [-> [PT _]]] ->]". hss. wsteps_r.
    sch_yield_r. iFrame. clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    winline_r. wforce_r (blk, 0%Z, Vint 0). wsteps_r. wforces_r. iSplitL "PT"; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iFrame. clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wforce_l (Vptr blk 0). wsteps_l. wforce_l. wsteps_l.

    (* alloc invariant *)
    iApply (wsim_own_alloc (Excl ())); ss. iIntros "[%γ TKN]".
    iMod (inv_alloc (SpinLockAS.lock_inv blk 0 P γ) u_a _ _ N_SpinLockA with "[P PT TKN]") as "#I"; eauto.
    { rewrite /lock_inv /=; SL_red; iRight; iFrame. }
    wforces_l. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    wsteps_l. wstep. eauto.
  (*FAST*)Admitted.

  Lemma acquire_simF : HSim.sim_fun open MA MI IstFull SpinLockName.acquire.
  Proof.
    winit_simF u_a 0.
    wsteps_l. iDestruct "ASM" as "[[% [TID #LOCK]] %]". hss.
    iDestruct "LOCK" as (? ?) "[% LOCK]".
    wsteps_r. iApply wsim_reset.
    iStopProof.
    clear NODD NODS.
    (* revert NODUPFS. combine_quant NODUPFT. *)
    (* combine_quant nths. *)
    revert nths.
    (* combine_quant NODD. combine_quant NODS. *)
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind. ii.
    destruct a as [st_tgt [st_src nths]]. ss.
    iIntros "[#LOCK [IST TID]] _ #CIH".
    unfold_iter_l. wsteps_l.
    unfold_iter_r. wsteps_r.
    sch_yield_r. iFrame. clear nths; iIntros (nths st_s st_t) "IST TID".
    iInv "LOCK" as "I" "Hcl".
    SL_red.
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      winline_r. wforces_r. 
      instantiate (1:= existT _ _). hss. instantiate (2:= 1). ss.
      instantiate (1:= (_, _, _, _, _)). hss. 
      iSplitL "FAIL". iFrame. et. 
      wsteps_r.
      iDestruct "GRT" as "[[POINTS_TO %] %]".
      hss. wsteps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". iFrame.
      sch_yield_r. iFrame. clear nths; iIntros (nths0 st_s0 st_t0) "IST TID".
      wsteps_r.
      sch_yield_r. iFrame. clear nths0; iIntros (nths st_s1 st_t1) "IST TID".
      wsteps_r.
      sch_yield_l. wforce_l false. wsteps_l.
      wby_coind "CIH".
      iFrame. done.
    }
    { (* success case *)
      iDestruct "SUCC" as "[POINTS_TO [Q TKN]]".
      winline_r. wforces_r.
      instantiate (1:= existT _ _). ss. instantiate (2:= 0). ss.  
      instantiate (1:= (_, _, _, _)). hss. iSplitL "POINTS_TO"; iFrame; et. 
      wsteps_r.
      iDestruct "GRT" as "[[POINTS_TO ->] ->]". hss.
      wsteps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". iFrame.
      sch_yield_r. iFrame. clear nths; iIntros (nths0 st_s0 st_t0) "IST TID".
      wsteps_r.
      sch_yield_r. iFrame. clear nths0; iIntros (nths st_s1 st_t1) "IST TID".
      wsteps_r.
      sch_yield_r. iFrame. clear nths; iIntros (nths0 st_s2 st_t2) "IST TID".
      sch_yield_l. wforce_l true. wsteps_l. wforces_l. iSplitL "Q TKN TID"; SL_red; et. iFrame. et.
      wstep.
      et.
    }
  (*FAST*)Admitted.

  Lemma release_simF : HSim.sim_fun open MA MI IstFull SpinLockName.release.
    winit_simF u_a 0.
    wsteps_l.
    iDestruct "ASM" as "[(% & TID & #LOCK & TKN & Q) %]".
    iDestruct "LOCK" as (? ?) "[% LOCK]".
    hss.
    wsteps_r.
    sch_yield_r. iFrame. clear nths; iIntros (nths0 st_s st_t) "IST TID".
    iInv "LOCK" as "I" "Hcl".
    SL_red.
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { winline_r. wsteps_r. wforces_r. instantiate (1:= (_, _)).
      ss. instantiate (2:=(_, _)). ss.
      iSplitL "LOCKED"; iFrame; et.
      wsteps_r. iDestruct "GRT" as "[[POINTS_TO %] %]". hss.
      wsteps_r.
      iMod ("Hcl" with "[POINTS_TO Q TKN]") as "_". iRight. iFrame.
      sch_yield_r. iFrame. clear nths0; iIntros (nths st_s0 st_t0) "IST TID".
      sch_yield_l. wsteps_l. wforces_l. iFrame. iSplit; et. wstep. iFrame; et.
    }
    { iDestruct "UNLOCKED" as "[POINTS_TO [Q' TKN']]".
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*FAST*)Admitted.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; iSplit; eauto. }
    { apply newlock_simF. }
    { apply acquire_simF. }
    { apply release_simF. }
  Qed.
End SpinLockIA.
Section SpinLockIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockAGΓ Γ}.
  Lemma wctxr (u : univ_id) (spc_s spc_user_s spc_mem : string → option fspec)
      (SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s)
      (MemInSpc : spc_incl MemA.spc spc_s) :
    ctx_refines
      (SpinLockA.t u spc_s ★ MemA.t u spc_mem, emp%I)
      (SpinLockI.t         ★ MemA.t u spc_mem, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End SpinLockIA. End SpinLockIA.
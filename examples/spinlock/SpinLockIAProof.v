Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockHeader SpinLockI SpinLockA SchA MemA wsim_tactics SchTactics.
Require Import SchHeader.

Module SpinLockIA. Section SpinLockIA.
  Import SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (spc_s spc_user_s spc_mem : string → option fspec). (* spcs of lock/sch/mem *)
  Context (SchInSpc : spc_incl (SchAS.spc u_a spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.Spc spc_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Notation MemA := (MemA.t u_a spc_mem).
  Local Notation SpinLockA := (SpinLockA.t u_a spc_s).
  Local Notation SpinLockI := (SpinLockI.t).
  Local Notation IstFull := (IstProd (IstSB SpinLockA.(HMod.scopes) Ist) IstEq).
  Local Notation MA := (SpinLockA ★ MemA).
  Local Notation MI := (SpinLockI ★ MemA).

  Lemma newlock_simF : HSim.sim_fun open MA MI IstFull SpinLockName.newlock.
  Proof.
    winit_simF u_a 0.
    wsteps_l. destruct q as [n P]; s. iDestruct "ASM" as "[P ->]". hss.
    wsteps_r. sch_yield_r. iSplitL "IST"; iFrame. clear nths; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r 1. wforces_r. iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[%blk [-> [PT _]]] ->]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; iFrame. clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (blk, 0%Z, Vint 0). wsteps_r. wforces_r. iSplitL "PT"; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; iFrame. clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    sch_yield_l. wforce_l (Vptr blk 0). wsteps_l. wforce_l. wsteps_l.

    (* alloc invariant *)
    iApply (wsim_own_alloc (Excl ())); ss. iIntros "[%γ TKN]".
    iMod (inv_alloc (SpinLockAS.lock_inv blk 0 P γ) u_a _ _ N_SpinLockA with "[P PT TKN]") as "#I"; eauto.
    { rewrite /lock_inv /=; SL_red; iRight; iFrame. }
    wforces_l. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    wsteps_l. wstep. eauto.
  Qed.

  Lemma acquire_simF : HSim.sim_fun open MA MI IstFull SpinLockName.acquire.
  Proof.
    winit_simF u_a 0.
    wsteps_l. iDestruct "ASM" as "[[% LOCK] %]". hss.
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
    iIntros "[IST #LOCK] _ #CIH".
    unfold_iter_l. wsteps_l.
    unfold_iter_r. wsteps_r.
    sch_yield_r. iSplitL "IST"; iFrame. clear nths; iIntros (nths st_s st_t) "IST".
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
      sch_yield_r. iSplitL "IST"; iFrame. clear nths; iIntros (nths0 st_s0 st_t0) "IST".
      wsteps_r.
      sch_yield_r. iSplitL "IST"; iFrame. clear nths0; iIntros (nths st_s1 st_t1) "IST".
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
      sch_yield_r. iSplitL "IST"; iFrame. clear nths; iIntros (nths0 st_s0 st_t0) "IST".
      wsteps_r.
      sch_yield_r. iSplitL "IST"; iFrame. clear nths0; iIntros (nths st_s1 st_t1) "IST".
      wsteps_r.
      sch_yield_r. iSplitL "IST"; iFrame. clear nths; iIntros (nths0 st_s2 st_t2) "IST".
      sch_yield_l. wforce_l true. wsteps_l. wforces_l. iSplitL "Q TKN"; SL_red; et. iFrame. et.
      wstep.
      et.
    }
  Qed.

  Lemma release_simF : HSim.sim_fun open MA MI IstFull SpinLockName.release.
    winit_simF u_a 0.
    wsteps_l.
    iDestruct "ASM" as "[(% & #LOCK & TKN & Q) %]".
    iDestruct "LOCK" as (? ?) "[% LOCK]".
    hss.
    wsteps_r.
    sch_yield_r.  iSplitL "IST"; iFrame. clear nths; iIntros (nths0 st_s st_t) "IST".
    iInv "LOCK" as "I" "Hcl".
    SL_red.
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { winline_r. wsteps_r. wforces_r. instantiate (1:= (_, _)).
      ss. instantiate (2:=(_, _)). ss.
      iSplitL "LOCKED"; iFrame; et.
      wsteps_r. iDestruct "GRT" as "[[POINTS_TO %] %]". hss.
      wsteps_r.
      iMod ("Hcl" with "[POINTS_TO Q TKN]") as "_". iRight. iFrame. 
      sch_yield_r. iSplitL "IST"; iFrame. clear nths0; iIntros (nths st_s0 st_t0) "IST".
      sch_yield_l. wsteps_l. wforces_l. iSplitR; et. wstep. iFrame; et.
    }
    { iDestruct "UNLOCKED" as "[POINTS_TO [Q' TKN']]".
      iCombine "TKN TKN'" gives %Hv. done.
    }
  Qed.
End SpinLockIA. End SpinLockIA.

Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockHeader SpinLockI SpinLockA SchA MemA wsim_tactics SchTactics.

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
    winit_simF u_a 0.
    wsteps_l. 
    iDestruct "ASM" as "[[% LOCK] %]". hss.
    wsteps_r.
    
  Admitted.

  Lemma release_simF : HSim.sim_fun open MA MI IstFull SpinLockName.release.
  Admitted.
End SpinLockIA. End SpinLockIA.

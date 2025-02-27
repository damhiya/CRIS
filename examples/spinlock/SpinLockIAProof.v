Require Import CRIS.

Require Import SpinLockA SpinLockI SpinLockHeader.
Require Import SchA SchHeader SchGInv SchTactics.
Require Import MemA MemHeader.
Require Import wsim_tactics SchTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module SpinLockIA.
Section SIMMODSEM.

  Context `{!invG α Σ Γ, !subG (Γ: HRA) Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !SchAGΣ Σ, !lockGΓ Γ}.
  Context `{!CtxST.t τ, !SL.G Σ Γ α β τ, !syn_invG Σ Γ α β τ}.
  Notation iProp := (iProp Σ). 

  Context (u_s: univ_id).
  Context (spc_s spc_user_s spc_mem: string → option fspec).

  Context (SchInSpc : spc_incl (SchAS.spc u_s spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.Spc spc_s).
  Context (SpinInSpc : spc_incl (SpinLockAS.Spc u_s) spc_user_s).
  (*
  Hypothesis SchInStbSpin:
    forall sk, stb_incl (SchAS.Stb univ sk StbMem_) (StbSpin sk).
  Hypothesis SchInStbSch: forall sk, stb_incl (SchAS.Stb univ sk StbMem_) (StbSch sk).
  Hypothesis StbSpinInStbMem_:
    forall sk, stb_incl (SpinLockAS.Stb univ) (StbMem_ sk).
  Hypothesis StbSpinInStbSpin:
    forall sk, stb_incl (SpinLockAS.Stb univ) (StbSpin sk). 
  Hypothesis SchInStbMem: forall sk, stb_sub (StbSch sk) (StbMem sk).
  Hypothesis SchInStbMem': forall sk, stb_sub (StbSch sk) (StbMem' sk). *)

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp :=
    (λ _ _ _, emp)%I.

  Local Notation MemA := (MemA.t u_s spc_mem).
  Local Notation SpinLockA := (SpinLockA.t u_s spc_s).
  Local Notation SpinLockAMod := (SpinLockA ★ MemA).
  Local Notation SpinLockIMod := (SpinLockI.t ★ MemA).


  Lemma simF_new_lock: 
    HSim.sim_fun open SpinLockAMod SpinLockIMod Ist SpinLockName.new_lock.
  Proof.
    winit_simF u_s 0.
    wsteps_l. hss.
    destruct q2.
    iDestruct "ASM" as "((% & Q) & %)".
    des; subst; hss.
    wsteps_r.
    wsteps_l.
    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".

    winline_r.
    wsteps_r. wforces_r. iSplitR; iFrame. iSplitR; eauto. iPureIntro.  instantiate (2:= 1). split; hss.

    wsteps_r.
  
    iDestruct "GRT" as "(GRT & %)".
    iDestruct "GRT" as (?) "(% & POINTS_TO & %)".
    rewrite right_id.
    iSplitR; hss.
    forces_l. 
    steps_l.   
    steps_r.
    yield_r "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }
    inline_r.
    steps_r. forces_r. instantiate (1:= (_, _, _)). hss. iSplitL "POINTS_TO". iFrame. et.
    steps_r. 
    iDestruct "GRT" as "(GRT & %)".
    iDestruct "GRT" as "(POINTS_TO & %)".
    forces_r. iSplitR; hss.
    yield_l "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }
    forces_l. steps_l. 
    steps_r.
    yield_r "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }
    yield_l "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }
    steps_l. forces_l. iSplitL; iFrame. unfold SpinLockAS.is_lock. iSplit. iExists b. iSplit. hss.
    iExists _. iExists (b, 0%Z). hss. iSplit; ss.
    admit. ss. steps_r. step. iPureIntro.
    split; ss.
    Unshelve. ss. 
    
    Admitted. 

  Lemma simF_acquire: 
    HSim.sim_fun open SpinLockAMod SpinLockIMod IstEq SpinLockName.acquire.
  Proof.
    init_simF.
    steps_l.
    destruct q2.

    rename q7 into loc.
    rename q8 into ofs.
    iDestruct "ASM" as "(W & (% & #IS_LOCK) & %)".
    unfold SpinLockAS.is_lock.
    iDestruct "IS_LOCK" as (?) "[% INV]".
    destruct l; ss.
    forces_r.
    
    iSplitR; hss.
    steps_l.
    forces_r.
    steps_r.
    yield_r "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }  
    iApply isim_reset. 

    Admitted.

  Lemma simf_release:
    HSim.sim_fun open SpinLockAMod SpinLockIMod IstEq SpinLockName.release.
  Proof.
    init_simF.
    steps_l.
    destruct q2.
    iDestruct "ASM" as "(W & ((% & (#IS_LOCK & LOCK & T)) & %))".
    forces_l. iSplitR; hss.
    steps_l. 
    steps_r.
    yield_r "IST W".
    { apply SchInStbSpin. unfold SchAS.spc. unseal CRIS. ss.  }
    { iFrame. }  
    inline_r.
    steps_r.
    forces_r.
    instantiate (1:= (_, _, _)).
    hss.
    unfold SpinLockAS.is_lock. 

    Admitted.
  

End SIMMODSEM.
End SpinLockIA.
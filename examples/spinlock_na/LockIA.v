Require Import CRIS.
Require Import ImpPrelude MemA MemTactics.
Require Import LockHeader LockI LockA.
Require Import SchHeader SchA SchTactics.

Module LockIA. Section LockIA.
  Import LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG}.

  Context (E : coPset) (Hsub : ↑N_SpinLockA ⊆ E).
  Context (sp_user : spl_type).
  Context (sp : sp_type).
  Context (SchInSp : sp_incl (SchA.sp sp_user E) sp).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t sp_none.
  Local Definition SpinLockA := (SpinLockA.t E sp).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockA ★ MemA).
  Local Notation MI := (SpinLockI ★ MemA).

  Lemma newlock_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.newlock).
  Proof using SchInSp Hsub.
    init_simF.

    (* preprocess initial conditions *)
    steps_l. rename _q3 into stid, _q into vret. destruct _q2 as [n P]; s.
    iDestruct "ASM" as "[TID [P ->]]". hss.
    steps_r.

    (* tgt yield *)
    sch_yield_ir.

    (* tgt inline - mem alloc *)
    steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (blk) "[↦ _]". steps_r. hss_r. steps_r.

    (* tgt yield *)
    sch_yield_ir.

    (* tgt inline - mem store *)
    steps_r.
    iApply (wsim_mem_store with "↦"); [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "↦". steps_r. hss_r. steps_r.

    (* src/tgt yield *)
    sch_yield_ir. steps_r.
    sch_yield_l. force_l (Vptr (blk, 0%Z)). steps_l.

    (* prove source postcondition *)
    (* alloc invariant *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    iMod (inv_alloc (LockAS.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA with "[P ↦ TKN]")
      as "#I"; eauto.
    { rewrite /lock_inv /=; SL_red; iRight; iFrame. }
    forces_l. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    steps_l. step. eauto.
  (*SLOW*)Qed.

  Lemma acquire_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.acquire).
  Proof using SchInSp Hsub.
    init_simF.

    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[TID [[-> #LOCK] ->]]". hss.
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]. steps_r.

    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#LOCK [IST TID]] /=".
    destruct_quant CIH.

    unfold_iterC_r. steps_r.
    (* tgt yield *)
    sch_yield_ir.
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      (* tgt inline - mem cas *)
      steps_r.
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "FAIL");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; first done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      steps_r. hss_r. steps_r. hss_r. steps_r.
      
      (* tgt yields *)
      sch_yield_ir. steps_r.
      sch_yield_ir. steps_r.
      by_coind CIH. iFrame. done.
    }
    { (* success case *)
      (* tgt inline - mem cas *)
      steps_r.
      iDestruct "SUCC" as "[↦ [Q TKN]]".
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "↦");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; last done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      steps_r. hss_r. steps_r.

      (* tgt yields *)
      do 3 (sch_yield_ir).

      (* src yield *)
      sch_yield_l. forces_l. iSplitL "Q TKN TID"; SL_red; iFrame; et.
      (* both terminate *)
      step; eauto.
    }
  Unshelve. all: try exact 1%Qp. all: try exact Vundef.
  (*SLOW*)Qed.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof using SchInSp Hsub.
    init_simF.
    (* process src precondition *)
    steps_l.
    iDestruct "ASM" as "[TID [(% & #LOCK & TKN & Q) %]]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs].
    hss.
    steps_r.
    (* tgt yield *)
    sch_yield_ir.
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { (* locked case *)
      steps_r. inline_r. steps_r.
      force_r (_,_,_,_). forces_r.
      iSplitL "LOCKED"; iFrame; et.
      steps_r. iDestruct "GRT" as "[[PT %] %]"; subst.
      hss. steps_r.
      iMod ("Hcl" with "[PT Q TKN]") as "_".
      { iRight. iFrame. }
      (* tgt yield *)
      sch_yield_ir.
      (* src yield *)
      sch_yield_l. steps_l. forces_l. iFrame. iSplit; et. step. iFrame; et.
    }
    { (* unlocked case - ex falso quodlibet *)
      iDestruct "UNLOCKED" as "[PT [Q' TKN']]".
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*SLOW*)Qed.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { split; et. }
    { apply newlock_simF. }
    { apply acquire_simF. }
    { apply release_simF. }
  Qed.

  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr :
    ctx_refines
      (SpinLockA.t E sp ★ MemA.t sp_none, emp%I)
      (SpinLockI.t      ★ MemA.t sp_none, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.

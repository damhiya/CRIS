Require Import CRIS.
Require Import LockHeader MainI MainA LockI LockA.
Require Import ImpPrelude.
Require Import SchHeader SchA MemA SchTactics MemTactics.
From iris Require Import frac_auth numbers.

Ltac sch_yield_ii IST :=
  (norm_l with 
    (do 1 iApply (wsim_yield_tgt_ii);  [simpl_sp; ss|simpl_sp; ss|ss|ss|set_solver|set_solver| ];
      iFrame IST)); clear_st; iIntros (??) IST.

Module MainIA. Section MainIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG, !spinlockmainG}.
  Import LockA MainA.

  Context (N : namespace).
  Context (sp_s sp_t sp_user_s sp_user_t : specmap). (* sps of lock/sch/mem *)
  Context (SchInSp_s : (SchA.sp sp_user_s (↑N)) ⊆ sp_s).
  Context (SchInSp_t : (SchA.sp sp_user_t (↑N)) ⊆ sp_t).
  Context (MainInSp : (MainA.sp (↑N)) ⊆ sp_user_s).

  Local Definition MemA := MemA.t sp_s.
  Local Definition SpinLockA := (LockA.t (↑N) sp_t).
  Local Definition SpinLockMainA := (MainA.t N sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockMainA ★ (SpinLockA ★ MemA)).
  Local Notation MI := (SpinLockMainI ★ (SpinLockA ★ MemA)).

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (Some SpinLockMainHdr.incr).
  Proof using SchInSp_s SchInSp_t MainInSp.
    iStartSim.
    (* process src precondition *)
    steps_l. destruct _q as [[stid mtid] [[[blk_l ofs_l] [blk_v ofs_v]] γ_v]]. rename _q0 into varg.
    iDestruct "ASM" as "[TID [-> [-> [%γ_l [#Lock Tkn]]]]]".
    hss_l; hss_r. steps_l; steps_r. hss_l; hss_r. steps_l; steps_r.

    (* main code *)
    rewrite /incr /SpinLockMainI.incr. steps_l. steps_r.
    (* tgt yields *)
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    (* tgt inline - lock acquire *)
    steps_r. inline_r.
    force_r (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))).
    steps_r. forces_r.
    (* rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]". *)
    iFrame "TID Lock". iSplit; eauto. steps_r. hss_r. steps_r.
    (* TODO : make *)
    sch_yield_ii "IST".

    (* (* success case *) *)
    steps_r. iDestruct "GRT" as "[TID [<- [_ [TKN P]]]]". hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* tgt yield *)
    solve_base_sl_red. iDestruct "P" as "[%x [PT P]]".
    steps_r.
    iApply (wsim_mem_load with "PT"); ss. iIntros "PT".
    steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    iApply (wsim_mem_store with "PT"); ss. iIntros "PT".
    steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    iCombine "P Tkn" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    inline_r. steps_r.
    force_r (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))). forces_r.
    iSplitL "TID F PT TKN".
    { solve_base_sl_red. iFrame. iSplit; eauto. }
    steps_r. hss_r; steps_r.
    sch_yield_ii "IST". steps_r.
    
    (* tgt inline - lock acquire - restore lock protected proposition *)
    iDestruct "GRT" as "[TID [<- _]]". hss_r. steps_r.
    (* iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2. *)
    sch_yield_ir "IST" "TID".
    (* src yield *)
    sch_yield_l. steps_l. forces_l. iFrame; iSplit; eauto.
    (* both terminate *)
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI IstFull None.
  Proof using SchInSp_s SchInSp_t MainInSp.
    iStartSim. steps_l.
    rewrite /Sch.spawn /Sch.join.

    iAssert (Tid 0 0) with "[TID IST]" as "TID"; first iFrame.

    steps_l. iDestruct "ASM" as "->". steps_r.
    (* tgt yield *)
    sch_yield_ir; iSplit; first (iExists [], [], [], []; iPureIntro; esplits; ss).
    iIntros (st_src st_tgt) "IST TID".

    (* tgt inline - mem alloc - counter allocation *)
    steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (blk) "[↦ _]". steps_r. hss_r. steps_r.
    sch_yield_ir.

    (* tgt inline - mem store - counter initialization *)
    steps_r.
    iApply (wsim_mem_store with "[↦]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros"↦". steps_r. hss_r. steps_r.
    sch_yield_ir.

    (* create lock-guarded proposition *)
    iMod (own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)) as "[%γ [B W]]". { eapply frac_auth_valid; ss. }

    (* tgt inline - newlock *)
    steps_r. inline_r. force_r (0, 0, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iSplitL "TID B ↦"; eauto.
    { iFrame; SL_red; iSplit; eauto. iFrame. iExists _; SL_red; iFrame. }
    steps_r. hss. steps_r.

    (* src/tgt yields *)
    sch_yield_ii.
    steps_r. iDestruct "GRT" as "[TID [[%val [%γ_l [-> #I]]] %EQ]]".
    hss. steps_r.
    sch_yield_ir.

    iPoseProof "I" as "[%bofs_l [-> _]]".
    sch_yield_l. steps_l. force_l (Vptr bofs_l, Vptr (blk, 0%Z)). steps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    steps_l. steps_r. force_l (_,_). forces_l. iSplitL "W1".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [[-> ->] TKN1]]]]".
    rename _q0 into tid1.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* spawn thread 2 - incr *)
    steps_l. steps_r. force_l (_,_). forces_l. iSplitL "W2".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [[-> ->] TKN2]]]]". hss.
    rename _q0 into tid2.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 1 - incr *)
    steps_l. steps_r.  force_l (_,_,_,_). forces_l. iSplitL "TKN1 TID".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W1]]]]]]".
    hss. rename _q1 into vret.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 2 - incr *)
    steps_l. steps_r.  force_l (_,_,_,_). forces_l. iSplitL "TID TKN2".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W2]]]]]]".
    hss. rename _q1 into vret0.
    steps_r. hss. steps_r.
    sch_yield_ir.

    (* tgt inline - lock acquire *)
    steps_r. inline_r. steps_r.
    force_r (_, _, (γ_l, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    iFrame. iSplit; eauto.
    steps_r. hss. steps_r.
    sch_yield_ii.
    steps_r. iDestruct "GRT" as "[TID' [[-> [TKN P]] _]]". hss. steps_r.
    SL_red. iCombine "W1 W2" as "W".
    iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    sch_yield_ir.

    (* tgt inline - mem load *)
    steps_r.
    iApply (wsim_mem_load with "[PT]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "↦". hss_r. steps_r. hss_r. steps_r.

    (* tgt yield *)
    do 2 (sch_yield_ir).

    (* tgt inline - lock release *)
    steps_r. inline_r. steps_r.
    force_r (_, _, (γ_l, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    iSplitL "TKN TID B ↦".
    { iFrame; SL_red. iSplit; eauto. iFrame. iSplit; eauto. iSplit; eauto.
      iExists _; SL_red; iFrame.
    }
    steps_r. hss. steps_r.

    (* tgt yield *)
    sch_yield_ii.
    steps_r. iDestruct "GRT" as "[TID' [-> _]]". hss. steps_r.
    sch_yield_ir.

    (* both output - counter value *)
    sch_yield_l. step.
    steps_l. steps_r.
    sch_yield_ir. sch_yield_l.
    (* terminate both *)
    forces_l. iSplit; first eauto. step. iSplit; eauto.
  Unshelve. all: eauto.
  (*SLOW*)Qed.

  Definition init_cond := MainA.init_cond (↑N).

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.

  Definition ctxr :
    ctx_refines
      ((SpinLockMainA.t E sp_s) ★ ((SpinLockA.t E sp_t) ★ MemA.t sp_none), init_cond)
      ((SpinLockMainI.t)        ★ ((SpinLockA.t E sp_t) ★ MemA.t sp_none), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.

Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA.
Require Import SpinLockHeader SpinLockI SpinLockA SchHeader SchA MemA wsim_tactics SchTactics.
From iris Require Import frac_auth numbers.

Module SpinLockMainIA. Section SpinLockMainIA.
  Import SpinLockAS SpinLockMainAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!memGΓ Γ, !SchAGΣ Σ, !SchAGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (spc_s spc_user_s spc_mem : string → option fspec). (* spcs of lock/sch/mem *)
  Context (SchInSpc : spc_incl (SchAS.spc u_a spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.spc spc_s).
  Context (MainInSpc : spc_incl (SpinLockMainAS.spc u_a) spc_user_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t u_a spc_mem).
  Local Definition SpinLockA := (SpinLockA.t u_a spc_s).
  Local Definition SpinLockMainA := (SpinLockMainA.t u_a spc_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (SpinLockMainA ★ (MemA ★ SpinLockA)).
  Local Definition MI := (SpinLockMainI ★ (MemA ★ SpinLockA)).

  Lemma incr_simF : HSim.sim_fun open MA MI IstFull SpinLockMainName.incr.
  Proof.
    winit_simF u_a 0.
    (* process src precondition *)
    wsteps_l. iDestruct "ASM" as "[[-> [TID [%γ_l [#I F]]]] ->]". hss.
    rename q2 into γ_v, q4 into ofs_v, q6 into blk_v, q8 into ofs_l, q10 into blk_l, q9 into tid.
    (* main code *)
    wsteps_l. hss. wsteps_l. rewrite /SpinLockMainA.incr. wsteps_l.
    wsteps_r. hss. wsteps_r. rewrite /SpinLockMainI.incr. wsteps_r.
    unfold_iter_l. wsteps_l.
    (* tgt yields *)
    sch_yield_r. iFrame; ss; clear nths; iIntros (nths st_s st_t) "IST TID".
    wsteps_r. sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - lock acquire *)
    winline_r. wforce_r (tid, γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    wsteps_r. wforces_r. iFrame.
    iSplit; eauto. hss. wsteps_r.
    sch_yield_l. wforce_l false. wsteps_l.
    (* start coinduction for lock acquisition *)
    iApply wsim_reset. iStopProof. revert nths. combine_quant st_s. combine_quant st_t.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s nths]]) "[#I [F IST]] _ #CIH".
    unfold_iter_r. unfold_iter_l. wsteps_l. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. destruct q; cycle 1.
    { (* fail case *)
      wsteps_r. sch_yield_l. wforce_l false. wsteps_l. wby_coind "CIH".
      hss. iFrame. eauto.
    }
    (* success case *)
    wsteps_r. iDestruct "GRT" as "[[_ [TKN P]] <-]". hss. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    rewrite /lock_P; SL_red; iDestruct "P" as "[TKN [%x P]]"; SL_red; iDestruct "P" as "[PT P]".
    (* tgt inline - mem load *)
    winline_r. wforce_r (blk_v, ofs_v, Vint x, 1%Qp). wforces_r. iSplitL "PT"; iFrame; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID". wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - mem store *)
    winline_r. wforce_r (blk_v, ofs_v, Vint (x + 1)). wforces_r. iSplitL "PT"; iFrame; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    iCombine "P F" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    (* tgt inline - lock acquire - restore lock protected proposition *)
    winline_r. wforce_r (tid, γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    wforces_r.
    iSplitL "TID F PT TKN".
    { SL_red. rewrite /lock_P; ss. iSplit; iFrame; eauto. iSplit; eauto. iSplit.
      { iExact "I". }
      { iExists _; SL_red; iFrame. }
    }
    wsteps_r. hss. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[-> TID] _]". hss. wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID". wsteps_r.
    (* src yield *)
    sch_yield_l. wsteps_l. wforce_l true. wsteps_l. wforces_l. iFrame; iSplit; eauto.
    (* both terminate *)
    wsteps_l. wstep. iFrame. eauto.
  (*FAST*)Qed.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull SpinLockMainName.main.
  Proof.
    winit_simF u_a 0.
    (* process src precondition *)
    wsteps_l. iDestruct "ASM" as "[[-> TID] ->]". hss.
    (* tgt yield *)
    wsteps_r. sch_yield_r. iFrame; ss; clear nths; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - mem alloc - counter allocation *)
    winline_r. wforce_r 1. wforces_r. iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[%blk [-> [GRT _]]] ->]". hss. wsteps_r.
    wsteps_r. sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - mem store - counter initialization *)
    winline_r. wforce_r (blk, 0%Z, Vint 0). wforces_r. iFrame; iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    wsteps_r. sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* create lock-guarded proposition *)
    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { eapply frac_auth_valid; ss. }
    iIntros "[%γ [B W]]".
    (* tgt inline - newlock *)
    winline_r. wforce_r (0, existT 0 (lock_P (blk, 0%Z) γ)). wforces_r. iSplitL "TID B PT"; eauto.
    { SL_red; iSplit; eauto. iFrame. iExists _; SL_red; iFrame. }
    wsteps_r. hss. wsteps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[TID [%val [%γ_l [-> #I]]]] %EQ]". hss. wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    iPoseProof "I" as "[%b_l [%o_l [-> _]]]".
    sch_yield_l. wsteps_l. wforce_l (Vptr b_l o_l, Vptr blk 0). wsteps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".
    (* spawn thread 1 - incr *)
    wsteps_l. sch_spawn.
    { apply MainInSpc; ss. }
    { eapply (incr_spawnable). }
    iFrame; ss; clear nths st_s st_t.
    iSplit.
    { iSplit; eauto. }
    iIntros (tid nths st_s st_t) "IST TID TKN".
    wsteps_l. wsteps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wsteps_l.
    (* spawn thread 2 - incr *)
    sch_spawn.
    { apply MainInSpc; ss. }
    { eapply (incr_spawnable u_a). }
    iSplitL "IST"; ss; clear nths st_s st_t. iFrame.
    iSplit.
    { iSplit; eauto. }
    iIntros (tid2 nths st_s st_t) "IST TID TKN2".
    wsteps_l. wsteps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wsteps_l.
    (* join thread 1 - incr *)
    sch_join; iFrame.
    clear nths st_s st_t; iIntros (nths st_s st_t vret ret) "IST TID W1 /=".
    wsteps_r. sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wsteps_l.
    (* join thread 2 - incr *)
    sch_join; iFrame.
    clear nths st_s st_t; iIntros (nths st_s st_t vret2 ret2) "IST TID W2 /=".
    wsteps_l. wsteps_r.
    unfold_iter_l. wsteps_l.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wforce_l false. wsteps_l.
    (* tgt inline - lock acquire *)
    winline_r. wforce_r (0, γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). wforces_r. iFrame.
    iSplit; eauto.
    wsteps_r. hss. wsteps_r.
    (* start coinduction for lock acquisition *)
    iApply wsim_reset. iStopProof. revert nths. combine_quant st_s. combine_quant st_t.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s nths]]) "[#I [W1 [W2 IST]]] _ #CIH /=".
    unfold_iter_r. unfold_iter_l. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. destruct q; cycle 1.
    { (* fail case *)
      wsteps_r. sch_yield_l. wforce_l false. wsteps_l. wby_coind "CIH".
      hss. iFrame. eauto.
    }
    (* success case *)
    wsteps_r. iDestruct "GRT" as "[[-> [TID [TKN P]]] _]". hss. wsteps_r.
    SL_red. iCombine "W1 W2" as "W". iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - mem load *)
    winline_r. wforce_r (blk, 0%Z, Vint 2%Z, 1%Qp). wforces_r. iSplitL "PT"; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID". wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    (* tgt inline - lock release *)
    winline_r. wforce_r (0, γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). wforces_r.
    iSplitL "TKN TID B PT".
    { SL_red. iSplit; eauto. iFrame. iSplit; eauto. iSplit; eauto. iExists _; SL_red; iFrame. }
    wsteps_r. hss. wsteps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[-> TID] _]". hss. wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID".
    sch_yield_l. wforce_l true. wsteps_l.
    (* both output - counter value *)
    sch_yield_l. wstep.
    wsteps_l. wsteps_r.
    sch_yield_r. iFrame; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST TID". wsteps_r.
    sch_yield_l. wsteps_l. wforces_l. iSplit; eauto. wsteps_l.
    (* terminate both *)
    wstep. iSplit; eauto.
  (*FAST*)Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; iSplit; eauto. }
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.
End SpinLockMainIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Definition ctxr (u : univ_id) (spc_s spc_user_s spc_mem : string → option fspec)
      (SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s)
      (MainInSpc : spc_incl (SpinLockMainAS.spc u) spc_user_s)
      (MemInSpc : spc_incl MemA.spc spc_s) :
    ctx_refines
      ((SpinLockMainA.t u spc_s) ★ (MemA.t u spc_mem ★ (SpinLockA.t u spc_s)), emp%I)
      ((SpinLockMainI.t)         ★ (MemA.t u spc_mem ★ (SpinLockA.t u spc_s)), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End SpinLockMainIA.
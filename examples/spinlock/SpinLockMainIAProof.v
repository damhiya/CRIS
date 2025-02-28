Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA.
Require Import SpinLockHeader SpinLockI SpinLockA SchHeader SchA MemA wsim_tactics SchTactics.
From iris Require Import frac_auth numbers.

Module SpinLockMainIA. Section SpinLockMainIA.
  Import SpinLockAS SpinLockMainAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (spc_s spc_user_s spc_mem : string → option fspec). (* spcs of lock/sch/mem *)
  Context (SchInSpc : spc_incl (SchAS.spc u_a spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.Spc spc_s).
  Context (MainInSpc : spc_incl (SpinLockMainAS.spc u_a) spc_user_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Notation MemA := (MemA.t u_a spc_mem).
  Local Notation SpinLockA := (SpinLockA.t u_a spc_s).
  Local Notation SpinLockMainA := (SpinLockMainA.t u_a spc_s).
  Local Notation SpinLockMainI := (SpinLockMainI.t).
  Local Notation IstFull := (IstProd (IstSB SpinLockMainA.(HMod.scopes) Ist) IstEq).
  Local Notation MA := (SpinLockMainA ★ (MemA ★ SpinLockA)).
  Local Notation MI := (SpinLockMainI ★ (MemA ★ SpinLockA)).

  Lemma incr_simF : HSim.sim_fun open MA MI IstFull SpinLockMainName.incr.
  Proof.
    winit_simF u_a 0.
    wsteps_l. iDestruct "ASM" as "[[-> [%γ_l [#I F]]] ->]". hss.
    rename q2 into γ_v, q4 into ofs_v, q6 into blk_v, q7 into blk_l, q8 into ofs_l.
    wsteps_l. rewrite SAny.upcast_downcast. wsteps_l. rewrite /SpinLockMainA.incr. wsteps_l.
    wsteps_r. rewrite SAny.upcast_downcast. wsteps_r. rewrite /SpinLockMainI.incr. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths; iIntros (nths st_s st_t) "IST".
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    wsteps_r. wforces_r.
    iSplit; eauto. hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[_ [TKN P]] <-]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    rewrite /lock_P; SL_red; iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT C]".
    winline_r. wforce_r (blk_v, ofs_v, Vint x, 1%Qp). wforces_r. iSplitL "PT"; iFrame; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (blk_v, ofs_v, Vint (x + 1)). wforces_r. iSplitL "PT"; iFrame; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    iCombine "C F" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    winline_r. wforce_r (γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    wforces_r.
    iSplitL "F PT TKN".
    { SL_red. rewrite /lock_P; ss. iSplit; iFrame; eauto. iSplit; eauto. iSplit.
      { iExact "I". }
      { iExists _; SL_red; iFrame. }
    }
    wsteps_r. hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[-> _]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r.
    sch_yield_l. wsteps_l. wforces_l. iFrame; iSplit; eauto.
    wsteps_l. wstep. iFrame. eauto.
  Qed.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull SpinLockMainName.main.
  Proof.
    winit_simF u_a 0.
    wsteps_l. iDestruct "ASM" as "[-> ->]". hss.
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r 1. wforces_r. iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[%blk [-> [GRT _]]] ->]". hss. wsteps_r.
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (blk, 0%Z, Vint 0). wforces_r. iFrame; iSplit; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    (* create lock-guarded proposition *)
    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { eapply frac_auth_valid; ss. }
    iIntros "[%γ [B W]]".
    winline_r. wforce_r (existT 0 (lock_P (blk, 0%Z) γ)). wforces_r. iSplitL "B PT"; eauto.
    { SL_red; iSplit; eauto. iExists _; SL_red; iFrame. }
    wsteps_r. hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[%val [%γ_l [-> #I]]] %EQ]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    iPoseProof "I" as "[%b_l [%o_l [-> _]]]".
    sch_yield_l. wsteps_l. wforce_l (Vptr b_l o_l, Vptr blk 0). wsteps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".
    wsteps_l. sch_spawn.
    { apply MainInSpc; ss. }
    { eapply (incr_spawnable u_a). }
    iSplitL "IST"; ss; clear nths st_s st_t.
    iSplitL "W1".
    { rewrite /incr_pre. iExists _. iFrame. done. }
    iIntros (tid nths st_s st_t) "IST TKN".
    wsteps_l. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    sch_yield_l. wsteps_l.
    sch_spawn.
    { apply MainInSpc; ss. }
    { eapply (incr_spawnable u_a). }
    iSplitL "IST"; ss; clear nths st_s st_t.
    iSplitL "W2".
    { rewrite /incr_pre. iExists _. iFrame. done. }
    iIntros (tid2 nths st_s st_t) "IST TKN2".
    wsteps_l. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    sch_yield_l. wsteps_l.
    sch_join; iFrame.
    clear nths st_s st_t; iIntros (nths st_s st_t ret) "IST W1 /=".
    wsteps_r. sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    sch_yield_l. wsteps_l.
    sch_join; iFrame.
    clear nths st_s st_t; iIntros (nths st_s st_t ret2) "IST W2 /=".
    wsteps_l. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). wforces_r.
    iSplit; eauto.
    wsteps_r. hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[[-> [TKN P]] _]". hss. wsteps_r.
    SL_red. iCombine "W1 W2" as "W". iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (blk, 0%Z, Vint 2%Z, 1%Qp). wforces_r. iSplitL "PT"; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST". wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    winline_r. wforce_r (γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). wforces_r.
    iSplitL "TKN B PT".
    { SL_red. iSplit; eauto. iFrame. iSplit; eauto. iSplit; eauto. iExists _; SL_red; iFrame. }
    wsteps_r. hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    wsteps_r. iDestruct "GRT" as "[-> _]". hss. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST".
    sch_yield_l. wsteps_l. wstep.
    wsteps_l. wsteps_r.
    sch_yield_r. iSplitL "IST"; ss; clear nths st_s st_t; iIntros (nths st_s st_t) "IST". wsteps_r.
    sch_yield_l. wsteps_l. wforces_l. iSplit; eauto. wsteps_l. wstep.
    iSplit; eauto.
  Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; iSplit; eauto. }
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.
End SpinLockMainIA.
Section wctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Definition wctxr (u : univ_id) (spc_s spc_user_s spc_mem : univ_id → string → option fspec)
      (SchInSpc : ∀ u, spc_incl (SchAS.spc u (spc_user_s u)) (spc_s u))
      (MainInSpc : ∀ u, spc_incl (SpinLockMainAS.spc u) (spc_user_s u))
      (MemInSpc : ∀ u, spc_incl MemA.Spc (spc_s u)) :
    ctx_refines
      ((SpinLockMainA.t u (spc_s u)) ★ (MemA.t u (spc_mem u) ★ (SpinLockA.t u (spc_s u))), emp%I)
      ((SpinLockMainI.t)             ★ (MemA.t u (spc_mem u) ★ (SpinLockA.t u (spc_s u))), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End wctxr. End SpinLockMainIA.
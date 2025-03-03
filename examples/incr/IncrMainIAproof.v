Require Import CRIS.

Require Import IncrMainI IncrMainA SchA MemA wsim_tactics SchTactics.
From iris Require Import frac_auth numbers.

Module IncrIA. Section IncrIA.
  Import IncrMainAS.
  Local Existing Instance IncrMainA.RA_inG.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s: univ_id).
  Context (spc_s spc_user_s spc_mem : string → option fspec).
  Context (SchInSpc : spc_incl (SchAS.spc u_s spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.Spc spc_s).
  Context (MainInSpc : spc_incl (IncrMainAS.spc u_s) spc_user_s).

  Local Definition MemA := (MemA.t u_s spc_mem).
  Local Definition IncrMainA := (IncrMainA.t u_s spc_s).
  Local Definition IncrMainI := (IncrMainI.t).
  Local Definition IstFull := (IstProd (IstSB IncrMainA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (IncrMainA ★ MemA).
  Local Definition MI := (IncrMainI ★ MemA).

  Lemma f_simF : HSim.sim_fun open MA MI IstFull MainName.f.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "[[-> [C #INV]] ->]". hss.

    wsteps_l. hss. wsteps_l.
    wsteps_r. hss. wsteps_r.
    rewrite /IncrMainI.f /IncrMainA.f /=. wsteps_r.
    
    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".

    rewrite /IncrMainAS.f_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (x) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    winline_r. wsteps_r.
    wforce_r (q5, q6, Vint x, 1%Qp).
    wsteps_r. wforce_r ([Vptr q5 q6]↑).
    wsteps_r. wforce_r.
    iSplitL "PT".
    { iFrame; ss. }
    wsteps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss.
    wsteps_r.

    winline_r. wsteps_r.
    wforce_r (q5, q6, Vint (x + 1)). wsteps_r.
    wforce_r ([Vptr q5 q6; Vint (x + 1)]↑). wsteps_r.
    wforce_r. iSplitL "PT"; iFrame; ss. wsteps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[PT CA]") as "_".
    { iExists (x + 1)%Z; SL_red; ss; iFrame. }
    
    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    
    sch_yield_l.
    wsteps_l. wforce_l. wsteps_l. wforce_l. iSplitL "C"; iFrame; eauto. wsteps_l.
    wstep; eauto.
  Qed.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull MainName.main.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "[-> ->]". hss.
    wsteps_l.

    (* src/tgt yield *)
    wsteps_r.
    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".
    sch_yield_l.

    (* src/tgt alloc *)
    wsteps_l. wforce_l 1. wsteps_l. wforce_l. wsteps_l.
    wforce_l. iSplit; eauto. wsteps_l.
    wsteps_r. wcall "IST".
    wsteps_l. iDestruct "ASM" as "[[%b [-> [PT _]]] ->]". hss.
    wsteps_r. hss. wsteps_r.

    (* tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    (* tgt store *)
    winline_r. wsteps_r. wforce_r (b, 0%Z, Vint 0%Z). wsteps_r.
    wforce_r. wsteps_r. wforce_r. iSplitL "PT".
    { iFrame. eauto. }
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    sch_yield_l.

    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { apply frac_auth_valid; ss. }

    iIntros "[%γc [A F]]".
    iMod (inv_alloc (ccounter_syn 0 γc b 0%Z) _ _ _ N_main with "[PT A]") as "#I"; eauto.
    { rewrite /ccounter_syn; SL_red; iExists 0; SL_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    iCombine "F1 I" as "F1". iCombine "F2 I" as "F2".
    wsteps_l. wsteps_r.

    (* src/tgt spawns *)
    sch_spawn.
    { apply MainInSpc; ss. }
    { instantiate (1:= λ _, existT 0 (counter_syn γc (1/2)%Qp 1%Z)).
      instantiate (2:= (b, 0%Z, 0%Z, γc)).
      split.
      - rewrite /precond /fspec_simple; ss.
      - iIntros (ret) "[%vret [$ [[-> P] ->]]]"; ss.
        iExists _; iSplit; SL_red; eauto.
    }
    iFrame. iSplitL "" ; eauto.
    clear nths st_s st_t.
    iIntros (tid nths st_s st_t) "IST TOKEN".

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    sch_yield_l.

    sch_spawn.
    { apply MainInSpc; ss. }
    { instantiate (1:= λ _, existT 0 (counter_syn γc (1/2)%Qp 1%Z)).
      instantiate (2:= (b, 0%Z, 0%Z, γc)).
      split.
      - rewrite /precond /fspec_simple; ss.
      - iIntros (ret) "[%vret [$ [[-> P] ->]]]"; ss.
        iExists _; iSplit; SL_red; eauto.
    }
    iFrame. iSplitL "" ; eauto.
    clear nths st_s st_t.
    iIntros (tid2 nths st_s st_t) "IST TOKEN2".

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    sch_yield_l.

    sch_join. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t []) "IST Q /="; SL_red.

    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    sch_yield_l.

    sch_join. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t []) "IST Q2 /="; SL_red.

    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    iInv "I" as "INV" "INVA"; iEval (SL_red) in "INV"; iDestruct "INV" as "[%x INV]".
    iEval (SL_red) in "INV". iDestruct "INV" as "[PT C]".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    winline_r. wsteps_r. wforce_r (b, 0%Z, (Vint 2), 1%Qp). wsteps_r. wforces_r.
    iSplitL "PT"; eauto.
    wsteps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. wsteps_r.

    iMod ("INVA" with "[CA PT]") as "_".
    { SL_red. iExists 2; SL_red; iFrame. }

    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    sch_yield_l. wstep.
    wsteps_l. wsteps_r.

    sch_yield_r. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    sch_yield_l.
    wsteps_l. wforce_l. wsteps_l. wforce_l. iSplit; eauto.
    wsteps_l. wsteps_r.
    wstep. eauto.
  Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; eauto. }
    { eapply main_simF. }
    { eapply f_simF. }
  Qed.
End IncrIA.

Section wctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition wctxr (u : univ_id) (spc_s spc_user_s spc_mem : univ_id → string → option fspec)
      (SchInSpc : ∀ u, spc_incl (SchAS.spc u (spc_user_s u)) (spc_s u))
      (MainInSpc : ∀ u, spc_incl (IncrMainAS.spc u) (spc_user_s u))
      (MemInSpc : ∀ u, spc_incl MemA.Spc (spc_s u)) :
    ctx_refines
      ((IncrMainA.t u (spc_s u)) ★ (MemA.t u (spc_mem u)), emp%I)
      ((IncrMainI.t)             ★ (MemA.t u (spc_mem u)), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End wctxr. End IncrIA.

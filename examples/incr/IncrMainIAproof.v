Require Import CRIS.

Require Import IncrMainI IncrMainA SchA MemA wsim_tactics wsim_sch.
From iris Require Import frac_auth numbers.

Module IncrIA. Section IncrIA.
  Import IncrMainAS.
  Local Existing Instance IncrMainA.RA_inG.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s u_t : univ_id).
  Context (ginv_s : invspec) (spc_s spc_user_s spc_mem : string → option fspec).
  Context (SchInSpc : spc_incl (SchAS.spc u_s spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.Spc spc_s).
  Context (MainInSpc : spc_incl (IncrMainAS.spc u_s) spc_user_s).

  Local Notation MemA := (MemA.t ginv_s spc_mem).
  Local Notation IncrMainA := (IncrMainA.t u_s ginv_s spc_s).
  Local Notation IncrMainI := (IncrMainI.t).
  Local Notation IstFull := (IstProd (IstSB IncrMainA.(HMod.scopes) Ist) IstEq).
  Local Notation MA := (IncrMainA ★ MemA).
  Local Notation MI := (IncrMainI ★ MemA).

  Lemma f_simF : HSim.sim_fun open MA MI IstFull MainName.f.
  Proof.
    init_wsim u_s u_t.

    w_steps_l. iDestruct "ASM" as "[[-> [C I]] ->]". hss.

    w_step_l. rewrite SAny.upcast_downcast. hss. w_steps_l.

    w_steps_r. rewrite SAny.upcast_downcast. hss. w_steps_r.
    rewrite /IncrMainI.f /IncrMainA.f /=. w_steps_l. w_steps_r.
  
    _prep_macro_r. _prep_macro_l.
    iApply (wsim_yield_tgt); first done.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".

    rewrite /IncrMainAS.f_inv; ss.
    iInv "I" as "I" "IA". SL_red.
    iDestruct "I" as (x) "PT"; SL_red; iDestruct "PT" as "[PT CA]".

    w_inline_r. w_steps_r.
    w_force_r (q5, q6, Vint x, 1%Qp).
    w_steps_r. w_force_r ([Vptr q5 q6]↑).
    w_steps_r. w_force_r.
    iSplitL "PT".
    { iFrame; ss. }
    w_steps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss.
    w_steps_r.

    w_inline_r. w_steps_r.
    w_force_r (q5, q6, Vint (x + 1)). w_steps_r.
    w_force_r ([Vptr q5 q6; Vint (x + 1)]↑). w_steps_r.
    w_force_r. iSplitL "PT"; iFrame; ss. w_steps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss. w_steps_r.

    iApply wsim_yield_src; eauto.
    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[PT CA]") as "_".
    { iExists (x + 1)%Z; SL_red; ss; iFrame. }

    w_steps_l. w_force_l. w_steps_l. w_force_l. iSplitL "C"; iFrame; eauto.
    w_steps_l. w_step; eauto.
  Qed.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull MainName.main.
  Proof.
    init_wsim u_s u_t.

    w_steps_l. iDestruct "ASM" as "[-> ->]". hss.
    w_steps_l. _prep_macro_l.

    (* src/tgt yield *)
    w_steps_r. _prep_macro_r.
    iApply (wsim_yield_tgt); first done.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done.

    (* src/tgt alloc *)
    w_steps_l. w_force_l 1. w_steps_l. w_force_l. w_steps_l.
    w_force_l. iSplit; eauto. w_steps_l.
    w_steps_r. w_call "IST".
    w_steps_l. iDestruct "ASM" as "[[%b [-> [PT _]]] ->]". hss. _prep_macro_l.
    w_steps_r. hss. w_steps_r. _prep_macro_r.

    (* tgt yield *)
    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    (* tgt store *)
    w_inline_r. w_steps_r. w_force_r (b, 0%Z, Vint 0%Z). w_steps_r.
    w_force_r. w_steps_r. w_force_r. iSplitL "PT".
    { iFrame. eauto. }
    w_steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. w_steps_r. _prep_macro_r.

    (* src/tgt yield *)
    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done. _prep_macro_l. _prep_macro_r.

    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { apply frac_auth_valid; ss. }

    iIntros "[%γc [A F]]".
    iMod (inv_alloc (ccounter 0 γc b 0%Z) _ _ _ N_main with "[PT A]") as "#I"; eauto.
    { rewrite /ccounter; SL_red; iExists 0; SL_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    iCombine "F1 I" as "F1". iCombine "F2 I" as "F2".

    (* src/tgt spawns *)
    iApply (wsim_spawn with "IST F1").
    { done. }
    { apply MainInSpc; ss. }
    { Unshelve. 2:{ ss. exact (b, 0%Z, 0%Z, γc). }
      2:{ exact (λ _, existT 0 (<own> γc (frac_auth_frag (1/2)%Qp 1%Z)))%SRF. }
      { intros tid. split; ss.
        { iIntros "[$ [C #I]]"; rewrite /precond /fspec_simple; ss; iFrame; eauto. }
        { iIntros (ret) "[%vret [$ [[-> P] ->]]]"; ss. iExists _; iSplit; SL_red; eauto. }
      }
    }
    clear nths st_s st_t.
    iIntros (tid nths st_s st_t) "IST TOKEN".
    _prep_macro_l. _prep_macro_r.

    (* src/tgt yield *)
    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done. _prep_macro_l. _prep_macro_r.

    iApply (wsim_spawn with "IST F2").
    { done. }
    { apply MainInSpc; ss. }
    { Unshelve. 2:{ ss. exact (b, 0%Z, 0%Z, γc). }
      2:{ exact (λ _, existT 0 (<own> γc (frac_auth_frag (1/2)%Qp 1%Z)))%SRF. }
      { intros tid'. split; ss.
        { iIntros "[$ [C #I]]"; rewrite /precond /fspec_simple; ss; iFrame; eauto. }
        { iIntros (ret) "[%vret [$ [[-> P] ->]]]"; ss. iExists _; iSplit; SL_red; eauto. }
      }
    }
    clear nths st_s st_t.
    iIntros (tid2 nths st_s st_t) "IST TOKEN2".
    _prep_macro_l. _prep_macro_r.

    (* src/tgt yield *)
    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done. _prep_macro_l. _prep_macro_r.

    iApply (wsim_join with "IST TOKEN"); first done.
    clear nths st_s st_t. iIntros (nths st_s st_t []) "IST Q /="; SL_red.
    _prep_macro_l. _prep_macro_r.

    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done. _prep_macro_l. _prep_macro_r.

    iApply (wsim_join with "IST TOKEN2"); first done.
    clear nths st_s st_t. iIntros (nths st_s st_t []) "IST Q2 /="; SL_red.
    _prep_macro_l. _prep_macro_r.

    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    iInv "I" as "INV" "INVA"; iEval (SL_red) in "INV"; iDestruct "INV" as "[%x INV]".
    iEval (SL_red) in "INV". iDestruct "INV" as "[PT C]".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    w_inline_r. w_steps_r. w_force_r (b, 0%Z, (Vint 2), 1%Qp). w_steps_r. w_forces_r.
    iSplitL "PT"; eauto.
    w_steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. w_steps_r. _prep_macro_r.

    iMod ("INVA" with "[CA PT]") as "_".
    { SL_red. iExists 2; SL_red; iFrame. }

    iApply wsim_yield_tgt; first done. iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".
    iApply wsim_yield_src; first done.

    w_step. w_steps_l. w_force_l. w_step_l. w_force_l. iSplit; eauto. w_steps_l.
    w_steps_r.

    w_step. eauto.
  Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; eauto. }
    { eapply main_simF. }
    { eapply f_simF. }
  Qed.
End IncrIA.

Notation "'<[' u 'CTX' v ']=' I A" := ({ k | ∀ u v, u >= v + k → ctx_refines I A})
  (at level 200, u name, v name, I, A at level 9, right associativity).
Section wctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !memGΓ Γ, !IncrMainAGΓ Γ}.
  (* Context (I A : univ_id → HMod.modc). *)
  (* Goal <[u CTX v]= (I u) (A u). *)
  Definition wctxr (gi : univ_id → invspec) (spc_s spc_user_s spc_mem : univ_id → string → option fspec)
      (SchInSpc : ∀ u, spc_incl (SchAS.spc u (spc_user_s u)) (spc_s u))
      (MainInSpc : ∀ u, spc_incl (IncrMainAS.spc u) (spc_user_s u))
      (MemInSpc : ∀ u, spc_incl MemA.Spc (spc_s u)) :
    <[u CTX v]=
        ((IncrMainA.t u (gi u) (spc_s u)) ★ (MemA.t (gi u) (spc_mem u)), emp%I)
        ((IncrMainI.t)                    ★ (MemA.t (gi u) (spc_mem u)), emp%I).
  Proof. exists 1; intros u v GE; eapply main_adequacy, sim; eauto. Defined.
End wctxr. End IncrIA.
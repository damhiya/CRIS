Require Import CRIS.
Require Import FaaHeader ClientI ClientA FaaA.
Require Import SchA SchTactics MemA MemTactics.
From iris Require Import frac_auth numbers.

(* Proof of refinement between ClientA.t and ClientI.t *)
Module ClientIA. Section ClientIA.
  Import ClientA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !incrG}.

  Context (E : coPset) (Hsub : ↑N_main ⊆ E).
  Context (sp_user : spl_type).
  Context (sp_s : string → option fspec).
  Context (Hsch : sp_incl (SchA.sp sp_user E) sp_s).
  Context (Hclient : spl_sub (ClientA.sp E) sp_user).

  Local Definition IstFull := (IstProd (IstSB (ClientA.t E sp_s).(Mod.scopes) IstTrue) IstEq).
  Local Definition init_cond := ClientA.init_cond E.
  Local Definition MA := (ClientA.t E sp_s ★ MemA.t sp_none).
  Local Definition MI := ((ClientI.t ★ FaaA.t) ★ MemA.t sp_none).

  Lemma f_spawnable γ v bofs :
    SchA.fspec_spawnable E (incr_spec E)
      (λ varg arg,
        ⌜varg = arg ∧ varg = ([Vptr bofs]↑↑)⌝
        ∗ counter γ (1/2) v
        ∗ incr_inv 0 γ bofs)%I
      (λ vret ret,
        existT 0 ((⌜vret = ret ∧ vret = tt↑↑⌝ ∗ counter_syn γ (1/2) (v + 2))%SAT)).
  Proof using.
    rewrite /SchA.fspec_spawnable /fspec_sch /fspec_virtual /precond /postcond /incr_spec /=.
    intros [mtid stid]; ss. eexists (_, _, (bofs, v, γ)); split; red; ii.
    - unfold_pre_post.
      iIntros "[W [% [-> [TID [% [-> [[-> ->] [C #INV]]]]]]]]". iFrame. eauto.
    - unfold_pre_post. iIntros "[$ [$ [[-> C] ->]]]". iExists _; iSplitR; eauto.
      iExists _; iSplitR; eauto. SL_red. iSplitR; eauto.
  Qed.

  Lemma incr_simF : ISim.sim_fun open MA MI init_cond IstFull (Some IncrHdr.incr).
  Proof using Hsch Hclient Hsub.
    init_simF.

    steps_l. iDestruct "ASM" as "[TID [[-> [C #INV]] ->]]". hss_l.
    destruct _q7 as [b ofs]. rename _q3 into mtid, _q4 into stid, _q6 into γ, _q8 into v.

    steps_l. hss. steps_l.
    steps_r. hss. steps_r.
    rewrite /ClientI.incr /ClientA.incr /=. norm_l; norm_r.

    sch_yield_ir.

    (* tgt inline - faa *)
    steps_r; inline_r; steps_r.
    hss_r; steps_r.
    sch_yield_ir.

    rewrite /incr_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (x) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    (* operational atomicity here *)
    forces_r; iFrame "PT"; steps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[GRT CA]") as "_".
    { iExists (x + 1)%Z; SL_red; ss; iFrame. }
    sch_yield_ir.

    rewrite /incr_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (y) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    (* operational atomicity here *)
    forces_r; iFrame "PT"; steps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[GRT CA]") as "_".
    { iExists (y + 1)%Z; SL_red; ss; iFrame. }
    sch_yield_ir.

    steps_r; hss_r; steps_r.
    sch_yield_ir.
    steps_r.

    sch_yield_l; steps_l; forces_l; iFrame "TID".
    iSplitL "C".
    { iFrame. replace (v + 1 + 1)%Z with (v + 2)%Z by lia. iFrame. eauto. }
    steps_l. step; eauto.
(*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI init_cond IstFull None.
  Proof using Hsch Hclient Hsub.
    init_simF.

    steps_l.

    (* src/tgt yield *)
    steps_r.
    sch_yield_ir. iSplitL.
    { iExists [], [], [], []; iSplit; eauto.
      iSplit; eauto.
      { iPureIntro; splits; ss; unfold_mod; ss. }
    }
    iIntros (??) "IST TID".

    (* tgt alloc *)
    steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (blk) "[map _]". steps_r; hss_r; steps_r.
    sch_yield_ir.
    sch_yield_ir.

    (* tgt store *)
    steps_r.
    iApply (wsim_mem_store with "map");
      [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "map". steps_r. hss_r. steps_r.
    sch_yield_ir.
    sch_yield_l. force_l (Vptr (blk, 0%Z)). steps_l. sch_yield_l. steps_l.

    (* spawn *)
    iMod (own_alloc ((●F 0%Z ⋅ ◯F{1} 0%Z))) as "[%γc [A F]]".
    { apply frac_auth_valid; ss. }
    iMod (inv_alloc (ccounter_syn 0 γc (blk, 0%Z)) _ _ _ N_main with "[map A]") as "#I"; eauto.
    { rewrite /ccounter_syn; SL_red; iExists 0; SL_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    iCombine "F1 I" as "F1". iCombine "F2 I" as "F2".

    (* src/tgt spawns *)
    rewrite /Sch.spawn; steps_r; steps_l.
    force_l (_, _); forces_l; iSplitL "F1".
    { iExists _; iSplit; eauto.
      iExists _, _, _; iSplit.
      { iPureIntro; split; [done|split; [done|]].
        eexists; split; last eapply f_spawnable.
        eapply Hclient; ss.
      }
      ss; iFrame; iSplit; eauto.
    }
    steps_l. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [[-> ->] Handle]]]]". hss.
    rename _q0 into tid1. steps_r. hss_r. steps_r.
    sch_yield_ir.
    sch_yield_l.

    rewrite /Sch.spawn; steps_r; steps_l.
    force_l (_, _); forces_l; iSplitL "F2".
    { iExists _; iSplit; eauto.
      iExists _, _, _; iSplit.
      { iPureIntro; split; [done|split; [done|]].
        eexists; split; last eapply f_spawnable.
        eapply Hclient; ss.
      }
      ss; iFrame; iSplit; eauto.
    }
    steps_l. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [[-> ->] Handle2]]]]". hss.
    rename _q0 into tid2. steps_r. hss_r. steps_r.
    sch_yield_ir.
    sch_yield_l.

    rewrite /Sch.join; steps_r; steps_l.
    force_l (_, _, _, _); forces_l. iFrame "TID Handle"; iSplit; [iExists _; eauto|]. steps_l.
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% ASM]]]]"; hss.
    iDestruct "ASM" as "[[% ->] [TID ASM]]". hss. SL_red. iDestruct "ASM" as "[[-> ->] Q]".
    steps_r. hss_r. steps_r.
    sch_yield_ir.
    sch_yield_l.

    rewrite /Sch.join; steps_r; steps_l.
    force_l (_, _, _, _); forces_l; iFrame "Handle2 TID"; iSplit; [iExists _; eauto|]. steps_l.
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% ASM]]]]"; hss.
    iDestruct "ASM" as "[[% ->] [TID ASM]]". hss. SL_red. iDestruct "ASM" as "[[-> ->] Q2]".
    steps_r. hss_r. steps_r.
    sch_yield_ir.

    iInv "I" as "INV" "INVA"; iEval (SL_red) in "INV"; iDestruct "INV" as "[%x INV]".
    iEval (SL_red) in "INV". iDestruct "INV" as "[PT C]".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    steps_r.
    iApply (wsim_mem_load with "[PT]");
        [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "PT". steps_r. hss. steps_r.

    iMod ("INVA" with "[CA PT]") as "_".
    { SL_red. iExists _; SL_red; iFrame. }

    sch_yield_ir. steps_r.
    sch_yield_ir.
    sch_yield_l; steps_l.

    step.
    steps_l. steps_r.
    sch_yield_ir.
    sch_yield_l. steps_l. forces_l. iSplit; eauto.
    step. eauto.
(*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof using Hsch Hclient Hsub.
    init_sim.
    { eapply incr_simF. }
    { eapply main_simF. }
  Qed.
End ClientIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !incrG}.

  Definition ctxr (E : coPset) (sp_s : string → option fspec) (sp_user : spl_type) :
    ↑ClientA.N_main ⊆ E →
    spl_sub (ClientA.sp E) sp_user →
    sp_incl (SchA.sp sp_user E) sp_s →
    ctx_refines
      (ClientA.t E sp_s   ★ MemA.t sp_none, init_cond E)
      (ClientI.t          ★ FaaA.t ★ (MemA.t sp_none), emp%I).
  Proof using.
    etrans; cycle 1. { do 2 ctxr_rotate. ctxr_refl. }
    eset (GRP := ClientI.t ★ _).
    etrans; cycle 1. { ctxr_rotate. ctxr_refl. }
    do 2 ctxr_rotate.
    eapply main_adequacy, sim; eauto.
  Qed.
End ctxr. End ClientIA.

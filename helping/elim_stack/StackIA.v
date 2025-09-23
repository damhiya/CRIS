Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics.
Require Import SchHeader SchA SchTactics.
Require Import StackHeader StackA StackI.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, Hsch : !newschG, !concG, !stackG} (N : namespace).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t.
  Local Definition StackM := StackM.t.
  Local Definition StackI := StackI.t.
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (StackM N)) IstTrue) IstEq).
  Local Notation MA := (StackM N ★ MemA).
  Local Notation MI := (StackI ★ MemA).

  Let offerN := N .@ "offer".
  Let stackN := N .@ "stack".

  Lemma new_stack_simF : ISim.sim_fun open MA MI init_cond IstFull (Some StackHdr.new_stack).
  Proof using Hsch.
    init_simF.
    steps_l. unfold_lat_img_l.

    steps_r. destruct (arg ↓) as [args|] eqn : Harg; cycle 1.
    { sch_yield_l. steps_l. iDestruct "ASM" as "[[% ->] _]"; hss. }

    clear Harg.

    (* allocate new stack *)
    steps_r. sch_yield_rr. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (stackb) "[↦stack [↦val _]]".
    steps_r. hss_r. steps_r.
    sch_yield_rr. steps_r. sch_yield_rr. steps_r.

    (* initialize stack *)
    iApply (wsim_mem_store with "↦stack");
      [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "↦stack". steps_r. hss_r. steps_r. sch_yield_rr.

    steps_r.
    iApply (wsim_mem_store with "↦val");
      [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "↦val". steps_r. hss_r. steps_r. sch_yield_rr. steps_r.

    sch_yield_l. steps_l. iDestruct "ASM" as "[[% ->] _]"; hss.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid_discrete. split; done. }
    iMod (inv_alloc (syn_stack_inv γs stackb 0%Z 0) _ _ _ stackN with "[-Hs◯ IST]")
      as "#Hinv"; eauto.
    { apply nclose_subseteq. }
    { rewrite SLRed_red. iExists (Vint 0), None, []; iFrame; eauto. }
    force_l ((Vptr (stackb, 0%Z))↑). steps_l. force_l.
    iFrame "Hs◯"; iSplit; eauto.
    { iSplit; eauto. iExists _; iSplit; eauto. iExists _, _; iSplit; eauto. }
    steps_l. sch_yield_l. step. iSplit; eauto.
  Unshelve. all: eauto. all: try exact 0.
  Qed.

  Lemma push_simF : ISim.sim_fun open MA MI init_cond IstFull (Some StackHdr.push).
  Proof using Hsch.
    init_simF.
    steps_l; unfold_lat_img_l.

    (* ill-formed argument *)
    destruct (classic (∃ blk ofs v, arg = [Vptr (blk, ofs); v]↑)); cycle 1.
    { admit. }
    des; subst; hss.

    steps_r.
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "IST /=".
    destruct_quant CIH.

    unfold_iter_r; rewrite {1}/StackI._push; steps_r.
    sch_yield_rr. steps_r. sch_yield_rr. steps_r.

    (* opening invariant *)
    sch_yield_l; steps_l. hss.
    iDestruct "ASM"  as "[[%Heq [[%stackb [%stackofs [-> #Hinv]]] stack]] _]".
    symmetry in Heq; hss.
    rename _q1 into γs, _q3 into l.

    (* load *)
    iInv "Hinv" as "Hstack" "close".
    rewrite SLRed_red.
    iDestruct "Hstack" as "[%stack_rep [%offer_rep [%l' [Hs [H↦ [Hlist Hoffer]]]]]]".

    iApply (wsim_mem_load with "[H↦]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "H↦". steps_r. hss_r. steps_r.

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { rewrite /stack_inv. do 3 (SL_red; iExists _); SL_red; iFrame. }
    force_l true. steps_l. force_l; iSplitL "stack"; iFrame.
    { iSplit; eauto. iSplit; eauto. iExists _, _; iFrame "Hinv"; eauto. }
    steps_l; unfold_lat_img_l. hss.
    iClear "Hinv". clear dependent l l' γs offer_rep.

    (* alloc new head *)
    sch_yield_rr. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (head_newb) "[Hnewv [Hnewhead _]]". steps_r. hss_r. steps_r.

    (* store to new head *)
    steps_r. sch_yield_rr. steps_r. sch_yield_rr. steps_r.
    iApply (wsim_mem_store with "Hnewv");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hnewv". steps_r. hss_r. steps_r. sch_yield_rr. steps_r.
    iApply (wsim_mem_store with "Hnewhead");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hnewhead". steps_r. hss_r. steps_r.

    (* try push *)
    sch_yield_rr. steps_r.
    steps_l; unfold_lat_img_l. sch_yield_l. steps_l.
    iDestruct "ASM" as "[[%EQ [#[% [% [-> #Hinv]]] Hl']] _]"; symmetry in EQ; hss.
    rename _q1 into γs, _q3 into l.
    iInv "Hinv" as "Hstack" "close".
    rewrite SLRed_red.
    iDestruct "Hstack" as "[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]".
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp".
    case_decide; subst.
    { (* success *)
      steps_r. hss_r. steps_r.
      iCombine "Hs Hl'" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs Hl'") as "[Hs Hl']".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      iMod ("close" with "[Hnewv Hnewhead Hoffer Hlist H↦ Hs]") as "_".
      { iExists _, offer_rep', (v :: l'). iFrame. iExists 1%Qp; iSplit; eauto.
        rewrite Z.add_0_l.
        destruct stack_rep, stack_rep'; inv Hcomp; des_ifs.
        simpl_bool; des; do 2 destruct (dec _ _); clarify.
      }
      force_l false. force_l. force_l. iSplitL "Hl'"; eauto.
      steps_l.

      sch_yield_rr. steps_r.
      iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". steps_r. hss_r. steps_r. sch_yield_rr. steps_r. sch_yield_l. step. eauto.
    }

    (* failure - make an offer *)
    steps_r. hss_r. steps_r.
    iMod ("close" with "[Hnewv Hnewhead Hoffer Hlist H↦ Hs]") as "_".
    { iExists _, offer_rep', l'. iFrame. }
    force_l true. force_l. iSplitL "Hl'"; iFrame.
    { iSplit; eauto. iSplit; eauto. rewrite /is_stack; iExists _, _; iSplit; eauto. }
    steps_l.

    sch_yield_rr. steps_r.
    iCombine "Hval" "Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r. hss_r. steps_r. sch_yield_rr. steps_r.
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep', stack_rep; inv Hcomp; des_ifs. }

    steps_r. sch_yield_rr. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (offerb) "[Hofferv [Hofferst _]]".
    steps_r; hss_r; steps_r.

    sch_yield_rr; steps_r. sch_yield_rr; steps_r.
    iApply (wsim_mem_store with "[Hofferv]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "Hofferv". steps_r. hss_r. steps_r.

    sch_yield_rr. steps_r.
    iApply (wsim_mem_store with "[Hofferst]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "Hofferst". steps_r. hss_r. steps_r.
    rewrite Z.add_0_l.

    sch_yield_rr; steps_r.
  Admitted.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { split; et. }
    { apply new_stack_simF. }
    { apply push_simF. }
  Qed.

  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr :
    ctx_refines
      (StackM.t N ★ MemA.t, emp%I)
      (StackI.t ★ MemA.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End StackIM. End StackIM.

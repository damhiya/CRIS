Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics.
Require Import SchHeader SchA SchTactics.
Require Import StackHeader StackA StackI.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !newschG, !concG, !stackG} (N : namespace).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t.
  Local Definition StackA := StackA.t.
  Local Definition StackI := StackI.t.
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (StackA N)) IstTrue) IstEq).
  Local Notation MA := (StackA N ★ MemA).
  Local Notation MI := (StackI ★ MemA).

  Lemma new_stack_simF : ISim.sim_fun open MA MI init_cond IstFull (Some StackHdr.new_stack).
  Proof using.
    init_simF.
    steps_l. unfold_lat_img_l.

    (* ill-formed argument *)
    destruct (arg↓) as [v|] eqn:E; cycle 1.
    { sch_yield_l. steps_l. hss.
      iDestruct "ASM" as "[[% %] _]". des; subst. hss.
    }

    (* tgt yield *)
    steps_r. sch_yield_rr.

    (* tgt inline - mem alloc *)
    steps_r. inline_r. force_r 2. forces_r.
    iSplit; et.
    steps_r. iDestruct "GRT" as "[[%blk [-> [↦stack [↦offer _]]]] ->]".
    rewrite ?Z.add_0_l.
    hss_r; steps_r.

    (* tgt yield *)
    sch_yield_rr. steps_r.
  Admitted.

  Lemma push_simF : ISim.sim_fun open MA MI init_cond IstFull (Some StackHdr.push).
  Proof using.
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
    iEval (rewrite /stack_inv) in "Hstack".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%stack_rep Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%offer_rep Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%l' Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[Hs [H↦ [Hlist Hoffer]]]".
    steps_r; inline_r; steps_r.
    force_r (blk, ofs, 1%Qp, _). forces_r. iFrame "H↦"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[H↦ ->]->]". hss_r. steps_r.
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { rewrite /stack_inv. do 3 (SL_red; iExists _); SL_red; iFrame. }
    force_l true. steps_l. force_l; iSplitL "stack"; iFrame.
    { iSplit; eauto. iSplit; eauto. iExists _, _; iFrame "Hinv"; eauto. }
    steps_l; unfold_lat_img_l. hss.

    (* alloc new head *)
    sch_yield_rr. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (head_newb) "[Hnewv [Hnewhead _]]". steps_r. hss_r. steps_r.

    (* store to new head *)
    steps_r. sch_yield_rr. steps_r. sch_yield_rr. steps_r.
    inline_r; force_r (head_newb, 0%Z, Vundef, _); forces_r.
    iFrame "Hnewv"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[Hnewv ->] ->]". hss_r. steps_r.
    sch_yield_rr. steps_r.
    inline_r; force_r (head_newb, 1%Z, Vundef, _); forces_r.
    iFrame "Hnewhead"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[Hnewhead ->] ->]". hss_r. steps_r.

    (* CAS *)
    sch_yield_rr. steps_r.
    steps_l; unfold_lat_img_l. sch_yield_l. steps_l.
    iInv "Hinv" as "Hstack" "close". clear offer_rep l'.
    iEval (rewrite /stack_inv) in "Hstack".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%stack_rep' Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%offer_rep Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[%l' Hstack]".
    iEval (SL_red) in "Hstack"; iDestruct "Hstack" as "[Hs [H↦ [Hlist Hoffer]]]".
    steps_r; inline_r; steps_r.
    destruct (decide (stack_elem_to_val stack_rep = stack_elem_to_val stack_rep')) as [e|e].
    { (* success *)
      rewrite e.
      force_r (blk, ofs, _, 1%Qp, _, _, _, _, _, 1%Z). forces_r. iFrame "H↦". iSplitR; eauto.
      { iSplit; eauto. iSplit.
        { iPureIntro; split; first done. rewrite /stack_elem_to_val; rewrite /MemSpec.compare_val.
          des_ifs; ss. simpl_bool. des; destruct (dec _ _); ss.
          admit.
        }
        admit.
      }
      steps_r. iDestruct "GRT" as "[[-> [H↦ [? ?]]]->]". hss_r. steps_r.
      case_decide; first clarify.
      admit.
    }
    force_r (blk, ofs, _, 1%Qp, _, _, _, _, _, 0%Z). forces_r. iFrame "H↦". iSplitR; eauto.
    { iSplit; eauto. iSplit.
      { iPureIntro; split; first done. admit. }
      admit.
    }
    steps_r. iDestruct "GRT" as "[[-> [H↦ [? ?]]]->]". hss_r. steps_r.
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { rewrite /stack_inv. do 3 (SL_red; iExists _); SL_red; iFrame. }
    force_l true. steps_l. force_l. iSplitL "ASM"; eauto. steps_l.

    sch_yield_rr. case_decide; clarify. 2:{ exfalso; apply e; clarify. }
    steps_r. sch_yield_rr. steps_r.
    { iSplit; eauto. iSplit; eauto. iExists _, _; iFrame "Hinv"; eauto. }
    steps_l; unfold_lat_img_l. hss.

    destruct _q1. s. iDestruct "ASM" as "[[% [% [% #I]]] _]"; des; subst. hss.
    iInv "I" as "INV" "ACC". iEval (SL_red) in "INV".
    iDestruct "INV" as "[PT | [PT [R TKN]]]".
    { force_r (_, _, _, _, _, _, _, _, _, _). steps_r. forces_r.
      iSplitL "PT".
      { iFrame. et. }
      steps_r. iDestruct "GRT" as "[[% [↦ _]] %]"; subst. hss.
      steps_r. iMod ("ACC" with "[↦]") as "_".
      { SL_red; iFrame "↦". }
      force_l true. forces_l. iSplitL "".
      { repeat (iSplit; et). iExists _; et. }
      steps_l. unfold_lat_img_l.
      sch_yield_rr. steps_r. sch_yield_rr. steps_r.
      by_coind CIH. hss_copset. iFrame.
    }
    { force_r (_, _, _, _, _, _, _, _, _, _). steps_r. forces_r.
      iSplitL "PT".
      { iFrame. repeat (iSplit; et). }
      steps_r. iDestruct "GRT" as "[[% [↦ _]] %]"; subst. hss.
      steps_r. iMod ("ACC" with "[↦]") as "_".
      { SL_red; iFrame "↦". }
      force_l false. forces_l. iSplitL "R TKN".
      { repeat (iSplit; et). SL_red. iFrame. }
      steps_l. sch_yield_rr. steps_r. sch_yield_rr. steps_r.
      sch_yield_rr. steps_r. sch_yield_l.
      step; et.
    }      
  Unshelve. all: try exact 1%Qp; try exact (Vint 0); eauto.
  (*SLOW*)Qed.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof using SchG.
    init_simF.
    steps_l; unfold_lat_img_l.

    (* ill-formed argument *)
    destruct (classic (∃ blk ofs, arg = [Vptr (blk,ofs)]↑)); cycle 1.
    {  sch_yield_l. steps_l. destruct _q1. iDestruct "ASM" as "[[% [L _]] _]".
      subst. iDestruct "L" as "[% [% _]]". destruct bofs. subst. exfalso. et.
    }
    des; subst; hss.

    steps_r; sch_yield_rr; steps_r.
    sch_yield_l; steps_l. force_l (Vundef↑). 
    destruct _q1. s. iDestruct "ASM" as "[[% [[% [% #I]] [TKN P]]] _]". hss.
    iInv "I" as "INV" "ACC". iEval (SL_red) in "INV".
    iDestruct "INV" as "[PT | [PT [R' TKN']]]"; cycle 1.
    { SL_red. iCombine "TKN" "TKN'" gives %WF; inv WF. }
    steps_r; inline_r; steps_r.
    force_r (_,_,_,_). forces_r.
    iSplitL "PT".
    { iFrame. et. }
    steps_r. iDestruct "GRT" as "[[↦ %] %]"; hss.
    iMod ("ACC" with "[↦ TKN P]") as "_".
    { SL_red. iRight. iFrame. }
    steps_r. forces_l. iSplit; et.
    steps_l. sch_yield_rr. sch_yield_l.
    step. et.
  Unshelve. all: eauto.
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
      (SpinLockA.t ★ MemA.t, emp%I)
      (SpinLockI.t ★ MemA.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End StackIA. End StackIA.

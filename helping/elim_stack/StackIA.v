Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
From CRIS.helping Require Import Header HelpingOn HelpingOnOffproof HelpingTactics.

(* TEMP *)
From iris.algebra Require Import gmap_view.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, Hsch : !newschG, !concG, !stackG StackM.jobID StackM.retID}.
  Local Existing Instances stack_helpingG.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (msk : string → bool) (N : namespace) (sp : sp_type).
  Context (Hspsch : sp_incl (SchA.sp [] (↑N)) sp).
  Context (Hsphelp : sp_incl ([(Some (Helping.run mn), None); (Some (Helping.help mn), None)]) sp).

  (* Whitelist of functions callable in stack *)
  Definition imp := omap id (Mod.exports SchI.t ++ Mod.exports MemA.t).
  Context (Hmsk : wmask_sub (wmask_list imp) msk).

  Lemma yield_msk : wmask_and msk wmask_all SchHdr.yield.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Lemma alloc_msk : wmask_and msk wmask_all MemHdr.alloc.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; rewrite /MemA.t; unseal CRIS.
    unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Lemma store_msk : wmask_and msk wmask_all MemHdr.store.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; rewrite /MemA.t; unseal CRIS.
    unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Lemma load_msk : wmask_and msk wmask_all MemHdr.load.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; rewrite /MemA.t; unseal CRIS.
    unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Lemma cas_msk : wmask_and msk wmask_all MemHdr.cas.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; rewrite /MemA.t; unseal CRIS.
    unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Lemma cmp_msk : wmask_and msk wmask_all MemHdr.cmp.
  Proof.
    revert Hmsk; rewrite /imp /wmask_and /wmask_list /wmask_sub; rewrite /MemA.t; unseal CRIS.
    unfold_mod; ss.
    intros Hmsk; simpl_bool; apply Hmsk; eauto.
  Qed.
  Hint Resolve yield_msk alloc_msk store_msk load_msk cas_msk cmp_msk : core.

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t.
  Local Definition SchI := CFilter.filter msk SchI.t.
  Local Definition HelpingOn := HelpingOn.t mn StackM.jobCode StackM.retCode sp.
  Local Definition StackM := (StackM.t mn N sp ★ MemA) ★ HelpingOn ★ SchI.
  Local Definition StackI := CFilter.filter msk (StackI.t ★ MemA) ★ SchI.
  Local Definition IstFull :=
    (IstHelp StackM.jobID StackM.retID mn (IstProd ((IstSB (Mod.scopes StackM) IstTrue)) IstEq)).

  Let offerN := N .@ "offer".
  Let stackN := N .@ "stack".

  Lemma new_stack_simF :
    ISim.sim_fun open StackM StackI init_cond IstFull (Some StackHdr.new_stack).
  Proof using Hsch Hmsk.
    init_simF.
    steps_l. rename _q3 into stid, _q4 into mtid.
    iDestruct "ASM" as "[TID [[%v ->] ->]]". hss. 

    steps_r. sch_yield_ir.

    (* allocate new stack *)
    steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (stackb) "[↦stack [↦val _]]".
    steps_r. hss_r. steps_r. sch_yield_ir.
    steps_r. sch_yield_ir.

    (* initialize stack *)
    steps_r.
    iApply (wsim_mem_store with "↦stack");
      [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "↦stack". steps_r. hss_r.

    steps_r. sch_yield_ir.

    steps_r.
    iApply (wsim_mem_store with "↦val");
      [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
    iIntros "↦val". steps_r. hss_r.

    steps_r. sch_yield_ir.
    steps_r.

    sch_yield_l.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid_discrete. split; done. }
    iMod (inv_alloc (syn_stack_inv N γs stackb 0%Z 0) _ _ _ stackN with "[-Hs◯ IST TID]")
      as "#Hinv"; eauto.
    { apply nclose_subseteq. }
    { rewrite /syn_stack_inv /syn_is_offer SLRed_red. iExists (Vint 0), (Vint 0), []; iFrame; eauto.
      rewrite SLRed_red //.
    }

    force_l (Vptr (stackb, 0%Z)). steps_l. forces_l.
    iFrame "Hs◯ TID"; iSplit; eauto.
    { iSplit; eauto. iExists _; iSplit; eauto. iExists _, _; iSplit; eauto. }
    steps_l. step. iSplit; eauto.
  (*SLOW*)Admitted.

  Program Global Instance winv_sep_WP `{!crisG Γ Σ α β τ _S _I} E P :
    WP (winv (E, E) ∗ P) :=
    {| WP_space := E; WP_remainder := P |}.
  Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

  Lemma push_simF : ISim.sim_fun open StackM StackI init_cond IstFull (Some StackHdr.push).
  Proof using Hsch Hmsk Hspsch Hsphelp.
    init_simF.

    steps_l.
    destruct Hsphelp as [Hfind2 Hfind]; rewrite (Hfind (Helping.run mn) None) //; cycle 1.
    { rewrite /alist_find eq_rel_dec_correct /=; des_ifs. }
    clear Hfind Hfind2.
    rename _q into args, _q3 into stid, _q4 into mtid, _q6 into γs, _q7 into s, _q8 into v.
    iDestruct "ASM" as "[TID [[% #[%stackb [%stackofs [-> Hinv]]]] _]]"; hss.

    (* Register for helping *)
    steps_r. norm_l.
    iApply (wsim_helping_run with "IST");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..].
    clear st_src st_tgt; iIntros (st_src st_tgt req_id) "IST Help".

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [TID [IST Help]]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._push. steps_r.

    sch_yield_ir. steps_r.
    sch_yield_ir. steps_r.

    (* load *)
    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red.
    iDestruct "Hstack" as "[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]".

    iApply (wsim_mem_load with "[H↦]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "H↦". steps_r. hss_r. steps_r.

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { rewrite /syn_stack_inv /syn_is_offer.
      do 3 (SL_red; iExists _); SL_red; iFrame. rewrite SLRed_red //.
    }

    (* alloc new head *)
    sch_yield_ir. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (head_newb) "[Hnewv [Hnewhead _]]". steps_r. hss_r. steps_r.

    (* store to new head *)
    sch_yield_ir. steps_r. sch_yield_ir. steps_r.
    iApply (wsim_mem_store with "Hnewv");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hnewv". steps_r. hss_r. steps_r. sch_yield_ir. steps_r.
    iApply (wsim_mem_store with "Hnewhead");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hnewhead". steps_r. hss_r. steps_r.

    (* try push *)
    sch_yield_ir. steps_r.
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
      clear CIH.
      steps_r. hss_r. steps_r.

      (* atomic update happens here: since it is valid to update stack_contents here (without any
         helps from other threads), the pusher does its own job *)
      sch_yield_l. norm_l.
      iApply (wsim_helping_try_run with "Help IST").
      clear st_src; iIntros (reqmap st_src) "Help IST".
      rewrite /StackM.jobCode /=. steps_l.
      rewrite Helping.trans_take. steps_l. clear l; rename _q into l.
      rewrite Helping.trans_Assume. steps_l.
      iCombine "Hs ASM" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      rewrite Helping.trans_Guarantee. force_l. iFrame.
      rewrite Helping.trans_ret. steps_l.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[Hnewv Hnewhead Hoffer Hlist H↦ Hs]") as "_".
      { iExists _, offer_rep', (v :: l'). iFrame. iExists 1%Qp; iSplit; eauto.
        rewrite Z.add_0_l.
        destruct stack_rep, stack_rep'; inv Hcomp; des_ifs.
        simpl_bool; des; do 2 destruct (dec _ _); clarify.
      }
      iMod (IstHelp_done with "Help IST") as "[Done IST]".

      (* comparison *)
      sch_yield_ir. steps_r.
      iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". steps_r. hss_r. steps_r.

      (* epilogue *)
      sch_yield_ir. steps_r. sch_yield_l. steps_l. hss.
      force_l; iFrame "TID". iSplit; eauto.
      step.
      iFrame; done.
    }

    (* failure *)
    steps_r. hss_r. steps_r.
    iMod ("close" with "[Hnewv Hnewhead Hoffer Hlist H↦ Hs]") as "_".
    { iExists _, offer_rep', l'. iFrame. }

    (* comparison - which leads us to offering *)
    sch_yield_ir. steps_r.
    iCombine "Hval" "Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r. hss_r. steps_r.
    sch_yield_ir. steps_r.
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep', stack_rep; inv Hcomp; des_ifs. }

    (* make an offer *)
    steps_r. sch_yield_ir. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros (offerb) "[Hofferv [Hofferst _]]".
    steps_r; hss_r; steps_r.

    sch_yield_ir. steps_r.
    sch_yield_ir. steps_r.
    iApply (wsim_mem_store with "[Hofferv]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "Hofferv". steps_r. hss_r. steps_r.

    sch_yield_ir. steps_r.
    iApply (wsim_mem_store with "[Hofferst]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "Hofferst". steps_r. hss_r. steps_r.
    rewrite Z.add_0_l.

    sch_yield_ir; steps_r.
    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red. clear dependent l l' stack_rep stack_rep' offer_rep offer_rep'.
    iDestruct "Hstack" as "[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]".
    iApply (wsim_mem_store with "Hoffer↦");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hoffer↦". steps_r. hss_r.
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (inv_alloc
      (syn_offer_inv 0 γo (offerb, 0%Z) (stid, mtid, (Vptr (stackb, stackofs), v, γs)))
      _ _ _ offerN with "[Hofferv Hofferst Help]") as "#Hoinv"; eauto.
    { apply nclose_subseteq. }
    { rewrite SLRed_red; iExists _, _; iFrame. done. }

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { rewrite SLRed_red. iExists _, (Vptr (offerb, 0%Z)), l. iFrame.
      rewrite /syn_is_offer /= SLRed_red. iExists γo, _. rewrite inv_red //. }
    steps_r. sch_yield_ir. steps_r.

    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red. clear dependent l stack_rep offer_rep.
    iDestruct "Hstack" as "[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]".
    iApply (wsim_mem_store with "Hoffer↦");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hoffer↦". steps_r. hss_r.

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { rewrite SLRed_red. iExists _, _, l. iFrame. rewrite SLRed_red //. }
    steps_r. sch_yield_ir. steps_r.

    iInv "Hoinv" as "oinv" "close"; rewrite {1}SLRed_red.
    iDestruct "oinv" as "[%offerst [%rid [offerv↦ [offerst↦ offer]]]] /=".
    rewrite Z.add_0_l.
    destruct offerst; try by (iCombine "OfferTkn" "offer" gives %WF).
    destruct n; try by (iCombine "OfferTkn" "offer" gives %WF).
    { (* nobody helped*)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      des_ifs_safe. iIntros "Hofferst _". steps_r. hss_r. steps_r.

      iMod ("close" with "[offerv↦ Hofferst OfferTkn]") as "_".
      { rewrite SLRed_red. iExists _, _. iFrame. done. }

      steps_r. sch_yield_ir. steps_r.
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.

      by_coind CIH. iFrame.
      (* TODO : make request id explicit in the invariant *)
      admit.
    }
    (* Helped! *)
  (*SLOW*)Admitted.

  Lemma pop_simF : ISim.sim_fun open StackM StackI init_cond IstFull (Some StackHdr.pop).
  Proof.
    init_simF.
    steps_l. iDestruct "ASM" as "[TID [[% #[%stackb [%stackofs [-> Hinv]]]] _]]". hss.
    rename _q3 into stid, _q4 into mtid, _q6 into γs.
    steps_r.

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [TID [IST Help]]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._pop. steps_r.
    sch_yield_ir. steps_r. sch_yield_ir. steps_r.

    (* Stack load *)
    iInv "Hinv" as "Hstack" "close".
    rewrite SLRed_red.
    iDestruct "Hstack" as "[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]".

    iApply (wsim_mem_load with "[H↦]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "H↦". steps_r. hss_r. steps_r.

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sch_yield_l. steps_l.
      destruct Hsphelp as [Hfind2 Hfind]; rewrite (Hfind (Helping.help mn) None) //; cycle 1.
      { rewrite /alist_find eq_rel_dec_correct /=; des_ifs; destruct (dec _ _); ss. }
      clear Hfind Hfind2.

      iDestruct "IST" as "[% [% [-> [Help● IST]]]]".
      inline_l. steps_l. force_l (fresh (dom reqmap)). steps_l.
      rewrite /HoareCall_prologue; unseal "Help".
      unfold_sp_exact sp (SchHdr.yield); ss.
      force_l (stid, mtid). steps_l.
      force_l (()↑).
      iDestruct "Help●" as "[Help● Help●2]".
      force_l.
      admit. 
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    admit.
  Admitted.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Admitted.

  (* ctxr works as a unit in compositions of module simulations *)
  (* Lemma ctxr :
    ctx_refines
      (StackM.t N ★ MemA.t, emp%I)
      (StackI.t ★ MemA.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed. *)
End StackIM. End StackIM.

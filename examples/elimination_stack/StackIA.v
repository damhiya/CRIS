Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
From CRIS.helping Require Import Header HelpingOn HelpingOnOffproof HelpingTactics HelpingFacts.

Ltac sch_yield_ir H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  (norm_l with do 1 (iApply (wsim_yield_tgt_ir); [simpl_sp; simpl_map; ss|simpl_sp; simpl_map; ss|ss|ss|iFrame H2']));
  last (clear_st; iIntros (??) H2').

Arguments Mod.add : simpl never.
Arguments Mod.fnsems : simpl never.
Hint Extern 100 (?A !! _ = _) => rewrite /A /=; simpl_map : simpl_map.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !newschG, !concG, !stackG StackM.jobID StackM.retID}.
  Local Existing Instances stack_helpingG.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (N : namespace) (sp sp_user : specmap).
  
  Definition init_cond : iProp Σ := helping_auth 1 ∅%I.

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode (SchA.sp ∅ (↑N))).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := (SchI ★ MemA ★ StackM.t mn N ((SchA.sp ∅ (↑N))) ★ HelpingOn).
  Local Notation StackI := (SchI ★ MemA ★ CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy).

  Local Notation IstFull := (HelpingTactics.IstFull StackM.jobID StackM.retID mn).

  Lemma new_stack_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.new_stack).
  Proof using.
    iStartSim.
    steps_l. destruct _q as [[stid mtid] n]. iDestruct "ASM" as "[TID [-> [%val ->]]]".
    hss_l. hss_r. steps_l. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* allocate new stack - can't use memtactics here..., generalize the lemma *)
    steps_r.
    iApply wsim_mem_alloc; [try by simpl_map|ss|ss|].
    iIntros (blk) "[↦stack [↦val _]]". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* initialize stack *)
    steps_r. store_r "↦stack". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    steps_r. store_r "↦val". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* Guarantee the postcondition *)
    sch_yield_l.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid_discrete. split; done. }
    iMod (inv_alloc (syn_stack_inv N γs blk 0%Z n) _ _ _ (stackN N) with "[-Hs◯ IST TID]")
      as "#Hinv"; eauto.
    { solve_ndisj. }
    { solve_base_sl_red. iLeft. iExists (Vint 0), (Vint 0), []; iFrame; solve_base_sl_red; ss. }

    force_l (Vptr (blk, 0%Z)). steps_l. forces_l.
    iFrame "Hs◯ TID"; iSplit; eauto.
    { iSplit; eauto. iExists _; iSplit; eauto. iExists _, _; iSplit; eauto. }
    steps_l. step. iSplit; eauto.
  (*SLOW*)Qed.

  (* Program Global Instance winv_sep_WP `{!crisG Γ Σ α β τ _S _I} E P :
    WP (winv (E, E) ∗ P) :=
    {| WP_space := E; WP_remainder := P |}.
  Next Obligation. intros; iSplit; iIntros "[$ $]". Qed. *)

  Lemma push_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.push).
  Proof using.
    iStartSim.
    rewrite /StackM.push; steps_l. steps_r.

    rewrite /atomic_body. steps_l. destruct _q as [[stid mtid] [[[n vs] v] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]".
    hss_r. steps_r. sch_yield_l.
    step_l. rewrite {3}/SchA.sp. simpl_map. step_l.
    iApply (wsim_helping_run with "IST"); [|].
    { simpl_map. rewrite /SB.sandbox_body. s. refl. }
    clear st_src st_tgt; iIntros (st_src st_tgt req_id) "IST Tkn".

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [TID [IST Help]]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._push. steps_r.

    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    load_r "H↦". steps_r. hss_r. steps_r.

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { iLeft; iFrame. }

    (* alloc new head *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    iApply wsim_mem_alloc; [try by simpl_map|ss|ss|].
    iIntros (blkhead) "[↦head [↦offer _]]". steps_r. hss_r. steps_r.

    (* store to new head *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    store_r "↦head". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    store_r "↦offer". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* try push *)
    iInv "Hinv" as "[[%stack_rep1 [%offer_rep1 [%l1 [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp"); [prove_inline_cond|ss|eauto| | ].
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp".
    case_bool_decide; subst.
    { (* success *)
      clear CIH.
      steps_r. hss_r. steps_r.

      (* atomic update happens here: since it is valid to update stack_contents here (without any
         helps from other threads), the pusher does its own job *)
      sch_yield_l. norm_l.
      iApply (wsim_helping_pend_try_run with "Help IST [-]").
      steps_l.
      iCombine "Hs ASM" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l. iFrame. steps_l. step.
      iFrame. iSplit; eauto.

      clear_st; iIntros (st_src st_tgt) "#Done IST". steps_l.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[↦head ↦offer Hoffer Hlist H↦ Hs]") as "_".
      { iLeft. iFrame.
        destruct stack_rep, stack_rep1; inv Hcomp; try case_bool_decide; des_ifs; iFrame; eauto.
        case_bool_decide; des; clarify; iFrame; eauto.
      }

      (* comparison *)
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". steps_r. hss_r. steps_r.

      (* epilogue *)
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      sch_yield_l. steps_l. sch_yield_l.
      force_l; iFrame "TID". iSplit; eauto.
      step.
      iFrame; done.
    }

    (* failure *)
    steps_r. hss_r. steps_r.
    iMod ("close" with "[↦offer ↦head Hoffer Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. }

    (* comparison - which leads us to offering *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep1, stack_rep; inv Hcomp; des_ifs. }

    (* make an offer *)
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    iApply wsim_mem_alloc; [prove_inline_cond|ss|ss|].
    iIntros (offerb) "[↦offer [↦offerst _]]".
    steps_r; hss_r; steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    store_r "↦offer". steps_r; hss_r; steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    store_r "↦offerst". steps_r; hss_r; steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    clear dependent l l1 stack_rep stack_rep1 offer_rep offer_rep1.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    store_r "Hoffer↦". steps_r. hss_r.
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (inv_alloc
      (syn_offer_inv n γo (offerb, 0%Z) req_id (stid, mtid, (n, Vptr (stackb, stackofs), v, γs)))
      _ _ _ (offerN N) with "[↦offer ↦offerst Help]") as "#Hoinv"; eauto.
    { solve_ndisj. }
    { solve_base_sl_red; iFrame; auto. }

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. solve_base_sl_red. iExists γo, _, _. iSplit; eauto. }
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    clear dependent l stack_rep offer_rep.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }
    store_r "Hoffer↦". steps_r. hss_r. steps_r.

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft; iFrame. solve_base_sl_red. }
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    iInv "Hoinv" as "[%offerst [offerst↦ offer]] /=" "close".
    rewrite Z.add_0_l.
    case_decide; subst.
    { (* nobody helped*)
      iApply (wsim_mem_cas with "offerst↦"); [prove_inline_cond|ss|eauto| | | ].
      { instantiate (1:=emp%I); done. }
      { eauto. }
      case_bool_decide; ss. iIntros "Hofferst _". steps_r. hss_r. steps_r.

      iMod ("close" with "[Hofferst OfferTkn]") as "_".
      { iFrame. done. }

      steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.

      by_coind CIH. iDestruct "offer" as "[? ?]"; iFrame. done.
    }
    case_decide; subst.
    { (* Somebody helped *)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      case_bool_decide; ss. iIntros "Hofferst _". steps_r. hss_r. steps_r.
      iPoseProof "offer" as "#offer".

      iMod ("close" with "[Hofferst]") as "_".
      { iFrame. done. }

      steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.

      sch_yield_l. steps_l.
      iApply (wsim_helping_done_try_run with "offer IST"); eauto.
      iIntros "IST".
      sch_yield_l. steps_l. sch_yield_l. force_l. iFrame. iSplit; eauto.
      step. iFrame. eauto.
    }

    case_decide; try by (iCombine "OfferTkn" "offer" gives %WF). ss.
  Unshelve. all: try exact 1%Qp.
  (*SLOW*)Qed.

  Lemma pop_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.pop).
  Proof using.
    iStartSim.
    rewrite /StackM.pop /atomic_body.
    steps_l. destruct _q as [[stid mtid] [[n vs] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]". hss_r. steps_r.

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [IST TID]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._pop. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* Stack load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }

    load_r "H↦". steps_r. hss_r. steps_r.

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sch_yield_l. steps_l. force_l false. steps_l.

      (* Atomic update *)
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      destruct l; [|ss; iPoseProof "Hlist" as "[% [% [% [% [% [% ?]]]]]]"; clarify].
      force_l. iFrame. steps_l.

      iMod ("close" with "[Hs Hlist Hoffer H↦]") as "_".
      { iLeft. iFrame. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iSplit; done.
    }
    (* Stack nonempty *)
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".

    destruct l as [|v l]; ss; first iPoseProof "Hlist" as "%"; clarify.
    iDestruct "Hlist" as (headb headofs stackrep q0 q1) "[-> [↦v [↦next Hlist]]]".
    iDestruct "↦next" as "[↦next ↦next2]".
    iMod ("close" with "[Hs Hlist H↦ ↦v ↦next2 Hoffer]") as "_".
    { iLeft. iFrame. iExists _, _, _, _; iFrame; eauto. }

    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    load_r "↦next". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    iInv "Hinv" as "[[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp");
      [prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". steps_r. hss_r. steps_r.
    case_bool_decide; subst.
    { (* Pop success *)
      sch_yield_l. steps_l. force_l false. steps_l.
      destruct (stack_rep') as [[| |]|[bold ofsold]|]; inv Hcomp; case_bool_decide; ss.
      destruct l'; ss.
      { iPoseProof "Hlist" as "%"; ss. }
      iDestruct "Hlist" as "[% [% [% [% [% [% [Hpt1 [Hpt2 Hlist]]]]]]]]". des; clarify.
      iPoseProof (mem_points_to_singleton_agree with "↦next Hpt2") as "<-".
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs ASM]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame. steps_l.
      iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
      { iLeft. iFrame. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

      iCombine "Hval Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval");
        [try prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      { case_bool_decide; ss; exfalso; naive_solver. }
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "[[% [% Hval]] _]". steps_r. hss_r. steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

      load_r "Hval".
      iPoseProof (mem_points_to_singleton_agree with "Hval Hpt1") as "<-".
      steps_r. hss_r. steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iFrame. eauto.
    }

    (* Pop failure *)
    iMod ("close" with "[↦next Hs Hoffer Hlist H↦]") as "_".
    { iLeft. iFrame. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    iCombine "Hval Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r. hss_r. steps_r.
    assert (succ = 0%Z); last subst succ.
    { destruct stack_rep' as [[|?|?]|[? ?]|]; inv Hcomp; ss; case_bool_decide; des; clarify; ss. }
    steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* Check the offer *)
    clear dependent stack_rep' offer_rep offer_rep' l  l'.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "Hoffer" as "[↦offer Hoffer]".
    load_r "↦offer". steps_r. hss_r. steps_r.
    rewrite /syn_is_offer; destruct (offer_rep) as [[|?|?]|[offerb offerofs]|]; solve_base_sl_red;
      try iPoseProof ("Hoffer") as "%"; ss.
    { steps_r.
      iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
      { iLeft; iFrame. solve_base_sl_red. }
      by_coind CIH. iFrame. done.
    }
    iDestruct "Hoffer" as (γo [[stid' mtid'] [[[n' s'] v'] γs']] reqid) "[OfferInv <-]".
    iPoseProof ("OfferInv") as "#OfferInv".

    steps_r.
    iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
    { iLeft; iFrame. solve_base_sl_red. repeat iExists _; iSplit; eauto. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    (* Try to take the offer *)
    iInv "OfferInv" as "[%offerst [↦offerst offer]] /=" "close".

    case_decide; subst.
    { (* Helping *)
      iDestruct "offer" as "[offerv offer]".
      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "offer↦ _". iClear "E". case_decide; last done.
      steps_r. hss_r. steps_r.

      (* Help *)
      sch_yield_l. force_l true. steps_l.
      rewrite {3}/SchA.sp; simpl_map.
      inline_l. steps_l.
      iDestruct "IST" as "[% [% [% [% [[-> ->] [IST [% [% [[-> ->] ●Help]]]]]]]]]".
      iPoseProof (helping_auth_token with "●Help offer") as "%Hreq".
      iMod (helping_auth_commit with "●Help offer") as "[●offer #◯offer]".
      iMod ("close" with "[offer↦ ◯offer]") as "_".
      { iExists 1; iFrame; case_decide; ss. }
      rewrite /HelpingOn.help. force_l reqid. steps_l.
      assert (Hsp : SchA.sp ∅ (↑N) !! speckey_fn SchHdr.yield = fsp_some (SchA.yield_spec (↑N))).
      { rewrite /SchA.sp; simpl_map; ss. }
      rewrite !Hsp.
      force_l (stid, mtid, tt). forces_l. iFrame. iSplit; eauto. steps_l.
      destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".

      (* Helpee's Atomic Assume *)
      rewrite /HelpingOn.try_run. steps_l. hss_l. step_l. rewrite Hreq /=.
      steps_l.
      clear dependent stack_rep offer_rep l.
      iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "Close";
        cycle 1.
      { iExFalso. iCombine "●" "●offer" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      (* Helpee's Atomic Guarantee *)
      force_l; iFrame "Hl". steps_l.

      (* My Atomic Assume *)
      iPoseProof (helping_auth_split (1/2) with "●offer") as "[●offer ●reclaim]"; ss.
      iMod ("Close" with "[●offer]") as "_".
      { iRight; iFrame. }
      forces_l. iFrame; iSplit; eauto. steps_l.
      iDestruct "ASM" as "[TID [_ ->]]".
      iCombine "Hs ASM'" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete. ss.
      iMod (own_update_2 with "Hs ASM'") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame "Hl"; steps_l.
      iInv "Hinv" as "[[% [% [% [Hs' _]]]]|[% ●]]" "close".
      { iExFalso. iCombine "Hs" "Hs'" gives %WF; inv WF. }
      iPoseProof ("●reclaim" with "●") as "●".
      iMod ("close" with "[- IST TID ● offerv]") as "_".
      { iLeft; iFrame. }
      set (st_src := union_with _ _ _); set (st_tgt := union_with _ _ _).
      iAssert (IstFull st_src st_tgt)%I with "[● IST]" as "IST".
      { iExists _, _, _, _; iFrame. iSplit; eauto. iPureIntro; esplits; eauto; set_solver. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

      (* Compare *)
      load_r "offerv". steps_r. hss_r. steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
      sch_yield_l. forces_l. iFrame. iSplit; eauto. step. iFrame. done.
    }

    (* Failed to take the offer - repeat the whole process! *)
    iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; ss; des_ifs; ss. }
    iIntros "↦offerst _". steps_r. hss_r. steps_r.
    iMod ("close" with "[↦offerst offer]") as "_".
    { iExists _; ss; iFrame. case_decide; clarify. case_decide; eauto. case_decide; clarify. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    iApply (wsim_mem_cmp with "E");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; clarify; des_ifs; ss. }
    iIntros "_". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.

    by_coind CIH. iFrame. done.
  (*SLOW*)Qed.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Proof.
    rewrite -mod_add_assoc -(mod_add_assoc SchI).
    eapply ISim_reflL.
    { rewrite !mod_add_assoc.
      intros fn; rewrite Mod.dom_fnsems_add; set_unfold; i; des; subst.
      { apply new_stack_simF. }
      { apply push_simF. }
      { apply pop_simF. }
      { iStartSim; steps_r. steps_r; ss. }
      { iStartSim; steps_r. steps_r; ss. }
    }
    { multiset_solver. }
    { multiset_solver. }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { iIntros "I"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      { rewrite dom_union_with; set_solver. }
      { rewrite left_id_L //. }
    }
  Qed.
End StackIM. End StackIM.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !newschG, !concG, !stackG StackM.jobID StackM.retID}.

  Lemma ctxr (N : namespace) (sp sp_user : specmap) :
    SchA.sp sp_user (↑N) ⊆ sp →
    ctx_refines
      (StackA.t N sp ★ MemA.t sp ★ SchI.t, StackIM.init_cond)
      (StackI.t      ★ MemA.t sp ★ SchI.t, emp%I).
  Proof.
    intros Hsp.
    etrans; first eapply ctxr_cond_strengthen.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main with (mM:=λ mn, StackM.t mn N ((SchA.sp ∅ (↑N)))).
    { intros mn.
      rewrite ?CFilter.filter_app ?mod_add_assoc.
      ctxr_swap. ctxr_rotate. ctxr_swap. do 3 ctxr_rotate. ctxr_swap.
      etrans; cycle 1.
      { eapply main_adequacy, StackIM.sim with (mn:=mn) (N:=N). }
      etrans; cycle 1.
      { do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_swap. do 2 ctxr_drop. refl. }
      rewrite left_id. refl.
    }
    intros mn.
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_refl. }

    rewrite -mod_add_assoc.
    eapply main_adequacy with (Ist := IstProd (IstSB (Mod.scopes (StackA.t N sp) ∪ {[+mn+]}) IstTrue) IstEq).
    init_sim.
    { iStartSim.
      steps_l. force_r _q. destruct _q as [[? ?] ?]; iDestruct "ASM" as "[? [-> [% ->]]]".
      forces_r. iFrame; iSplit; eauto.
      steps_r. hss_l; hss_r. steps_l; steps_r.
      sch_yield_ii "IST". sch_yield_l.
      steps_r; forces_l. iFrame; step. iFrame. done.
    }
    { iStartSim.
      rewrite /StackA.push /StackM.push /atomic_body.
      steps_l. steps_r. forces_r. iFrame "ASM". repeat case_match; clarify.
      steps_r. steps_l.
      sch_yield_ii "IST".
      steps_r. rewrite /SchA.sp; simpl_map.
      inline_r. rewrite /HelpingOff.HelpingOff.run. steps_r. hss_r. steps_r.
      sch_yield_ii "IST". sch_yield_l.
      steps_l. forces_r; iFrame. steps_r. forces_l. iFrame.
      steps_l. sch_yield_ii "IST". steps_r. 
      sch_yield_ii "IST". steps_r. 
      sch_yield_l; force_l; iFrame.
      step. iFrame. done.
    }
    { iStartSim.
      rewrite /StackA.pop /StackM.pop /atomic_body.
      steps_l. steps_r. forces_r. iFrame "ASM". repeat case_match; clarify.
      steps_r. steps_l.
      sch_yield_ii "IST".
      set (IstFull := IstProd _ _).
      steps_r. iApply wsim_bind; iSplitL.
      { instantiate (1:=λ x y, IstFull x.1 y.1).
        add_ret_l. case_match.
        { steps_r. rewrite /SchA.sp; simpl_map. inline_r.
          rewrite /HelpingOff.HelpingOff.help. steps_r.
          sch_yield_ii "IST". steps_r. sch_yield_l. step. iFrame.
        }
        { steps_r. sch_yield_l. step. iFrame. }
      }
      clear_st. iIntros (st_src [] st_tgt ?) "IST /=".
      steps_l. forces_r; iFrame. steps_r. forces_l. iFrame.
      steps_l. sch_yield_ii "IST". steps_r. 
      sch_yield_l; force_l; iFrame.
      step. iFrame. done.
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End StackIA. End StackIA.

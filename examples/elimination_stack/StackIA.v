Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
From CRIS.helping Require Import Header HelpingOn HelpingOnOffproof HelpingTactics HelpingFacts.

Ltac sch_yield_ir H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  (norm_l with do 1 (iApply (wsim_yield_tgt_ir); [simpl_map; simpl_sp; ss|simpl_map; simpl_sp; ss|ss|ss|iFrame H2']));
  last (clear_st; iIntros (??) H2').

Ltac unfold_fnsem :=
  rewrite /Mod.fnsems /=;
  match goal with | [|-context[?x]] => 
    match type of x with fnsemmap =>
      rewrite {1}/x /=
    end
  end.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !newschG, !concG, !stackG StackM.jobID StackM.retID}.
  Local Existing Instances stack_helpingG.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (N : namespace) (sp sp_user : specmap).
  Context (Hspsch : SchA.sp sp_user (↑N) ⊆ sp).
  (* Context (Hsphelp : {[ Some (Helping.run mn) := None; Some (Helping.help mn) := None ]} ⊆ sp). *)

  (* Whitelist of functions callable in stack *)
  (* Definition imp := omap id (Mod.exports SchI.t ++ Mod.exports (MemA.t sp_none)).
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
  Hint Resolve yield_msk alloc_msk store_msk load_msk cas_msk cmp_msk : core. *)

  Definition init_cond : iProp Σ := helping_auth 1 ∅%I.

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode sp).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := (SchI ★ MemA ★ StackM.t mn N (delete (speckey_fn (Helping.run mn)) sp) ★ HelpingOn).
  Local Notation StackI := (SchI ★ MemA ★ CFilter.filter (Helping.exports mn) StackI.t ★ HelpingOn).

  Local Notation IstFull := (HelpingTactics.IstFull StackM.jobID StackM.retID mn).
  (* IstProd IstEq (IstSB {[+mn+]} (IstHelp mn)). *)

  Lemma lookup_fnsems_l2 (m1 m2 : Mod.t) (k : option string) v :
    (Mod.fnsems m1) !! k = None →
    (Mod.fnsems m2) !! k = Some v →
    (Mod.fnsems (m1 ★ m2)) !! k = Some v.
  Proof. rewrite lookup_union_with => -> -> //. Qed.

  Lemma lookup_fnsems_r2 (m1 m2 : Mod.t) (k : option string) v :
    (Mod.fnsems m1) !! k = Some v →
    (Mod.fnsems m2) !! k = None →
    (Mod.fnsems (m1 ★ m2)) !! k = Some v.
  Proof. rewrite lookup_union_with => -> -> //. Qed.

  Lemma lookup_fnsems_None (m1 m2 : Mod.t) (k : option string) :
    (Mod.fnsems m1) !! k = None →
    (Mod.fnsems m2) !! k = None →
    (Mod.fnsems (m1 ★ m2)) !! k = None.
  Proof. rewrite lookup_union_with => -> -> //. Qed.

  Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = Some _) => eapply lookup_fnsems_l2 : simpl_map.
  Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = Some _) => eapply lookup_fnsems_r2 : simpl_map.
  Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = None) => eapply lookup_fnsems_None : simpl_map.
  Hint Extern 81 (Mod.fnsems _ !! _ = Some _) => unfold_fnsem; simpl_map : simpl_map.
  Hint Extern 81 (Mod.fnsems _ !! _ = None) => unfold_fnsem; simpl_map : simpl_map.

  Arguments Mod.add : simpl never.
  Arguments Mod.fnsems : simpl never.
  Lemma new_stack_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.new_stack).
  Proof using Hspsch.
    iStartSim.
    steps_l. destruct _q as [[stid mtid] n]. iDestruct "ASM" as "[TID [-> [%val ->]]]".
    hss_l. hss_r. steps_l. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* allocate new stack - can't use memtactics here..., generalize the lemma *)
    steps_r. inline_r. force_r 2. forces_r. iSplit; first eauto. steps_r.
    iDestruct "GRT" as "[-> [%blk [-> [↦stack [↦val _]]]]]". hss_r; steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* initialize stack *)
    steps_r.
    inline_r. force_r (blk, 0%Z, _, _). forces_r. iFrame "↦stack". iSplit; first eauto. steps_r.
    iDestruct "GRT" as "[-> [↦stack ->]]". hss_r; steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    steps_r.
    inline_r. force_r (blk, 1%Z, _, _). forces_r. iFrame "↦val". iSplit; first eauto. steps_r.
    iDestruct "GRT" as "[-> [↦val ->]]". hss_r; steps_r.
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

  Program Global Instance winv_sep_WP `{!crisG Γ Σ α β τ _S _I} E P :
    WP (winv (E, E) ∗ P) :=
    {| WP_space := E; WP_remainder := P |}.
  Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

  Lemma push_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.push).
  Proof using.
    iStartSim.
    rewrite /StackM.push; steps_l. steps_r.

    rewrite /atomic_body. steps_l. destruct _q as [[stid mtid] [[[n vs] v] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]".
    hss_r. steps_r. sch_yield_l.
    step_l. simpl_map; simpl_sp. step_l.
    iApply (wsim_helping_run with "IST"); eauto; [prove_inline_cond|].
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

    iApply (wsim_mem_load with "[H↦]");
      [try prove_inline_cond|try prove_sb_cond|ss].
    (* TODO : Make memtactics more flexible *)
    iIntros "H↦". steps_r. hss_r. steps_r.

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { rewrite /syn_stack_inv. SL_red; iLeft.
      do 3 (iExists _; SL_red). SL_red; iFrame. rewrite SLRed_red //.
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
    iDestruct "Hstack" as "[[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso.
      iDestruct "IST" as "[% [% [% [% [[-> ->] [-> [% [% [[-> ->] ●Help]]]]]]]]]".
      iCombine "●" "●Help" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
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
      iApply (wsim_helping_pend_try_run with "Help IST [-]").
      rewrite Helping.trans_take. steps_l.
      rewrite Helping.trans_Assume. steps_l.
      iCombine "Hs ASM" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      rewrite Helping.trans_Guarantee. force_l. iFrame.
      rewrite Helping.trans_ret. steps_l. iApply wsim_unfold; iIntros "W"; step.
      iFrame. iSplit; eauto.

      clear st_src st_tgt; iIntros (st_src st_tgt) "#Done IST". steps_l.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[Hnewv Hnewhead Hoffer Hlist H↦ Hs]") as "_".
      { iLeft. iExists _, offer_rep', (v :: l'). iFrame. iExists 1%Qp; iSplit; eauto.
        rewrite Z.add_0_l.
        destruct stack_rep, stack_rep'; inv Hcomp; des_ifs.
        simpl_bool; des; do 2 destruct (dec _ _); clarify.
      }

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
    { iLeft. iExists _, offer_rep', l'. iFrame. }

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
    iDestruct "Hstack" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }

    iApply (wsim_mem_store with "Hoffer↦");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hoffer↦". steps_r. hss_r.
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (inv_alloc
      (syn_offer_inv n γo (offerb, 0%Z) req_id (stid, mtid, (n, Vptr (stackb, stackofs), v, γs)))
      _ _ _ (offerN N) with "[Hofferv Hofferst Help]") as "#Hoinv"; eauto.
    { apply nclose_subseteq. }
    { rewrite SLRed_red; iExists _; iFrame. done. }

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { rewrite SLRed_red. iLeft. iExists _, (Vptr (offerb, 0%Z)), l. iFrame.
      rewrite /syn_is_offer /= SLRed_red. iExists γo, _, _. rewrite inv_red; iSplit; eauto.
    }
    steps_r. sch_yield_ir. steps_r.

    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red. clear dependent l stack_rep offer_rep.
    iDestruct "Hstack" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iApply (wsim_mem_store with "Hoffer↦");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].
    iIntros "Hoffer↦". steps_r. hss_r.

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { rewrite SLRed_red. iLeft. iExists _, _, l. iFrame. rewrite SLRed_red //. }
    steps_r. sch_yield_ir. steps_r.

    iInv "Hoinv" as "oinv" "close"; rewrite {1}SLRed_red.
    iDestruct "oinv" as "[%offerst [offerst↦ offer]] /=".
    rewrite Z.add_0_l.
    case_decide; subst.
    { (* nobody helped*)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      des_ifs_safe. iIntros "Hofferst _". steps_r. hss_r. steps_r.

      iMod ("close" with "[Hofferst OfferTkn]") as "_".
      { rewrite SLRed_red. iExists _. iFrame. done. }

      steps_r. sch_yield_ir. steps_r.
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.

      by_coind CIH. iDestruct "offer" as "[? ?]"; iFrame. done.
    }
    case_decide; subst.
    { (* Somebody helped *)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      des_ifs_safe. iIntros "Hofferst _". steps_r. hss_r. steps_r.
      iPoseProof "offer" as "#offer".

      iMod ("close" with "[Hofferst]") as "_".
      { rewrite SLRed_red. iExists _. iFrame. done. }

      sch_yield_ir. steps_r.
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r.

      sch_yield_l. steps_l.
      iApply (wsim_helping_done_try_run with "offer IST"); eauto.
      iIntros "IST".
      sch_yield_l. steps_l. force_l. hss. iFrame. iSplit; eauto.
      step. iFrame. eauto.
    }

    case_decide; try by (iCombine "OfferTkn" "offer" gives %WF). ss.
  Unshelve. all: try exact 1%Qp.
  (*SLOW*)Qed.

  Lemma pop_simF : ISim.sim_fun open StackM StackI init_cond IstFull (Some StackHdr.pop).
  Proof using Hsch Hmsk Hspsch Hsphelp.
    init_simF.
    steps_l. iDestruct "ASM" as "[TID [[% #[%stackb [%stackofs [-> Hinv]]]] _]]". hss.
    rename _q2 into stid, _q3 into mtid, _q5 into γs, _q6 into n.
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
    rewrite {1}SLRed_red.
    iDestruct "Hstack" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }

    iApply (wsim_mem_load with "[H↦]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    iIntros "H↦". steps_r. hss_r. steps_r.

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sch_yield_l. steps_l. force_l false. steps_l.

      (* Atomic update *)
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      destruct l; [|ss; iPoseProof "Hlist" as "[% [% [% [% [% [% ?]]]]]]"; clarify].
      force_l. iFrame. steps_l.

      iMod ("close" with "[Hs Hlist Hoffer H↦]") as "_".
      { rewrite /syn_stack_inv SLRed_red. SL_red; iLeft.
        do 3 (iExists _; SL_red). SL_red; iFrame. rewrite SLRed_red //.
      }
      sch_yield_ir. steps_r. sch_yield_l. force_l. iFrame. iSplit; eauto. step. iSplit; done.
    }
    (* Stack nonempty *)
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".

    destruct l as [|v l]; ss; first iPoseProof "Hlist" as "%"; clarify.
    iDestruct "Hlist" as (headb headofs stackrep q0 q1) "[-> [↦v [↦next Hlist]]]".
    iDestruct "↦next" as "[↦next ↦next2]".
    iMod ("close" with "[Hs Hlist H↦ ↦v ↦next2 Hoffer]") as "_".
    { rewrite /syn_stack_inv. SL_red; iLeft.
      do 3 (iExists _; SL_red). SL_red; iFrame. rewrite SLRed_red //=.
      iExists _, _, _, _; iFrame; eauto.
    }

    sch_yield_ir. steps_r. sch_yield_ir. steps_r.
    iApply (wsim_mem_load with "[↦next]");
      [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs]; eauto.
    iIntros "↦next". steps_r. hss_r. steps_r. sch_yield_ir. steps_r.

    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red.
    iDestruct "Hstack" as "[[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". steps_r. hss_r. steps_r.
    case_decide; subst.
    { (* Pop success *)
      sch_yield_l. steps_l. force_l false. steps_l.
      destruct (stack_rep') as [[| |]|[bold ofsold]|]; inv Hcomp; do 2 destruct (dec _ _); ss.
      destruct l'; ss.
      { iPoseProof "Hlist" as "%"; ss. }
      iDestruct "Hlist" as "[% [% [% [% [% [% [Hpt1 [Hpt2 Hlist]]]]]]]]". clarify.
      iPoseProof (mem_points_to_singleton_agree with "↦next Hpt2") as "<-".
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs ASM]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame. steps_l.
      iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
      { rewrite (SLRed_red (f := syn_stack_inv _ _ _ _ _)). iLeft. iFrame. }
      sch_yield_ir. steps_r.

      iCombine "Hval Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      { do 2 destruct (dec _ _); ss. }
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "[[% [% Hval]] _]". steps_r. hss_r. steps_r. sch_yield_ir. steps_r.
      iApply (wsim_mem_load with "[Hval]");
        [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
      iIntros "[Hpt3 _]".
      iPoseProof (mem_points_to_singleton_agree with "Hpt3 Hpt1") as "<-".
      steps_r. hss_r. steps_r. sch_yield_ir. steps_r.
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iFrame. eauto.
    }

    (* Pop failure *)
    iMod ("close" with "[↦next Hs Hoffer Hlist H↦]") as "_".
    { rewrite (SLRed_red (f:=syn_stack_inv _ _ _ _ _)). iLeft. iFrame. }
    sch_yield_ir. steps_r.
    iCombine "Hval Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r. hss_r. steps_r.
    assert (succ = 0%Z); last subst succ.
    { destruct stack_rep' as [[|?|?]|[? ?]|]; inv Hcomp; ss; do 2 destruct (dec _ _); ss; clarify. }
    steps_r. sch_yield_ir. steps_r.

    (* Check the offer *)
    iInv "Hinv" as "Hstack" "close".
    rewrite {1}SLRed_red. clear dependent stack_rep' offer_rep offer_rep' l  l'.
    iDestruct "Hstack" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "Hoffer" as "[↦offer Hoffer]".
    iApply (wsim_mem_load with "↦offer");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    iIntros "↦offer". steps_r. hss_r. steps_r.
    rewrite /syn_is_offer; destruct (offer_rep) as [[|?|?]|[offerb offerofs]|]; rewrite SLRed_red;
      try iPoseProof ("Hoffer") as "%"; ss.
    { steps_r.
      iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
      { rewrite (SLRed_red (f:=syn_stack_inv _ _ _ _ _)). iLeft; iFrame.
        rewrite /syn_is_offer SLRed_red //.
      }
      by_coind CIH. iFrame. done.
    }
    iDestruct "Hoffer" as (γo [[stid' mtid'] [[[n' s'] v'] γs']] reqid) "OfferInv"; rewrite inv_red.
    iPoseProof ("OfferInv") as "#OfferInv".

    steps_r.
    iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
    { rewrite (SLRed_red (f:=syn_stack_inv _ _ _ _ _)). iLeft; iFrame.
      rewrite /syn_is_offer SLRed_red //.
      iExists _, _, _; rewrite inv_red //.
    }
    sch_yield_ir. steps_r.

    (* Try to take the offer *)
    iDestruct "OfferInv" as "[OfferInv <-]"; ss. rename γs' into γs.
    iInv "OfferInv" as "inv" "close"; rewrite SLRed_red.
    iDestruct "inv" as "[%offerst [↦offerst offer]] /=".

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
      iDestruct "IST" as "[% [% [% [% [[-> ->] [IST [% [% [[-> ->] ●Help]]]]]]]]]".
      iPoseProof (helping_auth_token with "●Help offer") as "%Hreq".
      iMod (helping_auth_commit with "●Help offer") as "[●offer #◯offer]".
      iMod ("close" with "[offer↦ ◯offer]") as "_".
      { iExists 1; iFrame; case_decide; ss. }
      destruct Hsphelp as [Hfind2 Hfind]; rewrite (Hfind (Helping.help mn) None) //; cycle 1.
      { rewrite /alist_find eq_rel_dec_correct /=; des_ifs. destruct (dec _ _); ss. }
      clear Hfind Hfind2.
      inline_l. steps_l. force_l reqid. steps_l.
      rewrite /HoareCall_prologue; unseal "Help"; unfold_sp_exact sp SchHdr.yield; ss.
      force_l (stid, mtid). forces_l. iFrame. iSplit; eauto. steps_l.

      (* Helpee's Atomic Assume *)
      rewrite /HoareFun_prologue; unseal "Help"; unfold_sp_exact sp SchHdr.yield; ss.
      steps_l. rename _q1 into stid2, _q2 into mtid2.
      rewrite /HelpingOn.try_run. steps_l. hss. rewrite Hreq /=.
      steps_l. rewrite Helping.trans_take. steps_l. clear dependent l. rename _q1 into l'. 
      steps_l. rewrite Helping.trans_Assume. steps_l.
      iInv "Hinv" as "StackInv" "Close". rewrite {1}SLRed_red.
      clear dependent stack_rep offer_rep.
      iDestruct "StackInv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]";
        cycle 1.
      { iExFalso. iCombine "●" "●offer" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
      iCombine "Hs ASM'" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM'") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      (* Helpee's Atomic Guarantee *)
      rewrite Helping.trans_Guarantee; force_l; iFrame "Hl". steps_l.
      rewrite Helping.trans_ret; steps_l.

      (* My Atomic Assume *)
      iPoseProof (helping_auth_split (1/2) with "●offer") as "[●offer ●reclaim]"; ss.
      iMod ("Close" with "[●offer]") as "_".
      { rewrite SLRed_red; iRight; iFrame. }
      rewrite /HoareFun_epilogue; unseal "Help"; unfold_sp_exact sp SchHdr.yield; ss.
      forces_l. iDestruct "ASM"  as "[[_ $] _]"; iSplit; eauto. steps_l.
      rewrite /HoareCall_epilogue; unseal "Help"; unfold_sp_exact sp SchHdr.yield; ss.
      steps_l. hss.
      iCombine "Hs ASM'" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete. ss.
      iMod (own_update_2 with "Hs ASM'") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame "Hl"; steps_l.
      iInv "Hinv" as "Hstack" "close".
      rewrite (SLRed_red (f:=syn_stack_inv _ _ _ _ _)).
      iDestruct "Hstack" as "[[% [% [% [Hs' _]]]]|[% ●]]".
      { iExFalso. iCombine "Hs" "Hs'" gives %WF; inv WF. }
      iPoseProof ("●reclaim" with "●") as "●".
      iMod ("close" with "[- IST ASM ● offerv]") as "_".
      { rewrite SLRed_red; iLeft; iFrame. }
      set (st_src := st_srcL ++ _); set (st_tgt := st_tgtL ++ _).
      iAssert (IstFull st_src st_tgt)%I with "[● IST]" as "IST".
      { iExists _, _, _, _; iFrame. iSplit; eauto. }
      sch_yield_ir. iDestruct "ASM" as "[[_ $] _]".
      clear st_src st_tgt; iIntros (st_src st_tgt) "IST TID". steps_r.

      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r. hss_r. steps_r. sch_yield_ir. steps_r. sch_yield_ir. steps_r.

      (* Compare *)
      iApply (wsim_mem_load with "[offerv]");
        [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
      iIntros "offerv". steps_r. hss_r. steps_r.
      sch_yield_ir. steps_r. sch_yield_l. forces_l. iFrame. iSplit; eauto. step. iFrame. done.
    }

    (* Failed to take the offer - repeat the whole process! *)
    iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "↦offerst");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). destruct (dec _ _); clarify. des_ifs; ss. }
    iIntros "↦offerst _". steps_r. hss_r. steps_r.
    iMod ("close" with "[↦offerst offer]") as "_".
    { iExists _; ss; iFrame. case_decide; clarify. case_decide; eauto. case_decide; clarify. }
    sch_yield_ir. steps_r.

    iAssert (emp)%I with "[]" as "E"; first done.
    iApply (wsim_mem_cmp with "E");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). destruct (dec _ _); clarify. des_ifs; ss. }
    iIntros "_". steps_r. hss_r. steps_r. sch_yield_ir. steps_r.

    by_coind CIH. iFrame. done.
  (*SLOW*)Qed.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Proof.
    rewrite /StackM /StackI -mod_add_assoc -(mod_add_assoc SchI).
    eapply ISim_reflL.
    { hrepeat do 1 unfold_mod; ss. }
    { try prove_sub_perm. }
    { try prove_sub_perm. }
    { r; (hrepeat do 1 unfold_mod; s); i; ss. split; ss.
      iIntros "I"; iSplit; first (ss; iPureIntro; split; try refl; try apply incl_nil_l).
      iFrame. iSplit; eauto.
    }
    { rewrite ?mod_add_assoc.
      try unfold_mod_fn; i; des; subst; ss.
      { apply new_stack_simF. }
      { apply push_simF. }
      { apply pop_simF. }
      { rewrite /HelpingOn in H1; revert H1.
        do 2 unfold_mod; ss; i; des; clarify.
        { init_simF; steps_r; ss. }
        { init_simF; steps_r; ss. }
      }
    }
  Qed.
End StackIM. End StackIM.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !newschG, !concG, !stackG StackM.jobID StackM.retID}.

  Definition sp_m N mn : sp_type :=
    to_sp (SchA.sp [] (↑N) ++ [(Some (Helping.run mn), None); (Some (Helping.help mn), None)]).

  Lemma ctxr (N : namespace) (sp : sp_type) :
    sp_incl (SchA.sp [] (↑N)) sp →
    ctx_refines
      (StackA.t N sp ★ MemA.t sp_none ★ SchI.t , StackIM.init_cond)
      (StackI.t      ★ MemA.t sp_none ★ SchI.t, emp%I).
  Proof.
    intros Hsp.
    etrans; first eapply ctxr_cond_strengthen.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main with
      (imp:=StackIM.imp) (mM:=λ mn, StackM.t mn N (sp_m N mn)).
    { intros mn msk Hmn Hmsk.
      rewrite ?CFilter.filter_app ?mod_add_assoc.
      ctxr_swap. ctxr_rotate. ctxr_swap. do 3 ctxr_rotate. ctxr_swap.
      etrans; cycle 1.
      { eapply main_adequacy, StackIM.sim with (mn:=mn) (msk:=msk) (N:=N); cycle 3.
        { instantiate (1:=(sp_m N mn)).
          rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
          intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
        }
        { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
          intros ?? [?|[?|?]%in_inv]%alist_find_some%in_inv; clarify.
          { rewrite /alist_find /=; destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply _spawn_run_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply spawn_run_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply yield_run_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply join_run_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply get_tid_run_neq; eauto. }
            destruct (dec _ _); ss.
          }
          { rewrite /alist_find /=; destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply _spawn_help_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply spawn_help_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply yield_help_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply join_help_neq; eauto. }
            destruct (dec _ _); ss; clarify; eauto.
            { exfalso; eapply get_tid_help_neq; eauto. }
            repeat destruct (dec _ _); ss.
          }
        }
        ss.
      }
      rewrite /StackIM.StackM /StackIM.HelpingOn.
      do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_swap. do 2 ctxr_drop. ctxr_refl.
    }
    intros mn msk Hmn Hmsk.
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_refl. }

    rewrite -mod_add_assoc.
    eapply main_adequacy with (Ist := IstProd (IstSB (Mod.scopes (StackA.t N sp) ++ [mn]) IstTrue) IstEq).
    init_sim.
    { split; ss. iIntros "_"; iSplit; ss; eauto using incl_nil_l. }
    { init_simF.
      steps_l. force_r (_q3, _q4, _). forces_r. iFrame "ASM". hss. steps_r.
      sch_yield_ii. 2:{ rewrite right_id //. }
      { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
        intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      }
      { set_solver. }
      steps_r. sch_yield_l. forces_l. iFrame. step; iFrame; done.
    }
    { init_simF.
      steps_l. steps_r. force_r (_q2, _q3, (_, _, _q7, _)). forces_r. iFrame "ASM". hss. steps_r.
      rewrite /sp_m /to_sp /SchA.sp; unseal CRIS.
      rewrite /alist_find /=; destruct (dec _ _); ss; clarify; eauto.
      { exfalso; eapply _spawn_run_neq; eauto. }
      destruct (dec _ _); ss; clarify; eauto.
      { exfalso; eapply spawn_run_neq; eauto. }
      destruct (dec _ _); ss; clarify; eauto.
      { exfalso; eapply yield_run_neq; eauto. }
      destruct (dec _ _); ss; clarify; eauto.
      { exfalso; eapply join_run_neq; eauto. }
      destruct (dec _ _); ss; clarify; eauto.
      { exfalso; eapply get_tid_run_neq; eauto. }
      destruct (dec _ _); ss.
      inline_r.
      rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      steps_r. hss_r. steps_r.
      sch_yield_ii. 2:{ rewrite right_id //. }
      { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
        intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      }
      { set_solver. }
      steps_r. sch_yield_l. steps_l.
      rewrite Helping.trans_take. force_r. steps_r.
      rewrite Helping.trans_Assume. force_r. iFrame. steps_r.
      rewrite Helping.trans_Guarantee. steps_r. force_l. iFrame. steps_l.
      rewrite Helping.trans_ret. steps_r. sch_yield_ii.
       2:{ rewrite right_id //. }
      { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
        intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      }
      { set_solver. }
      steps_r. sch_yield_l. force_l. iFrame. step. iSplit; eauto.
      Unshelve. all: eauto.
    }
    { init_simF.
      steps_l. steps_r. force_r (_q2, _q3, (_, _, _)). forces_r. iFrame "ASM". hss. steps_r.
      sch_yield_ii. 2:{ rewrite right_id //. }
      { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
        intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      }
      { set_solver. }
      steps_r. iApply (wsim_bind).
      instantiate (1:=λ '(st_s, r_s) '(st_t, r_t), IstProd _ _ st_s st_t).
      iSplitL "IST".
      { destruct _q; ss.
        { steps_r.
          rewrite /sp_m /to_sp /SchA.sp; unseal CRIS.
          rewrite /alist_find /=; destruct (dec _ _); ss; clarify; eauto.
          { exfalso; eapply _spawn_help_neq; eauto. }
          destruct (dec _ _); ss; clarify; eauto.
          { exfalso; eapply spawn_help_neq; eauto. }
          destruct (dec _ _); ss; clarify; eauto.
          { exfalso; eapply yield_help_neq; eauto. }
          destruct (dec _ _); ss; clarify; eauto.
          { exfalso; eapply join_help_neq; eauto. }
          destruct (dec _ _); ss; clarify; eauto.
          { exfalso; eapply get_tid_help_neq; eauto. }
          destruct (dec _ _); ss.
          { exfalso; revert e; rewrite /Helping.help /Helping.run; i; clarify.
            eapply string_app_inv in H3; clarify.
          }
          destruct (dec _ _); ss.
          inline_r. steps_r.
          erewrite <-(bind_ret_r (SB.sandbox _ _ _ _)).
          sch_yield_ii. 2:{ rewrite right_id //. }
          { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
            intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
          }
          { set_solver. }
          steps_r. sch_yield_l. step. iFrame.
        }
        { steps_l. erewrite <-(bind_ret_r (SB.sandbox _ _ _ _)). sch_yield_l. step. iFrame. }
      }
      clear_st. iIntros (st_s _ st_t _) "IST".
      steps_l. forces_r; iFrame. steps_r; force_l. iFrame.
      steps_l.
      sch_yield_ii. 2:{ rewrite right_id //. }
      { rewrite /sp_m /to_sp /SchA.sp; unseal CRIS; split; first prove_nodup.
        intros ??; rewrite /alist_find ?eq_rel_dec_correct; des_ifs; i; clarify.
      }
      { set_solver. }
      steps_r. sch_yield_l. forces_l. iFrame. step. iFrame. done.
    }
  Unshelve. all: eauto.
  Qed.
End StackIA. End StackIA.

Require Import CRIS.
Require Import SchHeader SchA RRSHeader RRSI RRSA.
From iris.algebra Require Import gmap_view frac_auth.

Local Open Scope nat_scope.

Module RRSIA. Section RRSIA.
  Import RRSAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_concG: !concG}.
  Context `{_rrsG: !RRSA.rrsG}.

  Context (sp: sp_type).
  Context (sp_sch_user sp_rrs_user: spl_type).
  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (SchInSp : sp parent_yield = Some parent_yield_fsp).
  Context (RRSInSp : sp_incl (RRSAS.sp sp_rrs_user ⊤ get_stid PYIP) sp).
  Context (FunInSchSp : sp_incl sp_sch_user sp).
  Context (FunInRrsSp : spl_sub sp_rrs_user sp_sch_user).
  Context (YieldSpec :
              fspec_imply' parent_yield_fsp
                (fspec_winv ⊤
                   (fspec_simple (λ x,
                        ((λ varg, TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜varg = tt↑⌝),
                         (λ vret, TID (get_stid x) ∗ YIELD (get_stid x)∗ PYIP x ∗ ⌜vret = tt↑⌝))%I)))).

  (**************************)

  Definition Ist_init (rrinvO: gmap nat InvO) : iProp Σ := ⌜rrinvO = ∅⌝ ∗ rrinv ∅ ∗ own base_γ (gmap_view_auth (DfracOwn 1) ∅ : pubRA).
  Definition Ist_private (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) (Inv: InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>> ∧ <<LKUP: rrinvO !! (pred_rr tid (size rrinvO)) = Some Inv>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv_admin rrinvO ∗ ⟦ projT2 Inv ⟧ ∗ YIELD ssch ∗ Control ∗ Shot ssch ∗
    PublicAuth ths None.
  Definition Ist_public (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv rrinvO ∗ YIELD ssch ∗ Shot ssch ∗
    PublicAuth ths (Some tid).
  Definition Ist_global_in (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, YIELD e) ∗ 
    rrinv rrinvO ∗ own base_γ (gmap_view_frag tid (DfracOwn (1/2)%Qp) (to_agree stid)) ∗
    Shot ssch ∗ PublicAuth ths None.
  Definition Ist_global_out (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv rrinvO ∗ own base_γ (gmap_view_frag tid (DfracOwn (1/2)%Qp) (to_agree stid)) ∗
    YIELD ssch ∗ Shot ssch ∗ PublicAuth ths None.

  Definition Ist: alist key Any.t → alist key Any.t → iProp Σ :=
    λ st_src st_tgt,
      (∃ (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) (Inv: InvO),
          ⌜st_tgt = [(RRSI.v_ths, ths↑); (RRSI.v_tid, tid↑); (RRSI.v_sch, ssch↑)]
          ∧ st_src = st_tgt ∧ <<INVWF: size rrinvO = length ths>>⌝ ∗
          TidAuth (list_to_map (imap pair ths)) ∗
          (Ist_init rrinvO
           ∨ Ist_private ths tid stid ssch rrinvO Inv
           ∨ Ist_public ths tid stid ssch rrinvO
           ∨ Ist_global_in ths tid stid ssch rrinvO
           ∨ Ist_global_out ths tid stid ssch rrinvO))%I.

  Local Definition RRSAMod := RRSA.t parent_yield sp sp_rrs_user get_stid PYIP.
  Local Definition RRSIMod := RRSI.t parent_yield.

  Lemma simF_init : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr.init).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l. iDestruct "ASM" as "[% [-> (% & % & Tsch & Ysch & [RRI [P C]] & PRE & PYIP)]]"; des; hss.
    rename _q3 into x, _q4 into pre, _q2 into Inv.
    steps_r. steps_l. hss. steps_l. steps_r.

    (* Get Tid from parent scheduler *)
    force_l (get_stid x). steps_l. forces_l; iFrame. steps_l.
    rewrite /SModTr.NativeGetTid. steps_r. step. steps_l.
    iDestruct "ASM" as "[-> Tsch]". steps_r.

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 1.
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF & Ysch' & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    iDestruct "IST_init" as "(% & RRIA & PubA)"; subst.
    rewrite map_size_empty in INVWF. destruct ths; ss.

    steps_r. steps_l. rewrite Any.upcast_downcast. steps_r. steps_l.
    force_l (false, 0, pre). steps_l. forces_l. steps_l.
    spawn. iIntros (stid_0).

    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".
    iPoseProof (rrinv_admin_alloc ∅ Inv with "RRIA") as ">RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".

    iMod (own_update with "PubA") as "[PubA PubF]".
    { eapply (gmap_view_alloc _ None (DfracOwn 1) (to_agree false)); ss. }
    iMod (own_update with "PubA") as "[PubA PubF']".
    { eapply (gmap_view_alloc _ (Some 0) (DfracOwn 1) (to_agree false)); ss. }
    
    iMod (own_update with "TidA") as "[TidA TidF]".
    { etrans; first eapply (gmap_view_alloc _ 0 (DfracOwn 1) (to_agree stid_0)); ss. refl. }
    rewrite -{5}Qp.half_half -dfrac_op_own -{2}(agree_idemp (to_agree stid_0)) gmap_view_frag_op.
    iDestruct "TidF" as "[TidF TidF0]".

    iMod (Pending_Shot (get_stid x) with "P") as "S".
    iPoseProof (Shot_dup with "S") as "[S S']".

    steps_r. steps_l. iDestruct "ASM" as "Y".
    forces_l. iSplitL "PRE RRI TidF0 C PubF'".
    { do 4 iExists _. rewrite /Public. unseal RRS. iFrame. iPureIntro; eauto. }

    iApply wsim_unfold; iIntros "WI".
    rewrite /SModTr.NativeYield. steps_r.
    steps_l. force_l (get_stid x). steps_l. force_l. iSplitL "Tsch Y WI"; first iFrame.
    steps_l. yield "Ysch RRIA TidA TidF S' PubA".
    { do 6 iExists _. iSplit; eauto.
      { iPureIntro. esplits; eauto.
        instantiate (1 := <[0:=Inv]> ∅). set_solver. }
      iFrame. do 4 iRight. iFrame.
      rewrite /PublicAuth. unseal RRS. iFrame. ss. }

    steps_l. steps_r. iDestruct "ASM" as "(Tsch & Ysch & WI)".

    steps_l. iApply wsim_bind. iSplitL; cycle 1.
    { instantiate (1:= λ _ _, False%I). iIntros (????) "X"; ss. }

    clear H1. iApply wsim_reset. iStopProof.
    revert st_t'. combine_quant st_s'. combine_quant x.
    eapply wsim_coind. i. destruct_quant CIH.
    destruct a as [x [st_s' st_t']]. s.

    iIntros "(PYIP & RRIP & PubF & S & IST & Tsch & Ysch & WI)"; subst.
    unfold_iterC_l. unfold_iterC_r.

    steps_r. steps_l. rewrite SchInSp.
    rr in YieldSpec. destruct parent_yield_fsp; ss.
    rr in YieldSpec; ss. specialize (YieldSpec x).
    destruct YieldSpec as [x0 [PRE POST]]; ss.
    iPoseProof ((PRE tt↑ tt↑) with "[Tsch Ysch WI PYIP]") as ">PRE".
    { rewrite /fspec_simple /fspec_winv /FSpec.precond /=.
      rewrite /precondS /make_fspecS /=. iFrame. eauto. }

    rewrite /FSpec.precond. forces_l. iSplitL "PRE"; eauto.
    steps_l. call "IST". steps_l. steps_r. 

    iMod (POST with "ASM") as "(WI & (Tsch & Ysch & PYIP & %) & %)".

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 4.
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF & Ysch' & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%". subst.
      iPoseProof (YieldToken_both with "Ysch Ysch'") as "%"; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_subseteq_spec in H; eauto.
      instantiate (1 := Inv). instantiate (1 := size (∅: gmap nat InvO)). rewrite lookup_insert. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%". subst.
      iPoseProof (YieldToken_both with "NschY Ysch") as "%"; ss. }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (YieldToken_both with "Ysch NschY") as "%"; ss. }

    iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF & S' & PubA)". hss.
    
    steps_r. steps_l. rewrite Any.upcast_downcast.
    steps_r. steps_l. rewrite Any.upcast_downcast.
    steps_r. steps_l. rewrite H.
    steps_r. steps_l. hss.

    iPoseProof (Shot_match with "S S'") as "%". subst. hss.
    iPoseProof (big_sepL_delete with "Ys") as "[Y Ys]"; eauto.

    forces_l. iSplitL "Tsch Y WI"; first iFrame.

    steps_l. rewrite /SModTr.NativeYield. steps_r.
    yield "TidA RRIA Ys Ysch TidF S PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 4 iRight. iFrame; eauto. }

    steps_r. steps_l. iDestruct "ASM" as "(Tsch & Ysch & WI)".

    by_coind CIH; eauto. iFrame.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_inner_spawn : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr._spawn).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l. iDestruct "ASM" as "[T [Y WI]]".
    rename _q into stid, _q4 into b, _q5 into mtid, _q3 into pre.
    destruct b.
    { (** CASE 1 : normal case **)
      iDestruct "ASM'" as "[ASM' PubF]".
      iDestruct "ASM'" as (????) "(% & PRE & RRIP & TidF)"; des; subst; hss.

      steps_l. steps_r.
      iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 2.
      { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
        destruct (decide (tid = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
        rewrite H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA [PubF]") as "%".
        { rewrite /Public. unseal RRS. ss. }
        ss. }
      { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
        iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
      { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
        destruct (decide (tid = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
        rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
        rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
      { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
        iPoseProof (rrinv_prev_subset with "RRIA") as "%".
        eapply map_choose in H2. des. eapply lookup_weaken in H; eauto. }

      iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
      rewrite STID in Hmtid0. inv Hmtid0.

      dup H1. r in H1. des.
      assert (SPFN: sp fn = Some fsp) by (eapply FunInSchSp; eauto).
      rewrite SPFN. rr in H3; ss. destruct fsp; ss. rr in H3. ss.
      specialize (H3 (mtid, stid, ssch)). des.
      rename H3 into PRE, H4 into POST.
      specialize (PRE fvarg↑ farg↑). rewrite /FSpec.precond /fspec_winv /fspec_virtual /FSpec.precond in PRE; ss.

      iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
      iPoseProof (rrinv_wf with "RRIA") as "%WF".
      hexploit gmap_wf_lookup_size_none; eauto; intros LKN.
      hexploit (@gmap_wf_lookup_exists _ rrinvO (Nat.pred (size rrinvO))); eauto; i; des.
      { destruct (size rrinvO); try nia. destruct ths; ss. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      
      iMod (PRE with "[WI TidF Y RRIP PRE S' RRI Inv' C' PubF T]") as "PRE".
      { iFrame "WI". iExists _. iSplit; eauto. iFrame. iSplit; eauto. }

      forces_l. iSplitL "PRE"; eauto.
      steps_l. call "TidA Ys RRIA S NschY PubA".
      { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto. }

      steps_r. steps_l.

      iApply wsim_bind. iSplitL; cycle 1.
      { instantiate (1:= λ _ _, False%I). iIntros (????) "F"; ss. }
      
      (* Coinduction on yield loop *)
      iClear "IST ASM".
      rewrite !/RRS.spin. unseal "RRS".
      iApply wsim_reset.
      iStopProof.
      revert st_t'. combine_quant st_s'.
      eapply wsim_coind. i.
      destruct a as [st_src1 st_tgt1]. s.
      destruct_quant CIH. iIntros "_".
      unfold_iterC_l. unfold_iterC_r.
      steps_l; steps_r.
      by_coind CIH; eauto.      
    }
    { (** CASE 2: init case **)
      iDestruct "ASM'" as (????) "(% & PRE & RRI & TidF & C & PubF)"; des; subst; hss.

      steps_l. steps_r.

      iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst.
      { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRI RRIA" as "RRIA".
        iPoseProof (rrinv_match with "RRIA") as "%"; ss. }
      { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
        iCombine "C C'" as "C". iApply (Control_nodup with "C"). }
      { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid = 0)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
        rewrite H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
      { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
        iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }

      iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S' & PubA)". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid = 0)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
      rewrite H in Hmtid0. inv Hmtid0.

      iPoseProof (rrinv_wf with "RRI") as "%WF".
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst.
      iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
      iCombine "TidF TidF'" as "TidF". rewrite agree_idemp.

      dup H1. r in H1. des.
      assert (SPFN: sp fn = Some fsp) by (eapply FunInSchSp; eauto).
      rewrite SPFN. rr in H1; ss. destruct fsp; ss. rr in H2. ss.
      specialize (H2 (0, stid, ssch)). des.
      rename H2 into PRE, H3 into POST.
      specialize (PRE fvarg↑ farg↑). rewrite /FSpec.precond /fspec_winv /fspec_virtual /FSpec.precond in PRE; ss.

      hexploit gmap_wf_lookup_size_none; eauto; intros LKN.
      remember {[0 := Inv]} as rrinvO.
      hexploit (@gmap_wf_lookup_exists _ rrinvO (Nat.pred (size rrinvO))); eauto; i; des.
      { destruct (size rrinvO); try nia. destruct ths; ss. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      
      iMod (PRE with "[WI TidF Y RRIP PRE S' C RRI PubF T]") as "PRE".
      { iFrame "WI". iExists _. iSplit; eauto. iFrame. iSplit; eauto. }

      forces_l. iSplitL "PRE"; eauto.
      steps_l. call "TidA Ys RRIA S Ysch' PubA".
      { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto. }

      steps_r. steps_l.

      iApply wsim_bind. iSplitL; cycle 1.
      { instantiate (1:= λ _ _, False%I). iIntros (????) "F"; ss. }
      
      (* Coinduction on yield loop *)
      iClear "IST ASM".
      rewrite !/RRS.spin. unseal "RRS".
      iApply wsim_reset.
      iStopProof.
      revert st_t'. combine_quant st_s'.
      eapply wsim_coind. i.
      destruct a as [st_src1 st_tgt1]. s.
      destruct_quant CIH. iIntros "_".
      unfold_iterC_l. unfold_iterC_r.
      steps_l; steps_r.
      by_coind CIH; eauto.
    }

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr.spawn).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l. iDestruct "ASM" as (?) "(% & (% & % & % & % & PRE) & (TidF & Y & T & S & C & PubF) & RRI)"; des; subst; hss.
    rename _q2 into Inv, _q4 into Invs, _q6 into pre, _q8 into ssch, _q9 into mtid, _q10 into stid.
    
    steps_l; steps_r.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst.
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst; ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.

    steps_l. steps_r. hss.
    set (size rrinvO) as mtid_new.
    steps_l. steps_r. force_l (true, mtid_new, pre).
    steps_l. force_l. steps_l. spawn. iIntros (stid_new).

    iPoseProof (rrinv_wf with "RRIA") as "%".
    iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame; subst.
    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".
    iPoseProof (rrinv_admin_alloc rrinvO Inv with "RRIA") as ">RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
    hexploit gmap_wf_lookup_size_none; eauto. intros LKN.

    iMod (own_update with "TidA") as "[TidA TidF']".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree stid_new)); ss.
      { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom.
        rewrite -not_elem_of_list_to_map ?imap_fmap fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new. destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; lia.
      }
      refl.
    }

    iMod (Public_alloc with "PubA") as "[PubA PubF']"; eauto.

    steps_r. steps_l.
    forces_l. iSplitL "PRE RRIP TidF' PubF'"; first iFrame.
    { subst mtid_new. rewrite -INVWF. iFrame. iExists _. iPureIntro. esplits; eauto. eapply insert_non_empty. }

    steps_l. forces_l. iSplitL "TidF RRI Y T S C PubF"; iFrame; eauto.
    steps_l. step. iSplit; eauto.
    do 6 iExists _. iSplit; eauto.
    { iPureIntro. esplits; eauto. instantiate (1 := <[size rrinvO := Inv]> rrinvO).
      rewrite map_size_insert LKN last_length INVWF //. }
    iSplitL "TidA".
    { rewrite /TidAuth ?fmap_app /= imap_app /= ?length_fmap Nat.add_0_r list_to_map_snoc.
      { subst mtid_new. rewrite fmap_insert -INVWF //. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite ?length_fmap in Hin; lia. }

    do 2 iRight. iLeft. rewrite /Ist_public. iFrame. ss. iSplit; eauto.
    { iPureIntro. rewrite lookup_app. rewrite H //. }
    rewrite Nat.add_0_r. des_ifs. iFrame; eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_yield : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr.yield).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l.
    rename _q5 into mtid, _q6 into stid, _q4 into ssch, _q2 into Inv.
    iDestruct "ASM" as "[[-> [(TidF & Y & T & S & C & PubF) [RRI [% [% Inv]]]]] ->]". hss. steps_r. steps_l.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H0 in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst.
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst; ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
    iPoseProof (Shot_match with "S S'") as "->".
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite H0 in Hmtid0. inv Hmtid0.

    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
    assert (NEMP: Inv ≠ ∅) by set_solver.
    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_match with "RRIA") as "->".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.

    steps_l. steps_r. hss.
    steps_l. steps_r. rewrite /SModTr.NativeGetTid. force_l stid. steps_l. forces_l. iSplitL "T"; first iFrame.
    steps_l. step. steps_l. steps_r. iDestruct "ASM" as "[-> T]". hss.
    steps_l. steps_r. rewrite H0. case_decide; ss. steps_l. steps_r.
    eapply lookup_lt_Some in H0 as LEN.
    generalize (succ_rr_upperbound mtid (length ths) LEN); intro LEN0.
    eapply lookup_lt_is_Some in LEN0. rewrite /is_Some in LEN0. des. rewrite LEN0.

    rename x into stidn. set (succ_rr mtid (length ths)) as mtidn.
    steps_r. steps_l. rewrite /SModTr.NativeYield.
    iApply wsim_unfold; iIntros "WI".
    iAssert (YIELD stidn ∗
        [∗ list] i ↦ e ∈ ths, if decide (i = mtidn) then emp else YIELD e)%I
      with "[Y Ys]" as "[Y Ys]".
    { destruct (decide (mtid = mtidn)). 
      { subst mtidn; subst; destruct (ths !! mtid) eqn:L; ss; clarify.
        rewrite e in L. rewrite L in LEN0. inv LEN0. rewrite -e. iFrame. }
      iPoseProof (big_sepL_delete _ ths mtid with "[Ys Y]") as "Ys"; eauto.
      { do 2 iFrame. }
      rewrite big_sepL_delete; try iFrame.
      subst mtidn. eauto. }
    forces_l. iSplitL "T Y WI"; first iFrame.
    steps_l. steps_r. yield "TidA Ys RRIA Inv NschY C S' PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". iRight. iLeft. iFrame.
      iPureIntro. esplits.
      { subst mtidn. eauto. }
      { subst mtidn. rewrite INVWF pred_succ_id //. }
    }
    steps_l. steps_r.
    iDestruct "ASM" as "(T & Y & WI)".

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 2.
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H2 in Hmtid0. inv Hmtid0.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%"; ss. }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H2 in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_choose in NEMP. des. eapply lookup_weaken in H2; eauto. }

    iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)". hss.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite STID in Hmtid0. inv Hmtid0.
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_subset with "[RRIP RRI]") as "%"; first iFrame.
    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.
    
    forces_l. iFrame. iSplitR.
    { iPureIntro. esplits; eauto. }

    step. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame. eauto.
    
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_yield_global : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr.yield_global).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> (TidF & Y & T & S & C & PubF)] ->]".
    rename _q2 into ssch, _q3 into mtid, _q4 into stid.

    hss. steps_l. steps_r.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "[% RRIA]". subst.
      destruct ths; ss. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; first iFrame.
      rewrite lookup_empty in H. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.
    iPoseProof (Shot_match with "S S'") as "%"; subst.

    iPoseProof (rrinv_prev_gen with "RRIA") as "[RRIA RRIP]".
    assert (NEMP: rrinvO ≠ ∅).
    { destruct ths; ss. assert (size rrinvO > 0) by nia. set_solver. }
    rewrite -Qp.half_half -dfrac_op_own -(agree_idemp (to_agree stid)) gmap_view_frag_op.
    iDestruct "TidF" as "[TidF TidF0]".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.

    steps_l. hss. steps_l. steps_r. hss. steps_r.
    iApply wsim_unfold; iIntros "WI".
    rewrite /SModTr.NativeYield. forces_l. iSplitL "T NschY WI"; first iFrame.
    steps_l. steps_r. yield "TidA Ys RRIA TidF0 S' Y PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 3 iRight. iLeft. iFrame.
      iPoseProof (big_sepL_delete with "[Y Ys]") as "Ys"; eauto; iFrame. }
    steps_r. steps_l.

    iDestruct "ASM" as "(T & Y & WI)".
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst.
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_choose in NEMP. des. eapply lookup_weaken in H0; eauto. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
      iCombine "C C'" as "C". iApply (Control_nodup with "C"). }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H0 in Hmtid0. inv Hmtid0.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%"; ss. }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }

    iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch & S' & PubA)".
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H0 in Hmtid0. inv Hmtid0.

    iCombine "TidF TidF'" as "TidF". rewrite agree_idemp.

    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.

    forces_l. iSplitL "WI Y T S C TidF PubF"; iFrame; eauto.
    step. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA".
    do 2 iRight. iLeft. iFrame. eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open RRSAMod RRSIMod RRSA.init_cond Ist (Some RRSHdr.get_tid).
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> (TidF & Y & T & S & C & PubF)] ->]"; hss.
    rename _q2 into ssch, _q3 into mtid, _q4 into stid.
    steps_l; steps_r.

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". hss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "[% RRIA]". subst.
      destruct ths; ss. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; first iFrame.
      rewrite lookup_empty in H. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". hss.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". hss.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.

    steps_l. steps_r. hss. steps_l. steps_r. forces_l. iSplitL "TidF Y T S C PubF"; first iFrame; eauto.
    step. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open RRSAMod RRSIMod RRSA.init_cond Ist.
  Proof using FunInSchSp FunInRrsSp SchInSp RRSInSp YieldSpec.
    init_sim.
    - split; eauto. rewrite /RRSA.init_cond /init_inv /init_tid /init_pub. unseal RRS.
      iIntros "(RRI & tid & pub)". rewrite /Ist.
      iExists [], 0, 0, 0, ∅, (existT 0 (SL.pure True)).
      iSplit; eauto. ss. iFrame. iLeft. iFrame; eauto.
    - eapply simF_init.
    - eapply simF_inner_spawn.
    - eapply simF_spawn.
    - eapply simF_yield.
    - eapply simF_yield_global.
    - eapply simF_get_tid.
  Qed.
End RRSIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_rrsG: !rrsG}.

  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid : T → nat) (PYIP: T → iProp Σ).

  Lemma ctxr sp sp_sch_user sp_rrs_user
        (SchInGlobal     : sp parent_yield = Some parent_yield_fsp)
        (RRSInGlobal     : sp_incl (RRSAS.sp sp_rrs_user ⊤ get_stid PYIP) sp)
        (SchUserInGlobal : sp_incl sp_sch_user sp)
        (RrsUserInSch    : spl_sub sp_rrs_user sp_sch_user) 
        (YieldSpec :
          fspec_imply' parent_yield_fsp
            (fspec_winv ⊤
               (fspec_simple (λ x: T,
                      ((λ varg, TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜varg = tt↑⌝),
                        (λ vret, TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜vret = tt↑⌝))%I)))) :
    ctx_refines
      (RRSA.t parent_yield sp sp_rrs_user get_stid PYIP, RRSA.init_cond)
      (RRSI.t parent_yield,                              emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.

End ctxr.
End RRSIA.


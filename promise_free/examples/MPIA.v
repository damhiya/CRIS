Require Import CRIS.
Require Import PFMemHeader PFMemA base HistoryRA AtomicRA.
Require Import SystemHeader SystemA SystemTactics.
Require Import MPI MPA.

Module MPIA. Section MPIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG, !sysG, !one_shotG}.
  Local Existing Instances one_shot_inG.

  Definition Ist : alist key Any.t → alist key Any.t → iProp Σ := λ _ _, emp%I.

  Context (sp_user : spl_type).
  Context (sp_s : sp_type).
  Context (SchInSpS : sp_incl (SystemA.sp sp_user ⊤) sp_s).
  Context (HMP : spl_sub MPA.sp sp_user).

  Local Definition MA := (MPA.t sp_s ★ SystemA.t sp_user sp_s ★ PFMemA.t sp_s).
  Local Definition MI := (MPI.t      ★ SystemA.t sp_user sp_s ★ PFMemA.t sp_s).
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (MPA.t sp_s)) Ist) IstEq).

  Lemma mp2_spawnable : SystemA.fspec_spawnable sp_user MPHdr.mp2 MPA.mp2_precondition.
  Proof.
    exists MPA.mp2_spec; split; [eapply HMP; ss|].
    intros [tid stid]; ss; exists ((tid, stid)); split.
    { unfold_pre_post. iIntros (??) "[$ [% [-> [% [$ [% [-> P]]]]]]]"; iModIntro; iFrame; ss. }
    { unfold_pre_post; iIntros (??) "[$ $] //". }
  Qed.

  Lemma simF_mp : ISim.sim_fun open MA MI MPA.init_cond%I IstFull None.
  Proof.
    init_simF.
    (* iDestruct "IST" as "[[-> ->] TV]". *)
    steps_l. iDestruct "ASM" as "->". hss_l. steps_l.
    steps_r. hss_r. steps_r.

    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TID". iSplit.
    { iExists [], [], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      iPureIntro; split; unfold_mod; prove_scope.
    }
    iFrame.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    (* alloc *)
    steps_r. inline_r. force_r (1%positive, 0, 2, _). forces_r. iFrame. iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%loc [%V' [[-> %LE] [TV [FA ↦]]]]] ->]".
    rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
    hss_r. steps_r.

    (* yield *)
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    (* yield *)
    steps_r.
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    (* write *)
    steps_r. inline_r.
    force_r (existT 0 (1%positive, 0, loc, Val.Vnum 0, Ordering.na, _)). forces_r.
    rewrite shift_0.
    iFrame "TV".
    iDestruct "↦" as "[↦flag ↦data]"; iSplitL "↦flag".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    steps_r. iDestruct "GRT" as "[[%V'' [[-> %HLE2] [↦flag TV]]] ->]". hss_r.
    tview_sync HLE2.
    steps_r.

    (* yield *)
    steps_r.
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    (* write *)
    steps_r. inline_r.
    force_r (existT 0 (1%positive, 0, loc >> 1, Val.Vnum 0, Ordering.na, _)). forces_r.
    iPoseProof (own_loc_na_own_loc with "↦data") as "$".
    iFrame "TV".
    iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%V3 [[-> %Hle3] [↦data TV]]] ->]".
    tview_sync Hle3. hss_r. steps_r.

    (* yield *)
    steps_r.
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    (* spawn *)
    iMod (own_alloc Pending) as "[%γ O]"; ss.
    iMod (AtomicPtsTo_from_na loc (Val.Vnum 0) with "↦flag")
      as "[%γx [% [% [% [% [% [% [SW ↦flag]]]]]]]]".
    iMod (inv_alloc (MPA.mp_inv' 0 loc (loc >> 1) γ γx) 1 _ _ MPA.mpN with "[↦flag]") as "#I"; eauto.
    { rewrite MPA.mp_inv'_eq.
      SL_red; iExists _; SL_red; iExists false.
      do 6 (SL_red; iExists _).
      SL_red; iSplit; last done.
      rewrite syn_AtomicPtsTo_red; iFrame.
    }
    iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN".

    (* source yield *)
    iApply wsim_system_yield_src.
    force_l (Val.Vptr loc). steps_l.
    (* iApply wsim_system_yield_src. steps_l. *)

    (* spawn *)
    force_l (1%positive, 0, MPA.mp2_precondition, V3). forces_l.
    iFrame "TV".
    iSplitL "↦data SW".
    { iExists _; iSplit; first done.
      iExists _, _, _; iSplit; first (iPureIntro; esplits; eauto using mp2_spawnable).
      rewrite /MPA.mp2_precondition /MPA.mp_inv; iFrame "↦data SW".
      iExists γ; iSplit; eauto.
      rewrite shift_0; eauto.
    }
    steps_l. steps_r. call "IST".

    steps_l. iDestruct "ASM" as "[% [-> [TV [-> ->]]]]".
    steps_r. hss_r. steps_r.
    clear dependent st_src st_tgt.
    iApply wsim_reset.
    (* iRevert "I FA O SW IST TV". *)
    iStopProof.

    revert st_s'. combine_quant st_t'. clear Hle3 H4. combine_quant V3.
    eapply wsim_coind.
    (* destruct_quant. *)
    iIntros (g' _ CIH [V3 [st_t st_s]]) "[#[I SN] [FA [P [IST TV]]]]"; s.

    unfold_iterC_l. steps_l.
    unfold_iterC_r.

    (* yield *)
    steps_r.
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_s st_t.
    iIntros (??) "IST TV".
    Unshelve. all: try exact ⊤.

    steps_r. inline_r.
    iInv "I" as "INV" "ACC".
    iEval (rewrite MPA.mp_inv'_eq /MPA.mp_inv'_def; SL_red) in "INV".
    do 8 (iDestruct "INV" as "[% INV]"; iEval (SL_red) in "INV").
    destruct x0; cycle 1.
    { (* read 0 from flag *)
      iEval (SL_red; rewrite syn_AtomicPtsTo_red) in "INV"; iDestruct "INV" as "[↦flag ->]".
      rewrite AtomicPtsTo_eq. iDestruct "↦flag" as "[% ↦flag]".
      force_r (existT 1 (1%positive, 0, loc, Ordering.acqrel, _, _, _, _, _, _, _, _)). forces_r.
      iFrame "TV SN ↦flag". iSplit; eauto.
      steps_r.
      iDestruct "GRT" as "[[% [% [% [% [% [% [%V4 [[-> %] [#SN2 [↦flag TV]]]]]]]]]] ->]".
      hss_r. steps_r.
      iMod ("ACC" with "[↦flag]") as "_".
      { rewrite {2}MPA.mp_inv'_eq; SL_red; iExists _.
        SL_red; iExists false.
        do 6 (SL_red; iExists _); SL_red.
        rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
        done.
      }

      steps_r.
      iApply wsim_system_yield; ss.
      { unfold_sp_exact sp_s SystemHdr.yield; ss. }
      iFrame "TV IST".
      clear dependent st_src st_tgt.
      iIntros (??) "IST TV".

      steps_r.
      hexploit (H6 (Cell.max_ts ζ'')); first done; rewrite Cell.singleton_get.
      des_if; intros INV; inv INV.
      destruct v'; ss.
      apply Z.eqb_eq in H4; subst.
      steps_r.

      steps_r.
      iApply wsim_system_yield; ss.
      { unfold_sp_exact sp_s SystemHdr.yield; ss. }
      iFrame "TV IST".
      clear dependent st_src st_tgt.
      iIntros (??) "IST TV".
      steps_r.

      iApply wsim_system_yield_src. force_l false. steps_l.
      iApply wsim_progress.
      iApply wsim_base.
      iIntros "W".

      iApply ((CIH (V4, (st_tgt, st_src))) with "[-]"); iFrame. iFrame "I".
      ss. iModIntro. iEval (rewrite H8) in "SN". done.
      Unshelve. all: try exact ⊤; try exact 1%Qp.
    }
    { (* read 1 from flag *)
      iDestruct "INV" as "[↦flag INV]".
      do 3 (SL_red; iDestruct "INV" as "[% INV]").
      SL_red; iDestruct "INV" as "[[% %Hadd] [P2|INV]]".
      { iCombine "P" "P2" gives %WF; inv WF. }
      rewrite syn_AtomicPtsTo_red.
      iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at) in "↦flag".
      iDestruct "↦flag" as "[% ↦flag]".
      force_r (existT 1 (_, _, _, _, _, _, _, _, _, _, V3, x2)). forces_r.
      (* iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN". *)
      iFrame "TV SN ↦flag". iSplit; eauto.
      steps_r.
      iDestruct "GRT" as "[[% [% [% [% [% [% [% [[-> %Hres] [#SN2 [↦flag TV]]]]]]]]]] ->]".
      destruct Hres as [Hval [Hcell1 [Hcell2 [Hget [Hvle Hvle2]]]]].
      hexploit (Hcell2 (Cell.max_ts ζ'')); eauto.
      erewrite Cell.add_o; eauto; des_if.
      { (* read 1 *)
        subst. intros INV; inv INV.
        (* iClear "CIH". *)
        destruct v'; ss. apply Z.eqb_eq in Hval; subst.
        hss_r; steps_r.
        iMod ("ACC" with "[↦flag P]") as "_".
        { rewrite MPA.mp_inv'_eq; SL_red; iExists _.
          SL_red; iExists true.
          do 6 (SL_red; iExists _); SL_red.
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
          do 3 (iExists _; SL_red); iFrame "P"; eauto.
        }

        (* yield *)
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.

        (* yield *)
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.
        Unshelve. all: try exact ⊤.

        (* yield *)
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.

        (* non-atomic load here *)
        inline_r. force_r (existT 0 (_, _, _, _, _, _, _)). forces_r.
        iEval (rewrite syn_own_loc_na_red) in "INV".
        assert (Hawk : Ordering.le Ordering.acqrel Ordering.acqrel) by refl.
        rewrite Hvle2 Hawk Hvle.
        iFrame "TV INV". iSplit; eauto.

        steps_r. iDestruct "GRT" as "[[% [% [[-> %Hval'] [↦data TV]]]] ->]". hss_r.

        steps_r.
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.
        Unshelve. all: try exact ⊤.

        destruct v'; ss. eapply Z.eqb_eq in Hval'; subst.
        steps_r.

        iApply wsim_system_yield_src. force_l true; steps_l.
        forces_l. iSplit; eauto.
        step.
        iSplit; eauto.
        Unshelve. all: try exact ⊤; try exact 1%Qp.
      }
      { (* read 0 *)
        rewrite Cell.singleton_get; des_if; intros INV; inv INV.
        destruct v'; ss. eapply Z.eqb_eq in Hval; subst.
        hss_r; steps_r.

        (* close invariant *)
        iMod ("ACC" with "[↦flag INV]") as "_".
        { rewrite MPA.mp_inv'_eq; SL_red; iExists _.
          SL_red; iExists true.
          do 6 (SL_red; iExists _); SL_red.
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
          do 3 (iExists _; SL_red); iFrame "INV"; eauto.
        }

        (* yield *)
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.

        (* yield *)
        iApply wsim_system_yield; ss.
        { unfold_sp_exact sp_s SystemHdr.yield; ss. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        steps_r.

        iApply wsim_system_yield_src. force_l false. steps_l.
        iApply wsim_progress.
        iApply wsim_base.
        iIntros "W".
        (* iSpecialize ("CIH" $! ); s. *)

        iApply ((CIH (_, (st_tgt, st_src))) with "[-]"); iFrame. iFrame "I".
        iEval (rewrite Hvle) in "SN"; s; iModIntro; done.
      }
    }
  Unshelve. all: try exact 1%Qp; try exact ⊤.
  (*SLOW*)Admitted.

  Lemma simF_mp2 : ISim.sim_fun open MA MI MPA.init_cond%I IstFull (Some MPHdr.mp2).
  Proof.
    init_simF.
    steps_l.
    iDestruct "ASM" as "[%va [-> [%sa [%V [-> [PRE TV]]]]]]".
    rename _q1 into tid, _q2 into stid. hss_l.
    rewrite /MPA.mp2_precondition.
    iDestruct "PRE" as "[%loc [%γ [%γx [%V0 [%fd [%td [% [% [[-> ->] [#I [↦data ⊒]]]]]]]]]]]".
    steps_l. hss_l. steps_l.

    rewrite /MPA.mp2. steps_l.

    steps_r. hss_r. steps_r. hss_r. steps_r.
    rewrite /MPI.mp2. norm_r.

    (* yield *)
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    steps_r.
    Unshelve. all: try exact ⊤.

    (* yield *)
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    steps_r.
    Unshelve. all: try exact ⊤.

    (* write to data *)
    inline_r.
    force_r (existT 0 (_, _, _, _, _, _)). forces_r.
    iPoseProof (own_loc_na_own_loc with "↦data") as "↦data".
    iFrame "TV ↦data". iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%V2 [[-> %Hle] [↦data TV]]] ->]".
    hss_r. steps_r.

    (* yield *)
    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    steps_r.
    Unshelve. all: try exact ⊤.

    (* open invariant *)
    (* iMod (AtomicPtsToX_from_na _  _ V2 with "↦data") as "[%γd [%f [%t [%Hft [%V0 [% [%H02 [sw swX]]]]]]]]". *)
    iInv "I" as "INV" "ACC".
    iEval (rewrite MPA.mp_inv'_eq /MPA.mp_inv'_def; SL_red) in "INV".
    do 8 (iDestruct "INV" as "[% INV]"; iEval (SL_red) in "INV").
    iDestruct "INV" as "[↦flag _]".
    rewrite syn_AtomicPtsTo_red.
    rewrite shift_0; iPoseProof (AtomicPtsTo_SWriter_agree with "[$] [$]") as "->".

    inline_r. steps_r.
    iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at) in "↦flag".
    iDestruct "↦flag" as "[% ↦flag]".
    force_r (existT 1 (tid, stid, loc, Val.Vnum 1, Ordering.acqrel, V2, γx, _, _, _, _, _, _, _)).
    forces_r.
    iFrame "↦flag". iSplitL "⊒ TV"; eauto.
    { iSplit; eauto. iSplit; eauto. iFrame. tview_sync Hle.
      iPoseProof (AtomicSWriter_AtomicSeen with "⊒") as "#sn"; iSplit; eauto.
      rewrite AtomicSWriter_eq /AtomicSWriter_def /view_at /=; iDestruct "⊒" as "[? [? ?]]"; iFrame.
    }
    Unshelve. all: try exact 1%Qp.
    steps_r.

    iDestruct "GRT" as "[[% [% [% [% [% [% [[-> [%Htime %Hres]] [sn [at [sy [swX tv]]]]]]]]]]] ->]".
    destruct (Ordering.le _ _) eqn : Heqb in Hres; ss; subst; clear Heqb.
    rewrite Cell.max_ts_singleton in Htime.
    hss_r. steps_r.
    iMod ("ACC" with "[↦data swX]") as "_".
    { rewrite MPA.mp_inv'_eq.
      SL_red; iExists _; SL_red; iExists true.
      do 6 (SL_red; iExists _).
      SL_red.
      rewrite syn_AtomicPtsTo_red; iFrame.
      iSplitL "swX".
      { rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at; iExists t; iFrame. }
      do 3 (SL_red; iExists _); SL_red.
      iSplitR "↦data".
      iPureIntro. split; cycle 1; eauto.
      iRight; rewrite syn_own_loc_na_red.
      iApply (own_loc_mon_pred_gen with "↦data"); eauto; try exact 1%Qp.
      apply View.join_l.
    }

    iApply wsim_system_yield; ss.
    { unfold_sp_exact sp_s SystemHdr.yield; ss. }
    iFrame "tv IST". clear dependent st_src st_tgt; iIntros (st_src st_tgt) "IST TID".
    steps_r.

    iApply (wsim_system_yield_src with "[-]"). steps_l. forces_l.
    iFrame. iSplitR; [eauto|]. step. iFrame. done. 
  Unshelve. all: try exact ⊤.
  Qed.

  Lemma sim : ISim.t open MA MI MPA.init_cond IstFull.
  Proof.
    init_sim.
    { eapply simF_mp2. }
    { eapply simF_mp. }
  Qed.
End MPIA.
Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG, !sysG, !one_shotG}.

  Definition ctxr (sp_s : sp_type) (sp_user : spl_type) :
    sp_incl (SystemA.sp sp_user ⊤) sp_s →
    spl_sub MPA.sp sp_user →
    ctx_refines
      ((MPA.t sp_s ★ SystemA.t sp_user sp_s ★ PFMemA.t sp_s), MPA.init_cond)
      ((MPI.t      ★ SystemA.t sp_user sp_s ★ PFMemA.t sp_s), True%I).
  Proof using.
    intros ??.
    eapply main_adequacy, sim; eauto.
  Qed.
End ctxr.
End MPIA.
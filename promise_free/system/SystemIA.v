Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
(* rewrite Import SystemIAAlloc SystemIAWrite SystemIARead. *)
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Module SystemIA. Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG, !sysG}.
  Context (sp_user : spl_type).
  Context (sp : sp_type).
  Context (size : list Z).
  Context (Hincl : sp_incl sp_user sp).
  Context (Hsysincl : sp_incl (SystemA.sp sp_user ⊤) sp).

  Local Definition SystemA_s := SystemA.t sp_user sp ★ PFMemA.t sp.
  Local Definition SystemI_s := SystemI.t ★ PFMemA.t sp.
  Local Definition init_cond := init_cond size.

  Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    λ st_src st_tgt,
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = [(SystemI.v_tid, tid↑); (SystemI.v_tids, tids'↑)] ∧
         st_src = [(SystemA.v_tid, tid↑); (SystemA.v_tids, tids'↑)]⌝ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (* tview_sys_gen (1/2) i V ∗ *)
          (YIELD stid)))%I.

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq).

  Lemma simF__spawn :
    ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr._spawn).
  Proof.
    init_simF.

    steps_l.
    iDestruct "ASM'" as
      "[%tid [%𝓥 [%pre [%fvarg [%farg [%fn [[-> [-> %FS]] [TV PRE]]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA TVS]]]]".
    hss_l. steps_l.

    destruct FS as [[fsp|fsp] [->%Hincl Himpl]]; ss.
    destruct (Himpl (tid, _q, 𝓥)) as [fmeta [Hpre Hpost]].
    force_l fmeta. steps_l. force_l (farg↑). steps_l.

    (* iDestruct "TV" as "[TV STV]". *)
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    revert Hpre; unfold_pre_post; intros Hpre.
    iDestruct "ASM" as "[TID [YIELD W]]".
    (* iPoseProof (big_sepM_delete with "TVS") as "[TV2 TVS]"; eauto. *)
    (* iCombine "TV TV2" as "TV". *)
    iMod (Hpre with "[TID YIELD TV W PRE]") as "PRE"; first iFrame; eauto.
    force_l; iSplitL "PRE"; first iFrame.
    steps_l.

    hss_r. steps_r.
    (* steps_r. rewrite /SystemI.check_internal; steps_r; hss. *)
    
    call "TA TVS".
    { iExists [_; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
      iSplit; eauto.
      iSplit; eauto.
      iExists _, _; iSplit; [iPureIntro; esplits; eauto|ss; iFrame].
    }
    steps_l. steps_r.
    iMod (Hpost with "ASM") as "[W [% [_ TV]]]".

    rewrite /System.terminate; unseal "System".
    iApply wsim_reset. iStopProof.
    revert st_s'. combine_quant st_t'.
    eapply wsim_coind; intros g' _ CIH [st_s' st_t']; ss.
    destruct_quant CIH.

    iIntros "[IST [W TV]]". iPoseProof (winv_split_empty with "W") as "[W We]".

    unfold_iterC_l. steps_l. force_l (tid, _q, 𝓥). steps_l. force_l (tt↑). steps_l.
    force_l; iFrame "W TV"; iSplit; eauto. steps_l.
    unfold_iterC_r. steps_r.
    call "IST".
    steps_l. iDestruct "ASM" as "[[-> TV] ->]". hss. steps_l.
    steps_r. hss_r. steps_r.
    by_coind CIH; iFrame.
    (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.spawn).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[%varg [-> [%fvarg [%farg [%fn [[-> [-> %Hsp]] [TV PRE]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA TVS]]]]".
    (* rename _q2 into 𝓥, _q5 into tid, _q4 into pre, _q6 into stid. *)
    rename _q2 into V, _q5 into tid, _q4 into pre, _q6 into stid.

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV STV]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { 
      (* rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[V stid] [? Hlookup]]; ss; subst V. *)
      iPoseProof (big_sepM_lookup_acc with "TVS") as "[TV2 TVS]".
      { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
      iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
    }
    subst.

    steps_r. hss. steps_l; steps_r. hss. steps_l; steps_r. hss. steps_l; steps_r.

    (* Calling PFMemHdr.spawn *)
    (* steps_r. hss_r. steps_r. hss_r. steps_r. hss_r. steps_r. *)
    (* rewrite /SystemI.new_tid. steps_r. *)
    inline_r. steps_r.
    (* force_r (tid_cur, V). steps_r. *)
    force_r (tid_cur, V). steps_r.
    force_r (tid_cur↑). steps_r.

    iDestruct "TA" as "[TA MTVS]".
    iPoseProof (big_sepM_lookup_acc with "MTVS") as "[MTV MTVS]"; eauto; ss.
    force_r; iFrame "MTV"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%tid_new [-> [TV_cur TV_new]]] ->]".
    iPoseProof ("MTVS" with "TV_cur") as "MTVS".
    destruct (tids !! tid_new) as [[? ?]|] eqn : Hnew.
    { iPoseProof (big_sepM_lookup_acc _ _ tid_new with "MTVS") as "[TV_new2 MTVS]"; eauto.
      s; rewrite tview_eq /tview_def. iCombine "TV_new TV_new2" gives %WF%auth_frag_op_valid_1.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF; done.
    }
    hss_r. steps_r.

    unshelve (force_l (exist _ tid_new _)).
    { ss; rewrite lookup_fmap Hnew //. }
    steps_l. forces_l. steps_l.
    spawn. iIntros (nths); steps_l. steps_r. hss.

    iMod (own_update with "TA") as "TA".
    { eapply (gmap_view_alloc _ tid_new (DfracOwn 1) (to_agree (V, nths))); ss.
      { rewrite ?lookup_fmap Hnew //. }
    }
    iDestruct "TA" as "[TA TVS_new]".
    (* iDestruct "TVS_new" as "[TVS_new TVS_new1]". *)

    (* force_l. steps_l. force_l ((tid_new, fn, farg)↑). steps_l. *)
    force_l. iFrame "TVS_new".
    iSplitL "PRE".
    { iExists _, _, _, _; iSplit; eauto. }
    steps_l.
    (* spawn. iIntros (nths); steps_l. steps_r. hss. *)

    forces_l. iFrame "TV STV". iSplit; eauto. steps_l. step.
    iSplit; eauto.
    iExists [_; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists tid_cur, (<[tid_new := (V, nths)]> tids).
    rewrite -?fmap_insert /=.
    (* iSplit; eauto. *)
    rewrite ?fmap_insert /=; iSplit; eauto; iFrame.
    rewrite -fmap_insert; iFrame "TA".
    iSplitL "TV_new MTVS".
    { iPoseProof (big_sepM_insert with "[TV_new MTVS]") as "$"; last iFrame; eauto. }
    {
       (* destruct flag.
      { rewrite fmap_insert /= big_sepM_insert; [iFrame|rewrite lookup_fmap Hnew //]. }
      {  *)
        (* rewrite ?fmap_delete fmap_insert /= delete_insert_ne; cycle 1.
        { ii; clarify; rewrite lookup_fmap Hnew // in Hlookup. } *)
      rewrite delete_insert_ne; cycle 1. { ii; clarify. }
      rewrite fmap_insert /= big_sepM_insert; first iFrame.
      rewrite lookup_fmap lookup_delete_ne; cycle 1. { ii; clarify. }
      rewrite Hnew //.
    }
  Unshelve. ss.
  (*SLOW*)Admitted.

  Lemma simF_yield : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.yield).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> TV] ->]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
    rename _q3 into tid, _q2 into V, _q4 into stid.

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst.
    hss_l. steps_l; steps_r. hss. steps_l; steps_r. hss. steps_r.
    
    destruct _q as [[tid_next stid_next] Hin].
    force_l (exist _ (tid_next, stid_next) Hin). steps_l.

    force_l stid. steps_l. ss.
    iAssert (YIELD stid_next ∗
        [∗ map] i ↦ e ∈ (snd <$> delete tid_next tids), YIELD e)%I
      with "[Y YS]" as "[Y YS]".
    { destruct (decide (tid_cur = tid_next)). 
      { subst. rewrite lookup_fmap Hlookup in Hin; ss; clarify.
        destruct (tids !! tid_next) as [[[? ?] ?]|]; ss. iFrame.
      }
      rewrite fmap_delete.
      iPoseProof (big_sepM_insert_delete with "[Y YS]") as "YS".
      { iSplitL "Y"; iFrame; ss. }
      iPoseProof (big_sepM_delete _ _ tid_next with "YS") as "[$ YS]".
      { rewrite lookup_insert_ne //. }
      rewrite (insert_id (snd <$> tids) tid_cur). 2:{ rewrite lookup_fmap Hlookup //. }
      rewrite fmap_delete //.
    }
    iApply wsim_unfold; iIntros "W".
    force_l; iFrame.

    (* rewrite /trigger_Yield. steps_l. hss. *)
    (* rewrite /SystemI.trigger_Yield. steps_r. hss_r. steps_r. hss_r. steps_r.
    eapply elem_of_dom in Hin. destruct (_ !! tid_next) as [tid_s_next|] eqn : Hnext ; [|inv Hin]. *)

    (* steps_l. hss. rewrite Hnext. steps_l. steps_r.
    (* splitting thread view for IST *)
    iDestruct "TVS" as "[TVS TVS2]".
    iApply wsim_unfold; iIntros "WS". *)
    steps_l; steps_r. rewrite /SModTr.NativeYield /=.
    yield "TA YS".
    { iExists [_; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
      iSplit; eauto. iSplit; eauto. iExists _, _; iSplit; first eauto. iFrame.
    }

    clear dependent tids.
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur2 [%tids [[-> ->] [TA YS]]]]".
    steps_l. force_l (tt↑). step_l. force_l. iFrame. iDestruct "ASM" as "[$ [$ $]]". iSplit; eauto.

    steps_l; steps_r. step.
    (* hss. rewrite /check_internal. steps_l. hss.
    steps_r. hss.

    rename _q into tid.
    iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
    rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[??] [? Hlookup]]; ss; subst.

    iEval (rewrite (big_sepM_delete _ (fst <$> tids) tid); [|rewrite lookup_fmap Hlookup //]; s)
      in "TVSM".
    iDestruct "TVSM" as "[TVS2 TVSM]"; iCombine "TVS TVS2" as "TVS".
    forces_l; iFrame; iSplit; eauto. *)

    (* steps_l. step. *)
    iSplit; eauto.
    iExists [_; _], [_; _], _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists _, _; iSplit; first eauto.
    iFrame.
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.get_tid).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> TV] ->]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
    rename _q3 into tid, _q2 into V, _q4 into stid.

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst.
    hss_l. steps_l; steps_r. hss. steps_l; steps_r. hss. steps_r.
    force_l (tid_cur↑). steps_l. force_l. iFrame. iSplit; eauto. step. iSplit; eauto.

    (* steps_l. iDestruct "ASM" as "[[-> TVS] ->]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".

    steps_r. hss_r. steps_r. hss_r. steps_r.
    hss_l. steps_l. hss.
    rename _q into tid_cur, _q1 into tid_user, _q2 into V_user.
    iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
    destruct (decide (tid_user = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TV2 TVSM]".
      { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
      iCombine "TVS TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
      by apply dfrac_valid_own in WF.
    }
    subst.

    forces_l. iFrame. iSplit; eauto. step. iSplit; first done. *)
    iExists [_; _], [_; _], _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iFrame. done.
  (*SLOW*)Qed.
End SystemIA.
Section ctx_refines.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG, !sysG}.

  (* Scheduler for WM refines its specification when linked to WMM *)
  Lemma ctxr sp_user sp size :
    sp_incl sp_user sp →
    sp_incl (SystemA.sp sp_user ⊤) sp →
    ctx_refines
      (SystemA.t sp_user sp ★ PFMemA.t sp, init_cond size)
      (SystemI.t            ★ PFMemA.t sp, emp%I).
  Proof.
    intros ??.
    eapply main_adequacy with (Ist := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq)).
    init_sim.
    { split; ss. iIntros "TA"; iSplit; ss.
      { iPureIntro; split; prove_scope. }
      { iExists 1%positive, {[1%positive := (TView.init size, 0)]}; iFrame.
        iSplit; first eauto.
        rewrite delete_singleton fmap_empty //.
      }
    }
    { apply simF__spawn; eauto. }
    { apply simF_spawn; eauto. }
    { apply simF_yield; eauto. }
    { apply simF_get_tid; eauto. }
    (* { apply simF_alloc; eauto. } *)
    { admit. }
    { admit. }
    { admit. }
    (* { apply simF_write; eauto. }
    { apply simF_read; eauto. } *)
  Admitted.
End ctx_refines. End SystemIA.
Require Import CRIS.
Require Import SystemHeader SystemI SystemA SystemIAAlloc SystemIAWrite SystemIARead.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Module SystemIA. Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, !histG, !atomicG, !sysG}.
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
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)) (flag : bool),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = [(SystemI.v_tid, tid↑); (SystemI.v_tids, tids'↑)] ∧
         st_src = [(v_internal, flag↑); (SystemI.v_tid, tid↑); (SystemI.v_tids, tids'↑)]⌝ ∗
        (if flag then winv (⊤, ⊤) else True) ∗
        tview_sys_auth (fst <$> tids) ∗
        [∗ map] tid ↦ 𝓥 ∈ fst <$> (if flag then tids else delete tid tids),
          tview_sys_gen (1/2) tid 𝓥)%I.

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq).

  Lemma simF__spawn : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr._spawn).
  Proof.
    init_simF.

    steps_l.
    iDestruct "ASM" as
      "[%varg [-> [%tid [%𝓥 [%pre [%fvarg [%farg [%fn [[-> [-> %FS]] [TV PRE]]]]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA MTVS] TVS]]]]]]".
    (* flag must be true in order for _spawn to proceed *)
    hss_l. steps_l. rewrite /check_internal; steps_l; hss.

    destruct FS as [fsp [->%Hincl Himpl]].
    destruct (Himpl (tid, 𝓥)) as [fmeta [Hpre Hpost]].
    force_l fmeta. steps_l. force_l (farg↑). steps_l.

    iPoseProof (tview_sys_lookup with "[TA MTVS] TV") as "%Hlookup"; first iFrame.
    iPoseProof (big_sepM_delete with "TVS") as "[TV2 TVS]"; eauto.
    iCombine "TV TV2" as "TV".
    iMod (Hpre with "[TV W PRE]") as "PRE"; first iFrame; eauto.
    force_l; iSplitL "PRE"; first iFrame.
    steps_l.

    steps_r. rewrite /SystemI.check_internal; steps_r; hss.
    
    call "TA MTVS TVS".
    { iExists [_; _; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
      iSplit; eauto.
      iSplit; eauto.
      iExists _, _, _; iSplit; [iPureIntro; esplits; eauto|ss; iFrame].
      rewrite fmap_delete //.
    }
    steps_l. steps_r.
    iMod (Hpost with "ASM") as "[W [% [_ TV]]]".

    rewrite /System.terminate; unseal "System".
    iApply wsim_reset. iStopProof.
    revert st_s'. combine_quant st_t'.
    eapply wsim_coind; intros g' [st_s' st_t']; ss.
    iIntros "[IST [W TV]] _ #CIH".

    unfold_iter_l. steps_l. force_l (tid, 𝓥). steps_l. force_l (tt↑). steps_l.
    force_l; iFrame "W TV"; iSplit; eauto. steps_l.
    unfold_iter_r. steps_r.
    call "IST".
    steps_l. iDestruct "ASM" as "[[-> TV] ->]". hss. steps_l.
    steps_r. hss_r. steps_r.
    by_coind "CIH"; iFrame.
  Unshelve. all: eauto.
  (*SLOW*)Admitted.

  Lemma simF_spawn : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.spawn).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[%varg [-> [%fvarg [%farg [%fn [[-> [-> %Hsp]] [TV PRE]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA MTVS] TVS]]]]]]".
    rename _q2 into 𝓥, _q3 into tid, _q4 into pre.

    (* v_tid is set to a correct one *)
    iPoseProof (tview_sys_lookup with "[TA MTVS] TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "TVS") as "[TV2 TVS]".
      { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
      iCombine "TV TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
      by apply dfrac_valid_own in WF.
    }
    subst.

    hss_l. steps_l. hss. rename _q into tid_cur. rewrite /new_tid. steps_l.

    (* Calling PFMemHdr.spawn *)
    steps_r. hss_r. steps_r. hss_r. steps_r. hss_r. steps_r.
    rewrite /SystemI.new_tid. steps_r.
    inline_r. steps_r.
    force_r (tid_cur, 𝓥). steps_r.
    force_r (tid_cur↑). steps_r. force_r.

    iPoseProof (big_sepM_lookup_acc with "MTVS") as "[$ MTVS]"; ss.
    iSplit; eauto.
    steps_l. steps_r. iDestruct "GRT" as "[[%tid_new [-> [TV_cur TV_new]]] ->]".
    iPoseProof ("MTVS" with "TV_cur") as "MTVS".
    destruct (tids !! tid_new) as [[? ?]|] eqn : Hnew.
    { iPoseProof (big_sepM_lookup_acc _ _ tid_new with "MTVS") as "[TV_new2 MTVS]".
      { rewrite lookup_fmap Hnew //. }
      s; rewrite tview_eq /tview_def. iCombine "TV_new TV_new2" gives %WF%auth_frag_op_valid_1.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF; done.
    }
    iMod (own_update with "TA") as "TA".
    { eapply (gmap_view_alloc _ tid_new (DfracOwn 1) (to_agree 𝓥)); ss.
      { rewrite ?lookup_fmap Hnew //. }
    }
    iDestruct "TA" as "[TA TVS_new]".
    iDestruct "TVS_new" as "[TVS_new TVS_new1]".
    hss_r. steps_r.

    unshelve (force_l (exist _ tid_new _)).
    { ss; rewrite lookup_fmap Hnew //. }
    steps_l.

    force_l. steps_l. force_l ((tid_new, fn, farg)↑). steps_l. force_l. iFrame "TVS_new1".
    iSplitL "PRE".
    { iExists _; iSplit; eauto. iExists pre, _, _, _; iSplit; eauto. }
    steps_l. spawn. iIntros (nths); steps_l. steps_r. hss.

    forces_l. iFrame "TV". iSplit; eauto. steps_l. step.
    iSplit; eauto.
    iExists [_; _; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists tid_cur, (<[tid_new := (𝓥, nths)]> tids), flag.
    rewrite ?fmap_insert /=; iSplit; eauto; iFrame.
    rewrite -fmap_insert; iFrame "TA".
    iSplitL "TV_new MTVS".
    { iPoseProof (big_sepM_insert with "[TV_new MTVS]") as "$"; last iFrame.
      rewrite lookup_fmap Hnew //.
    }
    { destruct flag.
      { rewrite fmap_insert /= big_sepM_insert; [iFrame|rewrite lookup_fmap Hnew //]. }
      { rewrite ?fmap_delete fmap_insert /= delete_insert_ne; cycle 1.
        { ii; clarify; rewrite lookup_fmap Hnew // in Hlookup. }
        rewrite big_sepM_insert; first iFrame.
        rewrite lookup_delete_ne; [rewrite lookup_fmap Hnew //|ii; clarify].
        rewrite lookup_fmap Hnew // in Hlookup.
      }
    }
  Unshelve. ss.
  (*SLOW*)Admitted.

  Lemma simF_yield : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.yield).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> TVS] ->]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".
    rename _q1 into tid, _q2 into V.

    (* v_tid is set to a correct one *)
    iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TV2 TVSM]".
      { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
      iCombine "TVS TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
      by apply dfrac_valid_own in WF.
    }
    subst.
    hss_l. steps_l. hss.
    
    steps_r. hss_r. steps_r.
    destruct _q as [tid_next Hin].
    force_l (exist _ tid_next Hin). steps_l.

    rewrite /trigger_Yield. steps_l. hss.
    rewrite /SystemI.trigger_Yield. steps_r. hss_r. steps_r. hss_r. steps_r.
    eapply elem_of_dom in Hin. destruct (_ !! tid_next) as [tid_s_next|] eqn : Hnext ; [|inv Hin].

    steps_l. hss. rewrite Hnext. steps_l. steps_r.
    (* splitting thread view for IST *)
    iDestruct "TVS" as "[TVS TVS2]".
    iApply wsim_unfold; iIntros "WS".
    yield "W WS TA TVM TVSM TVS2".
    { iExists [_; _; _], [_; _], st_tgtR, st_tgtR; iSplit; first ss.
      iSplit; eauto.
      iSplit; eauto.
      iExists _, _, _; iSplit; first eauto.
      iFrame. destruct flag; ss.
      rewrite fmap_delete.
      iApply (big_sepM_delete with "[TVSM TVS2]"); [eauto|iFrame].
    }

    clear dependent tids flag.
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".
    steps_l. hss. rewrite /check_internal. steps_l. hss.
    steps_r. hss.

    rename _q into tid.
    iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
    rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[??] [? Hlookup]]; ss; subst.

    iEval (rewrite (big_sepM_delete _ (fst <$> tids) tid); [|rewrite lookup_fmap Hlookup //]; s)
      in "TVSM".
    iDestruct "TVSM" as "[TVS2 TVSM]"; iCombine "TVS TVS2" as "TVS".
    forces_l; iFrame; iSplit; eauto.

    steps_l. step.
    iSplit; eauto.
    iExists [_; _; _], [_; _], _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists _, _, _; iSplit; first eauto.
    iFrame. rewrite fmap_delete //.
  (*SLOW*)Admitted.

  Lemma simF_get_tid : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.get_tid).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> TVS] ->]".
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

    forces_l. iFrame. iSplit; eauto. step. iSplit; first done.
    iExists [_; _; _], [_; _], _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iFrame. done.
  (*SLOW*)Admitted.
End SystemIA.
Section ctx_refines.
  Context `{!crisG Γ Σ α β τ _S _I, !histG, !atomicG, !sysG}.

  (* Scheduler for WM refines its specification when linked to WMM *)
  Lemma ctxr sp_user sp size :
    sp_incl sp_user sp →
    sp_incl (SystemA.sp sp_user ⊤) sp →
    ctx_refines
      (SystemA.t sp_user sp ★ PFMemA.t sp, init_cond size)
      (SystemI.t ★ PFMemA.t sp, emp%I).
  Proof.
    intros ??.
    eapply main_adequacy with (Ist := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq)).
    init_sim.
    { split; ss. iIntros "TA"; iSplit; ss.
      { iPureIntro; split; prove_scope. }
      { iExists 1%positive, {[1%positive := (TView.init size, 0)]}, false; iFrame.
        iSplit; first eauto.
        rewrite delete_singleton fmap_empty //.
      }
    }
    { apply simF__spawn; eauto. }
    { apply simF_spawn; eauto. }
    { apply simF_yield; eauto. }
    { apply simF_get_tid; eauto. }
    { apply simF_alloc; eauto. }
    { apply simF_write; eauto. }
    { apply simF_read; eauto. }
  Qed.
End ctx_refines. End SystemIA.
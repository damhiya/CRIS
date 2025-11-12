Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Section SystemIA.
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

  Lemma simF_write : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.write).
  Proof.
    init_simF.
    steps_l. destruct _q as [[|[|i]] X]; steps_l; rename _q0 into arg'.
    { ss; destruct X as [[[[tid loc] val] ord] V]; ss.
      iDestruct "ASM" as "[[-> [PT TVS]] ->]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".
      iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TV2 TVSM]".
        { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
        iCombine "TVS TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      }
      subst.
      destruct flag.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TVS2 TVSM]"; eauto.
        iCombine "TVS TVS2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      }
      steps_r. hss_r. steps_r. rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 0 _). forces_r.
      instantiate (1 := (_, loc, val, ord, V)); ss; iFrame.
      rewrite big_sepM_delete //. iDestruct "TVM" as "[$ TVM]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[%V' [[-> %] [↦ TV]]] ->]".
      iCombine "TA" "TVS" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA TVS]". 
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.
      iSplit; eauto.
      iExists [_; _; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[? tid_s] [? Hlookup]]; ss; subst.
      iExists tid_cur, (<[tid_cur := (V', tid_s)]> tids), _; iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite fmap_insert /=; iFrame. iSplit; eauto.
      iSplitL "TA TVM TV".
      { rewrite /tview_sys_auth fmap_insert; iFrame.
        rewrite big_sepM_insert_delete; iFrame.
      }
      { rewrite delete_insert_delete //=. }
    }
    { ss. destruct X as [[[[[[[[[[[[tid loc] val] ord] V] γ] ζ'] Vb] tx] ζ] mode] q] tx']; ss.
      iDestruct "ASM" as "[[[-> %] [PT [PTS [TVS ?]]]] ->]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".
      iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TV2 TVSM]".
        { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
        iCombine "TVS TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      }
      subst.
      destruct flag.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TVS2 TVSM]"; eauto.
        iCombine "TVS TVS2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      }
      steps_r. hss_r. steps_r. rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 1 (tid_cur, loc, val, ord, V, γ, ζ', Vb, tx, ζ, mode, q, tx')).
      forces_r. iFrame.
      rewrite big_sepM_delete //. iDestruct "TVM" as "[$ TVM]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[% [% [% [% [% [% [[-> %GRT] [? [? [? [? TV]]]]]]]]]]] ->]".
      iCombine "TA" "TVS" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA TVS]". 
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.
      iSplit; eauto.
      iExists [_; _; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[? tid_s] [? Hlookup]]; ss; subst.
      iExists tid_cur, (<[tid_cur := (_, tid_s)]> tids), _; iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite fmap_insert /=; iFrame. iSplit; eauto.
      iSplitL "TA TVM TV".
      { rewrite /tview_sys_auth fmap_insert; iFrame.
        rewrite big_sepM_insert_delete; iFrame.
      }
      { rewrite delete_insert_delete //=. }
    }
    { destruct i; ss. }
  Qed.
End SystemIA.
Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Section SystemIA.
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
          (YIELD stid)))%I.

  (* Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    λ st_src st_tgt,
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)) (flag : bool),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = [(SystemI.v_tid, tid↑); (SystemI.v_tids, tids'↑)] ∧
         st_src = [(v_internal, flag↑); (SystemI.v_tid, tid↑); (SystemI.v_tids, tids'↑)]⌝ ∗
        (if flag then winv (⊤, ⊤) else True) ∗
        tview_sys_auth (fst <$> tids) ∗
        [∗ map] tid ↦ 𝓥 ∈ fst <$> (if flag then tids else delete tid tids),
          tview_sys_gen (1/2) tid 𝓥)%I. *)

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq).

  Lemma simF_read : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.read).
  Proof.
    init_simF.
    steps_l. destruct _q as [[|[|i]] X]; steps_l; rename _q0 into arg'.
    { ss; destruct X as [[[[[[tid stid] loc] ord] val] q] V]; ss.
      iDestruct "ASM" as "[[-> [PT TV]] ->]".
      iDestruct "TV" as "[TV STV]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
      iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.
      (* destruct flag.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TVS2 TVSM]"; eauto.
        iCombine "TVS TVS2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      } *)
      steps_r. hss_r. steps_r. rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 0 _). forces_r.
      instantiate (1 := (tid_cur, loc, ord, val, q, V)); ss; iFrame.
      iDestruct "TA" as "[TA TVS]".
      rewrite big_sepM_delete //=. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[%v [%V' [[-> %] [↦ tv]]]] ->]".
      iCombine "TA" "TV" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA TidS]". 
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.
      iSplit; eauto.
      iExists [_; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      (* rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[? tid_s] [? Hlookup]]; ss; subst. *)
      iExists tid_cur, (<[tid_cur := (V', stid)]> tids); iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS tv"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
    { ss.
      destruct X as [[[[[[[[[[[tid stid] loc] ord] ζ] ζ'] t0] γ] tx] mode] V] Vb].
      ss; unfold_pre_post.
      iDestruct "ASM" as "[[[-> %] [SN [PTS [Tid STid]]]] ->]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]". hss_r. steps_r.
      iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STid" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.
      (* iDestruct "IST" as "[%tid_cur [%tids [%flag [[-> ->] [W [[TA TVM] TVSM]]]]]]".
      iPoseProof (tview_sys_lookup with "[TA TVM] TVS") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TV2 TVSM]".
        { destruct flag; eauto. by rewrite fmap_delete lookup_delete_ne. }
        iCombine "TVS TV2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      }
      subst. *)
      (* destruct flag.
      { iPoseProof (big_sepM_lookup_acc with "TVSM") as "[TVS2 TVSM]"; eauto.
        iCombine "TVS TVS2" gives %[WF _]%gmap_view.gmap_view_frag_op_valid.
        by apply dfrac_valid_own in WF.
      } *)
      (* steps_r. hss_r. steps_r. *)
      rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 1 (tid_cur, loc, ord, _, _, _, _, _, _, _, _)).
      forces_r. iFrame.
      iDestruct "TA" as "[TA TVS]".
      rewrite big_sepM_delete //. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[% [% [% [% [% [% [% [[-> %] [SN [PTS TV]]]]]]]]]] ->]".
      iCombine "TA" "Tid" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA Tid]". 
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto. iSplit; eauto.
      iPureIntro; des; esplits; eauto.
      step.
      iSplit; eauto.
      iExists [_; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      (* rewrite lookup_fmap_Some in Hlookup; destruct Hlookup as [[? tid_s] [? Hlookup]]; ss; subst. *)
      iExists tid_cur, (<[tid_cur := (_, stid)]> tids); iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS TV"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
    { destruct i; ss. }
  Unshelve. exact 1%Qp.
  Qed.
End SystemIA.
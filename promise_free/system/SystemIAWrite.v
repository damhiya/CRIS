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

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user sp)) Ist) IstEq).

  Lemma simF_write : ISim.sim_fun open SystemA_s SystemI_s init_cond IstFull (Some SystemHdr.write).
  Proof.
    init_simF.
    steps_l. destruct _q as [[|[|i]] X]; steps_l; rename _q0 into arg'.
    { ss; destruct X as [[[[[tid stid] loc] val] ord] V]; ss.
      iDestruct "ASM" as "[[-> [PT Tid]] ->]".
      iDestruct "Tid" as "[Tid STV]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".

      (* Current tid is my tid *)
      iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.

      steps_r. hss_r. steps_r. rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 0 _). forces_r.
      instantiate (1 := (_, loc, val, ord, V)); ss; iFrame.
      iDestruct "TA" as "[TA TVS]".
      rewrite big_sepM_delete //=. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[%V' [[-> %] [↦ TV]]] ->]".
      iCombine "TA" "Tid" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA TidS]".
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.

      (* IST *)
      iSplit; eauto.
      iExists [_; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      iExists tid_cur, (<[tid_cur := (V', stid)]> tids); iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS TV"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
    { ss.
      destruct X as [[[[[[[[[[[[[tid stid] loc] val] ord] V] γ] ζ'] Vb] tx] ζ] mode] q] tx']; ss.
      iDestruct "ASM" as "[[[-> %] [PT [PTS [Tid ?]]]] ->]".
      iDestruct "Tid" as "[Tid STV]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".

      (* Current tid is my tid *)
      iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.

      steps_r. hss_r. steps_r. rewrite /SystemI.get_tid. steps_r. hss_r. steps_r.
      inline_r. force_r (existT 1 (tid_cur, loc, val, ord, V, γ, ζ', Vb, tx, ζ, mode, q, tx')).
      iDestruct "TA" as "[TA TVS]".
      forces_r. iFrame.
      rewrite big_sepM_delete //=. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[[% [% [% [% [% [% [[-> %GRT] [? [? [? [? TV]]]]]]]]]]] ->]".
      iCombine "TA" "Tid" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA Tid]". 
      hss_r. steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.

      (* IST *)
      iSplit; eauto.
      iExists [_; _], [_; _], _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      iExists tid_cur, (<[tid_cur := (_, stid)]> tids); iSplit.
      { iPureIntro; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS TV"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
    { destruct i; ss. }
  Qed.
End SystemIA.
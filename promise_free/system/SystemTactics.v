Require Import CRIS SystemHeader SystemA.

Require Import ltac2_lib.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !sysG}.

  (* Lemma wsim_system_yield
      fl_src fl_tgt Ist r g R_src R_tgt RR p_src p_tgt
      st_src st_tgt itr_src itr_tgt
      (tid : Ident.t) (V : TView.t)
      (E E_src E_tgt : coPset)
      (img_src img_tgt : bool)
      (msk_src msk_tgt : string → bool)
      scp_src sp_src
      scp_tgt sp_tgt :
    (E = if img_tgt then E_src ∖ E_tgt else E_src) →
    E_tgt ⊆ E_src →
    (img_tgt → img_src) →
    msk_src SystemHdr.yield →
    msk_tgt SystemHdr.yield →
    (sp_src SystemHdr.yield = if img_src then Some (SystemA.yield_spec E_src) else None) →
    (sp_tgt SystemHdr.yield = if img_tgt then Some (SystemA.yield_spec E_tgt) else None) →
    Ist st_src st_tgt ∗
    (if ((negb img_tgt) && img_src) then tview_sys tid V else emp) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      (if ((negb img_tgt) && img_src) then tview_sys tid V else emp) -∗
      wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR p_src true
        (st_src, SB.sandbox img_src msk_src scp_src (SModTr.trans sp_src 𝒴) >>= itr_src)
        (st_tgt, itr_tgt ())) ⊢
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR p_src p_tgt
      (st_src, SB.sandbox img_src msk_src scp_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      (st_tgt, SB.sandbox img_tgt msk_tgt scp_tgt (SModTr.trans sp_tgt 𝒴) >>= itr_tgt).
  Proof.
    intros -> ? Himg ?? Hsrc Htgt.
    rewrite /System.yield; unseal "System".
    revert p_src. combine_quant p_tgt.
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' [st_src [st_tgt [p_tgt p_src]]]) "[IST [TV KTR]] %LE /= #CIH".

    unfold_iter_r.
    steps_r. destruct _q.
    { steps_r.
      iApply wsim_unfold; iIntros "W".
      iApply wsim_mono_knowledge; cycle 2.
      { iApply wsim_fold; iFrame "W". iApply ("KTR" with "IST TV"). }
      { ii; iIntros "$ !> //". }
      { ii; iIntros "G"; iPoseProof (LE with "G") as "$"; done. }
    }

    destruct img_tgt; cycle 1.
    { steps_r. rewrite Htgt /=.
      unfold_iter_l. steps_l.
      iApply wsim_progress.
      force_l false. steps_l.
      destruct img_src; cycle 1.
      { rewrite Hsrc /=. steps_l. steps_r.
        call "IST".
        steps_l. hss. steps_l.
        steps_r. hss_r. step_r.
        iApply wsim_base.
        iSpecialize ("CIH" $! _);
          (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s; grind.
        iIntros "W"; iApply "CIH".
        iFrame. iIntros (??) "I _"; iPoseProof ("KTR" with "I") as "KTR".
        iApply (wsim_flag_mon with "[KTR]"); cycle 2.
        { iApply "KTR"; done. }
        all: eauto.
      }
      { rewrite Hsrc /=.
        force_l (tid, V). steps_l. forces_l.
        iFrame "TV". iSplit; eauto.
        steps_l. steps_r.
        call "IST".
        steps_l. iDestruct "ASM" as "[[-> TV] ->]". hss.
        steps_l. steps_r. hss_r. steps_r.
        iApply wsim_base.
        iSpecialize ("CIH" $! _);
          (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s; grind.
        iIntros "W"; iApply "CIH".
        iFrame. iIntros (??) "I TV"; iPoseProof ("KTR" with "I") as "KTR".
        iApply (wsim_flag_mon with "[-]"); cycle 2.
        { iApply "KTR"; done. }
        all: eauto.
      }
    }

    destruct img_src; cycle 1.
    { hexploit Himg; ss. }
    steps_r. rewrite Htgt /=. steps_r.
    iClear "TV"; iDestruct "GRT" as "[[-> TV] _]".

    unfold_iter_l. steps_l. force_l false. steps_l.
    iApply wsim_progress.
    rewrite Hsrc. force_l (_q1, _q2). steps_l.
    rewrite difference_union_L (comm_L union) subseteq_union_1_L //.

    forces_l. iFrame "TV". iSplit; eauto.
    steps_l. call "IST".
    steps_l. iDestruct "ASM" as "[[-> TV] ->]". hss.
    steps_l. forces_r. iFrame "TV"; iSplit; eauto.
    steps_r.
    hss_r. steps_r.
    iApply wsim_base.
    iSpecialize ("CIH" $! _);
      (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s; grind.
    iIntros "W"; iApply "CIH".
    iFrame. iSplit; first done. iIntros (??) "I TV"; iPoseProof ("KTR" with "I") as "KTR".
    iApply (wsim_flag_mon with "[-]"); cycle 2.
    { iApply "KTR"; done. }
    all: eauto.
  (*SLOW*)Qed.

  Lemma wsim_system_yield_src
      fl_src fl_tgt Ist r g R_src R_tgt RR p_src p_tgt
      st_src st_tgt itr_src itr_tgt
      (E : coPset)
      (img_src : bool)
      (msk_src : string → bool)
      scp_src sp_src :
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR true p_tgt
      (st_src, itr_src ())
      (st_tgt, itr_tgt) ⊢
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR p_src p_tgt
      (st_src, SB.sandbox img_src msk_src scp_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      (st_tgt, itr_tgt).
  Proof.
    iIntros "S"; rewrite /System.yield; unseal "System".
    unfold_iter_l; steps_l.
    force_l true; steps_l; done.
  Qed. *)
End wsim.
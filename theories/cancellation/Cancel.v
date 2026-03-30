Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics GSimAux.
Require Import MInline MInlineIntro MInlineElim ElimRel.
Require Import CancelCore CancelPG CancelAG CancelSpawn CancelPre CancelPost CancelYield CancelGetTid.

Module Cancel. Section Cancel.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma cancel_elim md (r_i r_s r_t: Σ) rs_diff srcs tgts cid st ps pt
    (WFS: SMod.cancellable md)
    (REL: Forall3i (thread_rel (SMod.conc_sp_from md) cid) rs_diff srcs tgts)
    (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
    (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
          TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    :
    gsim cancel_eq ps pt
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
        (Any.pair (ModTr.state_encode st) r_s ↑))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod_cancel (SMod.conc_sp_from md) md)) r_i))) (cid, tgts))
        (Any.pair (ModTr.state_encode st) r_t ↑)).
  Proof using.
    ginit. move WFS at top. (* move WF at top. *)
    revert_until r_i. gcofix CIH. i.
    destruct (decide (cid < length srcs)) as [Hcid|]; cycle 1.
    { giter_s. s. rewrite (proj2 (lookup_ge_None srcs cid)); last lia.
      gstep_s. gcNormS. gstep_s. i; ss.
    }
    inversion REL as [Hlenxy [Hlenyz Hrel]].
    exploit (@Forall3i_nth _ _ _ cid); eauto; try lia; clear REL.
    intros [r_diff [i_s [i_t [Hdiff [Hs [Ht Hcidrel]]]]]]; ss.

    assert (Hkey :
      ∀ itr_s itr_t st (r_s r_t: Σ) r_diff,
      ✓ r_s → map_Forall (const is_Some) st →
      (Own r_s ⊢ |==> ([∗ list] i ∈ <[cid := r_diff]> rs_diff, Own i) ∗ Own r_t ∗
        TIDAUTH cid ∗ YIELDAUTH (length (<[cid := r_diff]> rs_diff))) →
      cid < List.length srcs →
      thread_rel (SMod.conc_sp_from md) cid cid r_diff itr_s itr_t →
      gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
        (Any.t * Any.t)%type cancel_eq smj_top smj_top
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
            (SMod.to_mod ∅ (SMod.cancel md))) r_i)))
                (cid, <[cid:=itr_s]> srcs))
        (Any.pair (ModTr.state_encode st) r_s ↑))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod_cancel (SMod.conc_sp_from md) md)) r_i)))
                (cid, <[cid:=itr_t]> tgts))
        (Any.pair (ModTr.state_encode st) r_t ↑))).
    { i. zprogress.
      gbase. eapply CIH; et.
      split.
      { rewrite !length_insert //. }
      split.
      { rewrite !length_insert //. }
      i. destruct (decide (cid = i)); cycle 1.
      { rewrite list_lookup_insert_ne in H4; et.
        rewrite list_lookup_insert_ne in H5; et.
        rewrite list_lookup_insert_ne in H6; et.
      }
      subst. rewrite !list_lookup_insert in H4, H5, H6; et; try lia.
      clarify.
    }

    inversion_clear Hcidrel; subst; ss.

    punfold REL; depdes REL; ii; subst; pclearbot.
    - eapply gsim_Take_src; try apply Hs; ss.
    - eapply gsim_tau_src; try apply Hs; ss.
      eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal|ss].
    - revert Ht; ired; i. eapply gsim_Choose_tgt; try apply Ht; ss.
    - destruct cid; cycle 1.
      { giter_s; rewrite /= Hs; gcNormS; gsteps_s; gstep_s; ss. }
      giter_s; rewrite /= Hs; gcNormS; gsteps_s; ss.
      destruct Qo as [Q|].
      { eapply gsim_Choose_tgt; [revert Ht; ired; intros Ht; eapply Ht|]. intros ret.
        eapply gsim_tau_tgt; first rewrite list_lookup_insert //; try lia.
        rewrite list_insert_insert.
        eapply gsim_Guarantee_tgt; first rewrite list_lookup_insert //; try lia.
        intros rt2 [? Hrt2]. rewrite list_insert_insert.
        eapply gsim_tau_tgt; first rewrite list_lookup_insert //; try lia.
        rewrite list_insert_insert.
        giter_t; rewrite /= list_lookup_insert; last lia; s; gsteps_t.
        gstep. econs. econs. r; esplits; cSimpl.
        apply (Own_pure_soundness r_s); first done.
        { rewrite RS Hrt2; iIntros "> [_ [> [? _] _]]"; iApply RET; eauto. }
      }
      ss.
      giter_t; rewrite /= Ht /=. gsteps_t.
      gstep. econs. econs.
      r. esplits; eauto; cSimpl.
    - giter_s; giter_t; rewrite /= Hs Ht /=.
      gsteps_s; gsteps_t.
      eapply Hkey; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    - revert Ht; ired; i. eapply cancel_core; eauto.
    - revert Ht; ired; i. eapply cancel_pg; eauto.
    - revert Ht; ired; i. eapply cancel_ag; eauto.
    - eapply cancel_yield; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_spawn; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_pre; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_post; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_gettid; eauto. rewrite bind_bind // in Ht.
  (*SLOW*)Qed.


  Lemma cancel_main md rs rt
    (WFS: SMod.cancellable md)
    (WF: Mod.wf (SMod.to_mod ∅ (SMod.cancel md)))
    (VALID: ✓ rs)
    (MAIN : ∃ P Q, (fspec_flat ((SMod.conc_sp_from md).1 !! entry)) P Q ∧
      (Own rs ⊢ |==> (P tt↑ tt↑ ∗ Own rt) ∗ TIDAUTH 0 ∗ YIELDAUTH 1) ∧
      ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝)
    :
    refines_lmod
      (Mod.to_lmod (MInline.inline (SMod.to_mod_cancel (SMod.conc_sp_from md) md)) rt)
      (Mod.to_lmod (MInline.inline (SMod.to_mod ∅ (SMod.cancel md))) rs).
  Proof using.
    r. eapply gsim_adequacy.
    instantiate (1:= smj_top). instantiate (1:= smj_top).
    unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.

    rewrite !lookup_fmap !lookup_omap !lookup_fmap.
    destruct ((SMod.fnsems md) !! entry) eqn: FIND; rewrite ?FIND; cycle 1.
    { s. ired. ginit. gstep_s. ss. }
    s. ired. destruct o; ss; cycle 1.
    { s. ired. ginit. gstep_s. ss. }
    destruct p as [msk [fspo bd]]. s. ired.
    rewrite /ModTr.trans_fnsem /SModTr.trans_fnsem.
    dup WFS; rewrite /SMod.cancellable map_Forall_lookup in WFS.
    hexploit (WFS entry (Some (msk, (fspo, bd)))); eauto; intros [? ?].
    hexploit (SMod.well_scoped_fns md entry (msk, (fspo, bd))); last (intros [? ?]).
    { rewrite lookup_omap FIND //. }
    erewrite !sandbox_inline_commute; et.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ vrs vrt, cancel_eq vrs vrt). i. gstep. econs. econs. destruct SIM. des. et. }

    dup FIND.
    assert (FIND1 : SMod.fnsems (SMod.cancel md) !! entry = Some (Some (msk, (None, bd)))).
    { ss; rewrite lookup_fmap FIND //. }
    eapply MIRed_HoareFun_cancel with (sp:=SMod.conc_sp_from md) (arg:=()↑) in FIND; try by des.
    rewrite FIND.
    eapply MIRed_HoareFun with (fspo:=None) (sp:=∅) (arg:=()↑) in FIND1; try by des.
    rewrite FIND1 /=.

    eapply gsim_tau_src; ss; [do 2 f_equal; hnorm_itr|].
    eapply gsim_tau_src; ss; [do 2 f_equal; hnorm_itr|]. ghcNormS. rewrite bind_ret_r.

    destruct fspo as [fsp|]; ss.
    { assert (Hf : (SMod.sp_from md).1 !! entry = Some fsp).
      { rewrite !lookup_omap lookup_fmap lookup_omap FIND0 //. }
      rewrite Hf /= in MAIN. destruct MAIN as [P [Q [Hfsp [Hp Hq]]]].
      eapply gsim_Take_tgt; ss; [do 2 f_equal; hnorm_itr|]. exists (FSpec_mk _ _ Hfsp).
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
      eapply gsim_Take_tgt; ss; [do 2 f_equal; hnorm_itr|]. exists (tt↑).
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
      hexploit (Own_bupd_split); eauto using Hp.
      intros [rs1 [rs2 [Hrs [Hrs1 Hrs2]]]].

      eapply gsim_Assume_tgt; [s; do 2 f_equal; hnorm_itr|]. exists rs1; splits; eauto.
      { eapply (Own_wand_valid rs); eauto; rewrite Hrs; iIntros "> [$ ?] //". }
      { rewrite Hrs1; apply bupd_intro. }
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss. rewrite bind_ret_l.

      gfinal. right.
      rewrite /LMod.prog /LMod.fnsems /Mod.to_lmod.
      eapply cancel_elim with (r_s:=rs) (r_t:=rs1) (rs_diff:=[ε]); eauto.
      { econs; [ss|split; [ss|ss]].
        intros ????; rewrite !list_lookup_singleton; case_match; ss; i; clarify.
        eapply (thread_rel_body (Some Q)); eauto.
        eapply elim_rel_cancel; eauto.
      }
      { hexploit (Mod.nodup_init (SMod.to_mod ∅ (SMod.cancel md))); eauto. inv WF; ss. }
      rewrite Hrs Hrs2; iIntros "> [? [? ?]] !>"; iFrame; s; iSplit; auto; iApply Own_unit.
    }

    eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
    eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.

    gfinal. right.
    rewrite /LMod.prog /LMod.fnsems /Mod.to_lmod.
    eapply cancel_elim with (r_s:=rs) (r_t:=rt) (rs_diff:=[ε]); eauto.
    { econs; [ss|split; [ss|ss]].
      intros ????; rewrite !list_lookup_singleton; case_match; ss; i; clarify.
      eapply (thread_rel_body None); eauto.
      { eapply elim_rel_cancel; eauto. }
      f_equal; grind.
    }
    { hexploit (Mod.nodup_init (SMod.to_mod ∅ (SMod.cancel md))); eauto. inv WF; ss. }
    destruct MAIN as [? [? [? [-> _]]]].
    iIntros "> [[? ?] [? ?]] !>"; iFrame; s.
    iSplit; auto; iApply Own_unit.
    Unshelve. all: eauto.
  (*SLOW*)Qed.
  End Cancel.

  Section Cancel.
    Context `{!crisG Γ Σ α β τ _S _I}.

    Theorem cancellation_prepare (spt sps: specmap) IC (md: SMod.t)
      (CEQ: spt.2 = sps.2)
      (OUT: ∀ fn arg (msk: emask) p, md.(SMod.fnsems) !! fn = Some (Some (msk,p)) →
            ∀ (fc: string), spt.1 !! (fid fc) ≠ sps.1 !! (fid fc) →
            msk _ (subevent _ (Call fc arg)) = false ∧
            msk _ (subevent _ (Spawn fc arg)) = false)
      :
      ctx_refines
        (SMod.to_mod spt md, IC)
        (SMod.to_mod_cancel sps md, IC).
    Proof.
      rewrite -(left_id _ bi_sep IC). eapply ctxr_cond_frameR.
      eapply main_adequacy with (Ist := IstEq).
      cStartModSim; et.
      { destruct Hwf as [Hwf _]. rewrite /Mod.fnsems in Hwf |- *; ss.
        ii. specialize (Hwf i x). revert Hwf H. rewrite !lookup_fmap. i.
        destruct (SMod.fnsems md !! i) eqn: Emd; ss. depdes H. destruct o; ss. et. }

      rewrite /ISim.sim_fun; intros wfs wft; simpl_map. des_ifs; ss.
      rewrite /SMod.to_mod_cancel /SMod.to_mod /Mod.fnsems /sandbox_fnsemmap !lookup_fmap in Heq |- *.
      do 2 (rewrite fmap_Some in Heq; des); subst. destruct x0 as [[msk [fspo fbd]]|]; ss.
      depdes Heq0. rewrite Heq. s. esplits; et.
      iIntros ( arg st_src st_tgt ) "IST"; iApply wsim_isim; rewrite /SB.sandbox_body;
      simpl fst; simpl snd; rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN.
      iDestruct "IST" as "->".

      iStopProof.
      match goal with
        |- ?P ⊢ wsim ?fe_s ?fe_t ?Ist ?E ?g ?r _ _ ?rel _ _ _ _ =>
        assert (HYP: ∀ ps pt st itr, P ⊢ wsim fe_s fe_t Ist E g r _ _ rel ps pt
                (st, ⇓sb(msk) (SModTr._trans sps (Some msk) itr)) (st, ⇓sb(msk) (SModTr._trans spt None itr)))
      end; cycle 1.
      {
        iIntros "_". destruct fspo; cycle 1.
        { cStepsS. cStepsT. iStopProof. eapply HYP. }
        cStepsS. cStepsT. des_if; [| cStepsS; ss].
        cStepsS. case_match; [| cStepsS; ss].
        cStepsS. case_match; [| cStepsS; ss].
        cStepsS. cForceT _q. cStepsT. rewrite H. cStepsT.
        cForcesT. cStepsT. erewrite H0. cForcesT. iFrame.
        cStepsT. iApply wsim_bind. iSplitL "".
        { iStopProof. eapply HYP. }
        iIntros (????) "[-> ->]".
        cStepsT. cStepsS. des_if; [| cStepsS; ss].
        cStepsT. bsimpl. cStepsT. cForceS. cStepsS. bsimpl. cForceS. iFrame.
        cStep. et.
      }

      clear st_tgt. iIntros (????) "_".
      cCoind CIH g __ with ps pt st itr. iIntros "_".
      assert (CASE := case_itrH itr); des; subst.
      - rewrite !SRed._ret. cStep. et.
      - rewrite !SRed._tau. cStepsS. cStepsT. cByCoind CIH. et.
      - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT. cByCoind CIH. et.
      - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT. cByCoind CIH. et.
      - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsT. cForceS. iFrame. cStepsS. cByCoind CIH. et.
      - destruct c.
        + rewrite !SRed._bind !SRed._call. cStepsS. cStepsT.
          case_match eqn: Lsps; cycle 1.
          { case_match eqn: Lspt.
            { hexploit (OUT fn args); et.
              { erewrite Lsps, Lspt. et. }
              intros [Lmsk _]. cStepsS. rewrite Lmsk. cStepsS. ss.
            }
            cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cCall "". iIntros (???) "->". cStepsS. cStepsT. cByCoind CIH. et.
          }
          destruct (spt.1 !! fid fn0) eqn: Lspt; cycle 1.
          { hexploit (OUT fn args); et.
            { erewrite Lsps, Lspt. et. }
            intros [Lmsk _]. rewrite Lmsk. cStepsS. bsimpl. cForceS (). cStepsS. bsimpl.
            cForcesS. cStepsS. bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          destruct (classic (f = f0)) eqn: Ef_f0; cycle 1.
          { hexploit (OUT fn args); et.
            { erewrite Lsps, Lspt. ii. depdes H. et. }
            intros [Lmsk _]. rewrite Lmsk.
            cStepsS. bsimpl. cForceS (). cStepsS. bsimpl. cForcesS. cStepsS.
            bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          subst. case_match eqn: Lmsk; cycle 1.
          { cStepsS. bsimpl. cForceS (). cStepsS. bsimpl. cForcesS. cStepsS.
            bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          cStepS. cStepsT. bsimpl. cStepsT. cForceS _q. cStepsS. bsimpl.
          cStepsT. cForceS _q0. cStepsS. bsimpl.
          cStepsT. cForceS. iFrame. cStepsS. bsimpl. des_if; [|cStepsS; ss].
          cCall "". iIntros (???) "->". cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cForceT _q1. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cForceT. iFrame. cStepsT. cByCoind CIH. et.
        + rewrite !SRed._bind !SRed._spawn. cStepsS. cStepsT. rewrite /SModTr.HoareSpawn.
          case_match eqn: Lsps; cycle 1.
          { destruct (spt.1 !! fid fn0) eqn: Lspt.
            { hexploit (OUT fn args); et.
              { erewrite Lsps, Lspt. et. }
              intros [_ Lmsk]. destruct sps.2; rewrite CEQ.
              - cStepsS. rewrite Lmsk. cStepsS. ss.
              - cStepS. cStepsT. des_if; [| cStepsS; ss].
                cStep. cStepsS. cStepsT. cByCoind CIH. et.
            }
            destruct sps.2; rewrite CEQ.
            - cStepsS. cStepsT. des_if; [|cStepsS; ss].
              cStep. cStepsS. cStepsT. des_if; [|cStepsS; ss].
              cStepsS. cForcesT. iFrame. cStepsT. cByCoind CIH. et.
            - cStepsS. cStepsT. des_if; [|cStepsS; ss].
              cStep. cStepsS. cStepsT. cByCoind CIH. et.
          }
          destruct (spt.1 !! fid fn0) eqn: Lspt; cycle 1.
          { hexploit (OUT fn args); et.
            { erewrite Lsps, Lspt. et. }
            intros [_ Lmsk]. destruct sps.2; rewrite CEQ.
            - cStepsS. bsimpl. cForceS args. cStepsS. rewrite Lmsk. cStepsS. ss.
            - cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          destruct (classic (f = f0)) eqn: EQf_f0; cycle 1.
          { hexploit (OUT fn args); et.
            { erewrite Lsps, Lspt. ii. depdes H. et. }
            intros [_ Lmsk]. destruct sps.2; rewrite CEQ.
            - cStepsS. bsimpl. cForceS args. cStepsS. rewrite Lmsk. cStepsS. ss.
            - cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          subst. destruct sps.2; rewrite CEQ; cycle 1.
          { cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cStep. cStepsS. cStepsT. cByCoind CIH. et.
          }
          cStepsS. cStepsT. bsimpl. cStepsT. cForceS _q. cStepsS. des_if; [|cStepsS; ss].
          cStep. cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cForceT. iFrame. cStepsT. bsimpl.
          cStepsT. cForceS _q0. cStepsS. bsimpl.
          cStepsT. cForceS. iFrame. cStepsS. cByCoind CIH. et.
        + rewrite !SRed._bind !SRed._yield. cStepsS. cStepsT. rewrite /SModTr.HoareYield.
          destruct sps.2; rewrite CEQ.
          * cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cStepsT. cForceS _q. cStepsS. bsimpl.
            cStepsT. cForcesS. iFrame. cStepsS. des_if; [|cStepsS; ss].
            cYield "". iIntros (??) "->". cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cStepsS. cForceT. iFrame. cStepsT. cByCoind CIH. et.
          * cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cYield "". iIntros (??) "->". cStepsS. cStepsT. cByCoind CIH. et.
        + rewrite !SRed._bind !SRed._gettid. cStepsS. cStepsT. rewrite /SModTr.HoareGetTid.
          destruct sps.2; rewrite CEQ.
          * cStepsS. cStepsT. bsimpl.
            cStepsT. cForceS _q. cStepsS. bsimpl.
            cStepsT. cForcesS. iFrame. cStepsS. des_if; [|cStepsS; ss].
            cStep. cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cStepsS. cForceT. iFrame. cStepsT. cByCoind CIH. et.
          * cStepsS. cStepsT. des_if; [|cStepsS; ss].
            cStep. cStepS. cStepsT. cByCoind CIH. et.
      - rewrite !SRed._bind !SRed._pg. destruct s.
        + cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cStepsT. iApply wsim_sput_src. iApply wsim_sput_tgt.
          cStepsS. cStepsT. cByCoind CIH. et.
        + cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cStepsT. iApply wsim_sget_src. iApply wsim_sget_tgt.
          cStepsS. cStepsT. cByCoind CIH. et.
      - rewrite !SRed._bind !SRed._core. destruct e.
        + cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsT. cForceS _q. cStepsS. cByCoind CIH. et.
        + cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStepsS. cForceT _q. cStepsT. cByCoind CIH. et.
        + cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cStep. cStepsS. cStepsT. cByCoind CIH. et.
    Qed.

    Definition init_res : iProp Σ :=
      TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TIDAUTH 0 ∗ YIELDAUTH 1.

    Theorem cancellation md IC Pinit :
      SMod.cancellable md →
      (∃ P Q, (fspec_flat ((SMod.conc_sp_from md).1 !! entry)) P Q ∧
        (Pinit ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤)  ⊢ |==> (P tt↑ tt↑)) ∧
        ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝) →
      refines
        (SMod.to_mod_cancel (SMod.conc_sp_from md) md, IC)
        (SMod.to_mod ∅ (SMod.cancel md), IC ∗ Pinit ∗ init_res)%I.
    Proof using.
      intros Hcancel [P [Q [Hmain [HP HQ]]]].
      etrans; cycle 1. { eapply inline_elim. }
      etrans. { eapply inline_intro. }
      intros Hwfm.
      assert (Hwfc : Mod.wf (SMod.to_mod ∅ (SMod.cancel md))).
      { inv Hwfm; econs; ss.
        revert wf_fns; rewrite !map_Forall_lookup => Hwf i x; specialize (Hwf i).
        rewrite !lookup_fmap in Hwf; rewrite !lookup_fmap.
        destruct (SMod.fnsems md !! i) as [[[? ?]|]|]; s; i; clarify.
        specialize (Hwf None); ss; hexploit Hwf; eauto.
      }
      split.
      { inv Hwfm. econs; eauto. s.
        intros i ? Hl. ss. r in wf_fns. specialize (wf_fns i). ss.
        rewrite !lookup_fmap in Hl, wf_fns. destruct (SMod.fnsems md !! i); ss.
        destruct o; ss; cycle 1.
        { inv Hl. hexploit wf_fns; eauto. }
        inv Hl. destruct p as [msk [fspo bd]]. ss.
      }
      s; intros rs ? Hrs.
      rewrite assoc in Hrs.
      hexploit (Own_bupd_split); eauto using Hrs.
      intros [rt [ra [Hr1 [Hr2 Hr3]]]].
      exists rt. esplits; et.
      { eapply Own_wand_valid; [iIntros "S"; iPoseProof (Hr1 with "S") as ">[$ _]"; done|done]. }
      { rewrite Hr2. eauto. }
      eapply cancel_main; eauto.
      esplits; eauto.
      rewrite Hr1 Hr3.
      iIntros "> [$ [? [? [? [? [$ $]]]]]]".
      iApply HP; iFrame; done.
  (*SLOW*)Qed.

End Cancel. End Cancel.

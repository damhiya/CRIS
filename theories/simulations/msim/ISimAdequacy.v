From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.lsim Require Import LSim LSimMod.
From CRIS.simulations.msim Require Import MSimCommon MSim MSimAdequacy ISim ISimFacts TacticsCommon ITactics SimNotations.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Section ISIM_ADEQUACY.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma ISim_wf contextual ms mt Ist :
    ISim.t contextual ms mt Ist ⊢
      (⌜Mod.wf mt⌝ → ⌜Mod.wf ms⌝).
  Proof.
    rewrite /ISim.t.
    iIntros "SIM %WFT".
    iSpecialize ("SIM" with "[]"); first done.
    iDestruct "SIM" as "[[%SCOPES %NODUP] _]".
    iPureIntro. econs; et.
    eapply submseteq_NoDup; et. apply WFT.
  Qed.
  
  Lemma ISim_dom contextual ms mt Ist :
    ISim.t contextual ms mt Ist ⊢
      (⌜Mod.wf mt⌝ →
       ⌜dom (Mod.fnsems ms) ⊆ dom (Mod.fnsems mt)⌝).
  Proof using.
    eapply entails_pointwise. intros r VALID SIM.
    assert (WFSIM :
      Own r ⊢ ⌜Mod.wf mt⌝ → ⌜Mod.wf ms⌝).
    { rewrite SIM. eapply ISim_wf. }
    iIntros "R %WFT". iStopProof.
    assert (WFS : Mod.wf ms).
    { eapply Own_pure_soundness; et. rewrite WFSIM.
      iIntros "SIM". iApply "SIM". done. }
    assert (DOM : dom (Mod.fnsems ms) ⊆ dom (Mod.fnsems mt)).
    { intros fn [f Hin]%elem_of_dom.
      rewrite elem_of_dom.
      destruct f as [[msk body]|].
      - assert (TGT :
          ∃ ft,
            sandbox_fnsemmap (Mod.fnsems mt) !! fn =
              Some (Some ft)).
        { eapply Own_pure_soundness; et. rewrite SIM /ISim.t.
          iIntros "SIM".
          iSpecialize ("SIM" with "[]"); first done.
          iDestruct "SIM" as "[_ [_ FUNS]]".
          rewrite /ISim.sim_fun.
          iSpecialize ("FUNS" $! fn with "[] []").
          { done. }
          { done. }
          iSpecialize ("FUNS" $! (SB.sandbox_body (msk, body))
            with "[]").
          { iPureIntro.
            rewrite /sandbox_fnsemmap lookup_fmap Hin //. }
          iDestruct "FUNS" as (ft) "[%Hft _]".
          iPureIntro. eauto. }
        destruct TGT as [ft Hft].
        rewrite /sandbox_fnsemmap lookup_fmap in Hft.
        destruct (Mod.fnsems mt !! fn); ss; eauto.
      - exfalso. eapply WFS in Hin. rr in Hin. des; ss. }
    iIntros "_". iPureIntro. exact DOM.
  Qed.

  (* ISim.t implies lsim_mod *)
  Lemma ISim_adequacy
    (ms mt : Mod.t) Ist
    : ISim.t closed ms mt Ist ⊢ lsim_mod ms mt.
  Proof using.
    eapply entails_pointwise. intros r VALID SIM.
    rewrite lsim_mod_unseal.
    eapply Own_general_completeness. cbn.
    intros WFT.
    assert (WFS : Mod.wf ms).
    { eapply Own_pure_soundness; et.
      rewrite SIM. iIntros "SIM".
      iPoseProof (ISim_wf with "SIM") as "WF".
      iApply "WF". done. }
    split; first done.
    intros rt rs WF SUB.
    exists (IstWorld (λ x y,
      (∀ fn, ISim.sim_fun closed ms mt Ist fn) ∗
        winv (∅, ∅) ∗ Ist x y)%I).
    dup WFS. dup WFT. destruct WFS0, WFT0.
    assert (SUB' : Own rs ⊢ |==> Own rt ∗
      ((∀ fn, ISim.sim_fun closed ms mt Ist fn) ∗
        winv (∅, ∅) ∗
        Ist (Mod.initial_st ms) (Mod.initial_st mt))).
    { rewrite SUB SIM /ISim.t.
      iIntros "($ & SIM & WINV)".
      iSpecialize ("SIM" with "[]"); first done.
      iDestruct "SIM" as "[_ [INIT FUNS]]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in SUB' as
      [rrt [rinit [SUBOWN [HRT HINIT]]]]; eauto.
    constructor; ss.
    - eapply interp_inv_intro with (mr := rinit).
      + exact WF.
      + iIntros "H". iMod (SUBOWN with "H") as "[RT INIT]".
        rewrite /ctx_sem /= left_id Own_op.
        iModIntro. iSplitL "INIT"; first done.
        iApply HRT; done.
      + iIntros "INIT". iModIntro.
        iApply HINIT; done.
      + destruct ms; ss; apply nodup_init; eauto.
      + destruct mt; ss; apply nodup_init; eauto.
    - ii; inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite big_opL_app. s. rewrite ?right_id; eauto.
    - intros fn fs; rewrite ?lookup_fmap lookup_omap.
      destruct (_ ms !! fn) as [[[msks its]|]|] eqn : Hms; ss; i; clarify.
      assert (TGT :
        ∃ ft,
          sandbox_fnsemmap (Mod.fnsems mt) !! fn =
            Some (Some ft)).
      { eapply Own_pure_soundness with (a := r); et.
        rewrite SIM /ISim.t.
        iIntros "SIM".
        iSpecialize ("SIM" with "[]"); first done.
        iDestruct "SIM" as "[_ [_ FUNS]]".
        rewrite /ISim.sim_fun.
        iSpecialize ("FUNS" $! fn with "[] []").
        { done. }
        { done. }
        iSpecialize ("FUNS" $! (SB.sandbox_body (msks, its))
          with "[]").
        { iPureIntro.
          rewrite /sandbox_fnsemmap lookup_fmap Hms //. }
        iDestruct "FUNS" as (ft) "[%Hft _]".
        iPureIntro. eauto. }
      destruct TGT as [ft Hft].
      rewrite /sandbox_fnsemmap lookup_fmap in Hft.
      destruct (_ mt !! fn) as [[[mskt itt]|]|] eqn : Hmt; ss;
        clarify.
      eexists (ModTr.trans_fnsem (SB.sandbox_body (mskt, itt))).
      split.
      { rewrite ?lookup_fmap lookup_omap Hmt //. }
      intros tid ??? arg ??. inv SIMMRS.
      eapply msim_adequacy; eauto; cycle 4.
      { apply le_mine_refl. }
      { ginit; cycle 2; i.
        eapply gpaco8_mon with (r := bot8) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd.
        iMod (MR with "H") as "[FUNS [I H]]".
        iDestruct "FUNS" as "#FUNS".
        iPoseProof "FUNS" as "FSIM".
        iEval (rewrite /ISim.sim_fun) in "FSIM".
        iSpecialize ("FSIM" $! fn with "[] []").
        { done. }
        { done. }
        iSpecialize ("FSIM" $! (SB.sandbox_body (msks, its))
          with "[]").
        { iPureIntro.
          rewrite /sandbox_fnsemmap lookup_fmap Hms //. }
        iDestruct "FSIM" as (ft') "[%Hft' Hsim]".
        rewrite /sandbox_fnsemmap lookup_fmap Hmt /= in Hft'.
        clarify.
        rewrite /isim_fsem.
        iSpecialize ("Hsim" $! arg st_src st_tgt with "H").
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
        iPoseProof ("Hsim" with "I") as "ISIM".
        iModIntro. iApply isim_mono; cycle 1; i.
        { iApply isim_ist_frame.
          iSplitL "FUNS". { iFrame "FUNS". }
          iApply isim_ist_frame. iFrame "I' ISIM". }
        { s. iIntros "[FUNS [WINV [EQ IST]]]". iFrame. }
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ ms !! i); ss.
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ mt !! i); ss.
      }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
  Qed.
End ISIM_ADEQUACY.

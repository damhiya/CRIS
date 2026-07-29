From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.lsim Require Import LSim.
From CRIS.simulations.msim Require Import MSimCommon MSim MSimAdequacy ISim ISimFacts TacticsCommon ITactics SimNotations.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Section ISIM_ADEQUACY.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma ISim_wf contextual ms mt cond Ist :
    ISim.t contextual ms mt cond Ist → Mod.wf mt → Mod.wf ms.
  Proof.
    intros [] WFT. econs; et.
    specialize (sim_scopes WFT).
    eapply submseteq_NoDup; et. apply WFT.
  Qed.
  
  Lemma ISim_dom contextual ms mt cond Ist :
    ISim.t contextual ms mt cond Ist →
    Mod.wf mt →
    dom (Mod.fnsems ms) ⊆ dom (Mod.fnsems mt).
  Proof using.
    intros Hsim Hwf fn [? Hin]%elem_of_dom; eapply ISim_wf in Hwf as Hwfsrc; eauto.
    rewrite elem_of_dom.
    destruct (_ mt !! fn) eqn : Ht; ss. exfalso.
    destruct Hsim; hexploit (sim_fnsems Hwf fn); eauto.
    rewrite /ISim.sim_fun ?lookup_fmap /= Hin /=. destruct x; s; i.
    - hexploit H; et. i; des. rewrite Ht in H0. ss.
    - eapply Hwfsrc in Hin. rr in Hin. des; ss.
  Qed.

  (* ISim.t implies lsim_lmod *)
  Lemma ISim_adequacy (ms mt : Mod.t) (rs rt : Σ) (IC : iProp Σ) Ist
      (SUB : Own rs ⊢ |==> Own rt ∗ (IC ∗ winv (∅,∅)))
      (WF : ✓ rs)
      (WFT : Mod.wf mt)
      (SIM : ISim.t closed ms mt IC Ist) :
    lsim_lmod
      (Mod.to_lmod ms rs) (Mod.to_lmod mt rt)
      (IstWorld (λ x y, winv (∅, ∅) ∗ Ist x y)%I).
  Proof using.
    hexploit ISim_wf; eauto; intros WFS.
    dup SIM. dup WFS. dup WFT. destruct SIM0, WFS0, WFT0.
    constructor; ss.
    - ii; inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite big_opL_app. s. rewrite ?right_id; eauto.
    - intros it_src Hsrc; rewrite ?lookup_fmap lookup_omap in Hsrc.
      hexploit (sim_fnsems WFT entry); rewrite /ISim.sim_fun.
      rewrite ?lookup_fmap lookup_omap; destruct (_ ms !! entry) as [[p|]|] eqn : Hsrc2; ss; clarify.
      intros Hsim; hexploit Hsim; eauto; clear Hsim; intros [ft [Htgt Hsim]].
      destruct (_ mt !! entry) as [[pt|]|] eqn : Htgt2; ss; clarify.
      eexists; split; first refl.

      intros arg; exists ε, ε.
      specialize (Hsim arg (Mod.initial_st ms) (Mod.initial_st mt)).
      eapply lsim_mon_rr.
      { instantiate (1:= interp_inv IstTrue). et. }

      exploit Own_bupd_split; et. i; des.
      exploit Own_split; i; des; et.
      { eapply Own_wand_valid, WF. rewrite x0. iIntros ">[_ ?]". et. }

      eapply msim_adequacy; eauto.
      + f_equal. instantiate (1:=(λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms)).
        apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ ms !! i); ss.
      + f_equal. instantiate (1:=(λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt)).
        apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ mt !! i); ss.
      + eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H.
      + eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H.
      + destruct ms; ss; apply nodup_init; eauto.
      + destruct mt; ss; apply nodup_init; eauto.
      + eapply le_mine_refl.
      + ginit. eapply isim_init.
        * iIntros "P". iApply isim_mono; cycle 1; i.
          { iApply isim_ist_frame; et. }
          { instantiate (1:= (ist_with_eq Ist)). s.
            iIntros "[? [? ?]]". iFrame. }
        * instantiate (1:= a0 ⋅ a3). rewrite !Own_op x4 x5.
          iIntros "[H I]".
          iPoseProof (winv_split_empty with "[I]") as "[I I']"; et; iFrame.
          iApply (Hsim with "[H]"); et. iApply sim_initial; done.
        * eauto using iunlift_ibot.
      + rewrite x0 x1 x3 !Own_op -Own_unit. iIntros ">[? [? ?]]"; iFrame. et.
    - intros fn fs; rewrite ?lookup_fmap lookup_omap.
      destruct (_ ms !! _) as [[[msks its]|]|] eqn : Hms; ss; i; clarify.
      hexploit (sim_fnsems WFT (funid fn)); eauto.
      rewrite /ISim.sim_fun ?lookup_fmap Hms /= ?lookup_fmap lookup_omap.
      intros H; hexploit H; clear H; eauto.
      destruct (_ mt !! _) as [[[mskt itt]|]|] eqn : Hmt; try by (i; des; clarify).
      intros [? [? Hsim]]; clarify; ss.
      eexists; split; first done.
      intros tid ??? arg ??. inv SIMMRS. specialize (Hsim arg st_src st_tgt).
      eapply msim_adequacy; eauto; cycle 4.
      { apply le_mine_refl. }
      { ginit; cycle 2; i.
        eapply gpaco8_mon with (r := bot8) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd. iMod (MR with "H") as "[I H]".
        iPoseProof (Hsim with "[H]") as "SIM"; cycle 2; s; et.
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
        iPoseProof ("SIM" with "I") as "SIM".
        iModIntro. iApply isim_mono; cycle 1; i.
        { iApply isim_ist_frame; et. iFrame. }
        { s. iIntros "[? [? ?]]". iFrame. }
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

Require Import Common.

Require Import Mod HMod.
Require Import ModSim HPSimFacts ISimCore.


Section HSSIM_ADEQUACY.

  Context `{Σ : GRA}.
  Notation iProp := (iProp Σ).

  Lemma hssim_wf ms mt cond Ist is_closed
    (SIM: HSSim.t ms mt cond Ist is_closed)
    (WF: HModSem.wf ms)
    :
    HModSem.wf mt.
  Proof.
    inv SIM. econs.
    - eapply sub_perm_nodup; eauto. apply WF.
    - eapply sub_perm_nodup; eauto. apply WF.
  Qed.

  Lemma hssim_match ms mt cond Ist is_closed fn
    (SIM: HSSim.t ms mt cond Ist is_closed)
    (WF: List.NoDup (List.map fst (HModSem.fnsems ms)))
    (IN: In fn (List.map fst (HModSem.fnsems mt)))
    :
    In fn (List.map fst (HModSem.fnsems ms)).
  Proof.
    eapply sub_perm_incl; eauto. apply SIM.
  Qed.
  
  Lemma hssim_adequacy (ms mt : HModSem.t) (rs rm rt : Σ) (IC : iProp) Ist
      (SUB : Own rs ⊢ Own rt ∗ Own rm)
      (WF : ✓ rs)
      (COND : Own rm ⊢ IC)
      (WFS : HModSem.wf ms)
      (WFT : HModSem.wf mt)
      (SIM : HSSim.t ms mt IC Ist true) :
    MSim.t (HModSem.to_mod ms rs) (HModSem.to_mod mt rt).
  Proof.
    inv SIM.
    econs; i; ss.
    - ii; subst; eauto.
    - instantiate (1:= interp_inv Ist).
      inv WF0. econs; eauto.
      iIntros "H". iMod (MR with "H") as "H". iModIntro.
      iApply sim_mon; eauto.
    - instantiate (1:= ε).
      inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite big_opL_app. s. rewrite ?right_id; eauto.
    - exists ε. econs; eauto.
      { iIntros "S"; iPoseProof (SUB with "S") as "[T IC]"; rewrite /ctx_sem /= ?left_id.
        iModIntro; iSplitL "IC"; iFrame.
      }
      { iIntros "M"; iModIntro; iApply sim_initial; iApply COND; done. }
      { eapply ms.(HModSem.nodup_fns). eapply WFS. }
      { eapply mt.(HModSem.nodup_fns). eapply WFT. }
    - move: FIND; rewrite ?alist_find_map_snd /o_map; intros FIND; des_ifs; cycle 1.
      { eapply alist_find_fst_some, sub_perm_incl in Heq0; [|apply sim_match].
        eapply alist_find_fst_in in Heq0. des. rewrite Heq0 in Heq. ss.
      }
      esplits; eauto.
      exploit sim_fnsems; eauto using alist_find_fst_some.
      { apply WFS. }
      { apply WFT. }
      ii. des; subst.
      rewrite Heq in x0. inv x0. inv SIMMRS.
      eapply hpsim_adequacy; eauto; cycle 5.
      { apply le_mine_refl. ii; eauto. }
      { ginit; cycle 2; i.
        eapply gpaco9_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd. iPoseProof (MR with "H") as ">H".
        iModIntro. iApply x1; eauto.
        { eapply HPSim._hpsim_mon. }
        { eapply cpn9_wcompat, HPSim._hpsim_mon. }
      }
      { exact true. }
      { inv WFS. rewrite List.map_map.
        eapply eq_ind; [apply wf_fns|].
        f_equal. extensionalities. destruct H; eauto.
      }
      { inv WFT. rewrite List.map_map.
        eapply eq_ind; [apply wf_fns|].
        f_equal. extensionalities. destruct H; eauto.
      }
      { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
      { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
  Unshelve. apply string_Dec.
  Qed.
  
End HSSIM_ADEQUACY.

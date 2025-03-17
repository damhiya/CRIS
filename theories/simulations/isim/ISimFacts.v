Require Import Common.
Require Import Mod HMod.
Require Import ModSim HPSimFacts ISim.

(* HSIM_ADEQUACY *)

Lemma hsim_wf `{Σ: GRA} contextual ms mt cond Ist
  (SIM: HSim.t contextual ms mt cond Ist)
  (WF: HMod.wf mt)
  :
  HMod.wf ms.
Proof.
  inv SIM. econs.
  - eapply sub_perm_nodup; eauto. apply WF.
  - eapply sub_perm_nodup; eauto. apply WF.
Qed.

Lemma hsim_match `{Σ: GRA} ms mt cond Ist contextual fn
  (SIM: HSim.t contextual ms mt cond Ist)
  (WF: List.NoDup (List.map fst (HMod.fnsems mt)))
  (IN: In fn (List.map fst (HMod.fnsems ms)))
  :
  In fn (List.map fst (HMod.fnsems mt)).
Proof.
  eapply sub_perm_incl; eauto. apply SIM.
Qed.

Lemma hsim_adequacy `{Σ: GRA} (ms mt : HMod.t) (rs rm rt : Σ) (IC : iProp Σ) Ist
    (SUB : Own rs ⊢ Own rt ∗ Own rm)
    (WF : ✓ rs)
    (COND : Own rm ⊢ IC)
    (WFS : HMod.wf ms)
    (WFT : HMod.wf mt)
    (SIM : HSim.t closed ms mt IC Ist) :
  MSim.t (HMod.to_mod ms rs) (HMod.to_mod mt rt).
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
    { eapply ms.(HMod.nodup_fns). eapply WFS. }
    { eapply mt.(HMod.nodup_fns). eapply WFT. }
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
    eapply hpsim_adequacy; eauto; cycle 4.
    { apply le_mine_refl. ii; eauto. }
    { ginit; cycle 2; i.
      eapply gpaco9_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
      eapply isim_init; eauto.
      iIntros "H". iApply isim_upd. iPoseProof (MR with "H") as ">H".
      iModIntro. iApply x1; eauto.
      { eapply HPSim._hpsim_mon. }
      { eapply cpn9_wcompat, HPSim._hpsim_mon. }
    }
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

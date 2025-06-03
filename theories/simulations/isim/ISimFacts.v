Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod HMod.
Require Import ModSim HModSim HModSimFacts ISim ModSimTactics.

(* HSIM_ADEQUACY *)
Lemma Hsim_wf `{Σ: GRA} contextual ms mt cond Ist
  (SIM: HSim.t contextual ms mt cond Ist)
  (WF: HMod.wf mt)
  :
  HMod.wf ms.
Proof.
  inv SIM. dup WF. inv WF. econs.
  - eapply sub_perm_nodup; eauto.
  - eapply sub_perm_nodup; eauto.
Qed.

Lemma Hsim_match `{Σ: GRA} contextual ms mt cond Ist fn
  (SIM: HSim.t contextual ms mt cond Ist)
  (WF: HMod.wf mt)
  (IN: In fn (List.map fst (HMod.fnsems ms)))
  :
  In fn (List.map fst (HMod.fnsems mt)).
Proof.
  dup WF. destruct WF. eapply sub_perm_incl; eauto. apply SIM; et.
Qed.

Lemma Hsim_adequacy `{Σ: GRA} (ms mt : HMod.t) (rs rm rt : Σ) (IC : iProp Σ) Ist
    (SUB : Own rs ⊢ Own rt ∗ Own rm)
    (WF : ✓ rs)
    (COND : Own rm ⊢ IC)
    (WFS : HMod.wf ms)
    (WFT : HMod.wf mt)
    (SIM : HSim.t closed ms mt IC Ist) :
  MSim.t (HMod.to_mod ms rs) (HMod.to_mod mt rt).
Proof.
  inv SIM. dup WFT. destruct WFS, WFT.
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
  - exists ε, ε.
    destruct (o2flat _) eqn: E; cycle 1.
    { s. ginit. step. }

    rewrite /HSim.initial_valid in sim_initial.
    destruct (HMod.initial_code ms); ss. destruct o; ss. inv E.
    destruct (HMod.initial_code mt); ss. destruct o; ss.
    specialize (sim_initial WFT0 arg).

    rewrite /HModTr.trans_ktree.
    eapply sim_itree_mon_rr.
    { instantiate (1:= interp_inv IstTrue). et. }

    assert (NDS:= ms.(HMod.nodup_init)).
    assert (NDT:= mt.(HMod.nodup_init)).
    
    eapply hsim_adequacy; et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (HMod.fnsems ms)).
      rewrite map_map fst_map_snd. et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (HMod.fnsems mt)).
      rewrite map_map fst_map_snd. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + eapply le_mine_refl. et.
    + ginit. eapply isim_init; eauto using iunlift_ibot.
      iIntros "H". iApply sim_initial; et. rewrite -COND. et.
    + rewrite SUB !Own_op -!Own_unit. iIntros "[? ?]"; iFrame. et.
  - move: FIND; rewrite ?alist_find_map_snd /o_map; intros FIND.
    clear sim_initial. des_ifs; cycle 1.
    { eapply alist_find_fst_some, sub_perm_incl in Heq0; [|apply sim_match]; et.
      eapply alist_find_fst_in in Heq0. des. rewrite Heq0 in Heq. ss.
    }
    esplits; eauto.
    exploit sim_fnsems; eauto using alist_find_fst_some, HMod.wf.
    ii. des; subst.
    rewrite Heq in x0. inv x0. inv SIMMRS.
    eapply hsim_adequacy; eauto; cycle 4.
    { apply le_mine_refl. ii; eauto. }
    { ginit; cycle 2; i.
      eapply gpaco9_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
      eapply isim_init; eauto.
      iIntros "H". iApply isim_upd. iMod (MR with "H") as "H".
      iModIntro. iApply x1; eauto.
    }
    { rewrite List.map_map.
      eapply eq_ind; [apply wf_fns|].
      f_equal. extensionalities. destruct H; eauto.
    }
    { rewrite List.map_map.
      eapply eq_ind; [apply wf_fns0|].
      f_equal. extensionalities. destruct H; eauto.
    }
    { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
    { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
Unshelve. apply string_Dec.
Qed.

Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod.
Require Import LSim MSim MSimFacts ISim LSimTactics.

(* ISIM_ADEQUACY *)
Lemma ISim_wf `{Σ: GRA} contextual ms mt cond Ist
  (SIM: ISim.t contextual ms mt cond Ist)
  (WF: Mod.wf mt)
  :
  Mod.wf ms.
Proof.
  inv SIM. dup WF. inv WF. econs.
  - eapply sub_perm_nodup; eauto.
  - eapply sub_perm_nodup; eauto.
Qed.

Lemma ISim_match `{Σ: GRA} contextual ms mt cond Ist fn
  (SIM: ISim.t contextual ms mt cond Ist)
  (WF: Mod.wf mt)
  (IN: In fn (List.map fst (Mod.fnsems ms)))
  :
  In fn (List.map fst (Mod.fnsems mt)).
Proof.
  dup WF. destruct WF. eapply sub_perm_incl; eauto. apply SIM; et.
Qed.

Lemma ISim_adequacy `{Σ: GRA} (ms mt : Mod.t) (rs rm rt : Σ) (IC : iProp Σ) Ist
    (SUB : Own rs ⊢ Own rt ∗ Own rm)
    (WF : ✓ rs)
    (COND : Own rm ⊢ IC)
    (WFS : Mod.wf ms)
    (WFT : Mod.wf mt)
    (SIM : ISim.t closed ms mt IC Ist) :
  LSim.t (Mod.to_lmod ms rs) (Mod.to_lmod mt rt).
Proof.
  dup SIM. dup WFS. dup WFT. destruct SIM0, WFS0, WFT0.
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
  - rewrite !alist_find_map_snd in FIND.
    destruct (alist_find _ _) eqn: FINDSRC; ss. inv FIND.
    exploit (sim_fnsems WFT None); et. i; des.
    rewrite !alist_find_map_snd x0. s. esplits; et.
    destruct f as [[[img msk] scp] bd].
    destruct ft as [[[img0 msk0] scp0] bd0].
    i. exists ε, ε.

    specialize (x1 arg 1 (Mod.initial_st ms) (Mod.initial_st mt)).
    rewrite /ModTr.trans_ktree /SB.sandbox_body. s.
    eapply lsim_mon_rr.
    { instantiate (1:= interp_inv IstTrue). et. }
    assert (NDS:= ms.(Mod.nodup_init) wf_scopes).
    assert (NDT:= mt.(Mod.nodup_init) wf_scopes0).
    
    eapply msim_adequacy; et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems ms)).
      rewrite map_map fst_map_snd. et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems mt)).
      rewrite map_map fst_map_snd. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + eapply le_mine_refl. et.
    + ginit. eapply isim_init; [eapply x1|..]; eauto using iunlift_ibot.
      erewrite COND. iIntros "H". iSplit; et.
    + rewrite SUB !Own_op -!Own_unit. iIntros "[? ?]"; iFrame. et.
  - move: FIND; rewrite ?alist_find_map_snd /o_map; intros FIND.
    clear sim_initial. des_ifs; cycle 1.
    { eapply alist_find_fst_some, sub_perm_incl in Heq0; [|apply sim_match]; et.
      eapply alist_find_fst_in in Heq0. des. rewrite Heq0 in Heq. ss.
    }
    esplits; eauto.
    exploit sim_fnsems; eauto using alist_find_fst_some, Mod.wf.
    ii. des; subst.
    rewrite Heq in x0. inv x0. inv SIMMRS.
    eapply msim_adequacy; eauto; cycle 4.
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
Unshelve. eapply option_Dec, string_Dec.
Qed.

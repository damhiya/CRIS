Require Import Coqlib sflib ITreelib.
Require Import AList SubPerm.
Require Import PCM IPM.
Require Import Mod HMod.

From ExtLib Require Import
     Data.Map.FMapAList.

Require Import ModSim HPSimFacts ISimCore.


Section HSSIM_ADEQUACY.

  Context `{Σ: GRA.t}.

  Lemma hssim_wf ms mt cond Ist
    (SIM: HSSim.t ms mt cond Ist)
    (WF: HModSem.wf ms)
    :
    HModSem.wf mt.
  Proof.
    inv SIM. econs.
    - eapply in_eqlen_nodup_rev with (l1:= map fst _).
      + rewrite map_length. rewrite sim_length. rewrite map_length. eauto.
      + apply WF.
      + eauto.
    - eapply sub_perm_nodup; eauto. apply WF.
  Qed.

  Lemma hssim_match ms mt cond Ist fn
    (SIM: HSSim.t ms mt cond Ist)
    (WF: List.NoDup (List.map fst (HModSem.fnsems ms)))
    (IN: In fn (List.map fst (HModSem.fnsems mt)))
    :
    In fn (List.map fst (HModSem.fnsems ms)).
  Proof.
    eapply nodup_eqlen_in_rev, IN.
    - rewrite !map_length. eapply SIM.
    - eauto.
    - i. eapply SIM. eauto.
  Qed.
  
  Lemma hssim_adequacy
    (ms mt: HModSem.t) (p q: Σ)
    (IC: iProp) Ist

    (WF: URA.wf (p ⋅ q))
    (COND: IC p)
    (WFS: HModSem.wf ms)
    (WFT: HModSem.wf mt)
    (SIM: HSSim.t ms mt IC Ist)
    :
    MSim.t (HModSem.to_mod ms (p ⋅ q)) (HModSem.to_mod mt q).
  Proof.
    inv SIM.
    econs; i; ss.
    - ii; subst; eauto.
    - instantiate (1:= interp_inv Ist).
      inv WF0. econs; eauto.
      iIntros "H". iMod (MR with "H") as "H". iModIntro.
      iStopProof. eauto.
    - instantiate (1:= ε).
      inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite foldr_app. s. r_solve. eauto.
    - eexists ε. econs; eauto.
      { instantiate (1:= p). s. r_solve. eauto. }
      {
        iIntros "H". iModIntro.
        eapply iProp_Own in COND. iApply sim_initial.
        iApply COND. eauto.
      }
      { eapply ms.(HModSem.nodup_fns). eapply WFS. }
      { eapply mt.(HModSem.nodup_fns). eapply WFT. }
    - rewrite! map_length. eauto.
    - rewrite alist_find_map_snd in *. unfold o_map in *. des_ifs; cycle 1.
      { exfalso.
        eapply alist_find_fst_some, sim_match, alist_find_fst_in in Heq0.
        des. rewrite Heq in Heq0. ss.
      }
      esplits; eauto.
      exploit sim_fnsems; eauto using alist_find_fst_some.
      { apply WFS. }
      { apply WFT. }

      ii. des; subst.
      rewrite Heq in x0. inv x0. inv SIMMRS.
      eapply hpsim_adequacy; eauto; cycle 5.
      { ginit. i.
        eapply gpaco8_mon with (r:= iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd. iPoseProof (MR with "H") as ">H".
        iModIntro. iApply x1; eauto.
      }
      { r_solve; eauto. }
      { r_solve; eauto. }
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
      { apply le_mine_refl. ii; eauto. }
  Qed.
  
End HSSIM_ADEQUACY.

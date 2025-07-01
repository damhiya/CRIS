Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import HMod SMod Sp.
Require Export ISim TacticsCommon ITactics ISimNotations.

Set Implicit Arguments.

(* HModProd *)

Lemma state_scopes_update k v st:
  state_scopes (alist_upd k v st) = state_scopes st.
Proof.
  rewrite /state_scopes -!List.map_map alist_upd_keys. eauto.
Qed.

Lemma isim_refl `{Σ : GRA} r g contextual Ist stid fl_src fl_tgt img msk scp
  ps pt nths st_src st_tgt {R} (it: itree hmodE R)
  (MON: Ist_monotone Ist)
  (EQGET : ∀ nths st_src st_tgt (k: key) (IN: In k.1 scp)
              (NODS: List.NoDup (map fst st_src))
              (NODT: List.NoDup (map fst st_tgt)),
      Ist nths st_src st_tgt -∗ ⌜alist_find k st_src = alist_find k st_tgt⌝)
  (EQSET : ∀ nths st_src st_tgt (k: key) v (IN: In k.1 scp)
              (NODS: List.NoDup (map fst st_src))
              (NODT: List.NoDup (map fst st_tgt)),
      Ist nths st_src st_tgt -∗ Ist nths (alist_upd k v st_src) (alist_upd k v st_tgt))
  :
  Ist nths st_src st_tgt
  ⊢ isim contextual fl_src fl_tgt Ist stid r g (ist_with_eq Ist) ps pt nths
    (st_src, SB.sandbox img msk scp it)
    (st_tgt, SB.sandbox img msk scp it).
Proof.
  revert it.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant nths.
  combine_quant ps.
  combine_quant pt.
  eapply isim_coind. intros g0 a _.
  destruct a as [pt [ps [nths [st_src [st_tgt it]]]]]. s. destruct_quant.
  iIntros "[IST CIH]".
  assert (CASE := case_itrH it); des; subst.
  - istep. iFrame. eauto.
  - isteps_l. isteps_r. iby_coind "CIH"; eauto.
  - destruct img.
    + isteps_l. iforces_r. iFrame. isteps_r. iby_coind "CIH". eauto.
    + rewrite SBRed.bind SBRed.Assume. ired.
      iApply isim_take_src. iIntros (?). ss.
  - isteps_l. isteps_r. istep. isteps_l. isteps_r. iby_coind "CIH". eauto.
  - isteps_r. iforces_l. iFrame. isteps_l. iby_coind "CIH". eauto.
  - depdes c.
    + isteps_l. isteps_r. rewrite SBRed.call. des_ifs.
      * iApply isim_call. iSplitL "IST"; et.
        iIntros (? ? ? ? ? ? ?) "IST".
        iby_coind "CIH". et.
      * isteps_l. ss.
    + isteps_l. isteps_r. rewrite SBRed.spawn. des_ifs.
      * iApply isim_spawn. iby_coind "CIH". iApply MON; [|eauto]; nia.
      * isteps_l. ss.
    + iyield "IST".  eauto. iby_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup. iIntros (? ? ? ?).
      iApply isim_sput_src. iApply isim_sput_tgt.
      iby_coind "CIH". iApply EQSET; et.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst. et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup. iIntros (? ? ? ?).
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iPoseProof (EQGET with "IST") as "%"; et. rewrite H.
      iby_coind "CIH". eauto.
  - destruct e.
    + isteps_r. iforce_l q. isteps_l. iby_coind "CIH". eauto.
    + destruct img.
      * isteps_l. iforce_r q. isteps_r. iby_coind "CIH". eauto.
      * rewrite SBRed.bind SBRed.take. s. des_ifs; isteps_l; ss.
        isteps_l. iforce_r q. isteps_r. iby_coind "CIH". eauto.
    + istep. iby_coind "CIH". eauto.
Qed.

Lemma isim_reflL `{Σ : GRA} contextual Ist fl_src fl_tgt mask scopesL scopesR scopesF (EqL : _ → _ → _ → iProp Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesL)
    (EQGET : ∀ nths st_src st_tgt
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        EqL nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        EqL nths st_src st_tgt -∗ EqL nths0 (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd EqL (IstSB scopesR Ist)) contextual
    (IstProd EqL (IstSB scopesR Ist)) (IstProd EqL (IstSB scopesR Ist))
    (SB.sandbox_body (mask,scopesF,itr)) (SB.sandbox_body (mask,scopesF,itr)).
Proof.
  ii. subst. unfold SB.sandbox_body. s.
  eapply isim_refl; i; et.
  - iIntros "[% [% [% [% [% [EQ [% IST]]]]]]]". des; subst.
    iPoseProof (EQGET with "EQ") as "%".
    { rewrite map_app in NODS0. eapply NoDup_app_remove_r. et. }
    { rewrite map_app in NODT. eapply NoDup_app_remove_r. et. }
    rewrite !alist_find_app_o. des_ifs.
    erewrite alist_find_fst_notin; cycle 1.
    { ii. eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H0. eapply in_map in H. rewrite List.map_map in H. apply H. }
    erewrite alist_find_fst_notin; cycle 1.
    { ii. eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H1. eapply in_map in H. rewrite List.map_map in H. apply H. }
    et.
  - iIntros "[% [% [% [% [% [EQ [% IST]]]]]]]". des; subst.
    iExists (alist_upd k v st_srcL), (alist_upd k v st_tgtL), st_srcR, st_tgtR.
    iSplitR; cycle 1.
    { iFrame. iSplit; eauto. iApply EQSET; eauto.
      - rewrite map_app in NODS0. eapply NoDup_app_remove_r. et.
      - rewrite map_app in NODT. eapply NoDup_app_remove_r. et.
    }
    iPureIntro. esplits; eauto.
    * eapply alist_upd_not_tail. ii.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      eapply H0. eapply in_map in H. rewrite List.map_map in H. apply H.
    * eapply alist_upd_not_tail. ii.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H1. eapply in_map in H. rewrite List.map_map in H. apply H.
Qed.

Lemma isim_reflR `{Σ : GRA} contextual Ist fl_src fl_tgt mask scopesL scopesR scopesF (EqR : _ → _ → _ → iProp Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesR)
    (EQGET : ∀ nths st_src st_tgt, EqR nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqR nths st_src st_tgt -∗ EqR nths0 (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) contextual
    (IstProd (IstSB scopesL Ist) EqR) (IstProd (IstSB scopesL Ist) EqR)
    (SB.sandbox_body (mask,scopesF,itr)) (SB.sandbox_body (mask,scopesF,itr)).
Proof.
  ii. subst. unfold SB.sandbox_body. s.
  eapply isim_refl; i; et.
  - iIntros "[% [% [% [% [% [[% IST] EQ]]]]]]". des; subst.
    iPoseProof (EQGET with "EQ") as "%". subst.
    rewrite alist_find_app_o; des_ifs.
    { exfalso. apply alist_find_fst_some in Heq.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H0. eapply in_map in Heq. rewrite List.map_map in Heq. eauto.
    }
    rewrite alist_find_app_o; des_ifs.
    exfalso. apply alist_find_fst_some in Heq0.
    eapply NoDup_app_disjoint; try apply DISJ; eauto.
    apply H1. eapply in_map in Heq0. rewrite List.map_map in Heq0. eauto.
  - iIntros "[% [% [% [% [% [[% IST] EQ]]]]]]". des; subst.
    iExists st_srcL, st_tgtL, (alist_upd k v st_srcR), (alist_upd k v st_tgtR).
    iSplitR; cycle 1.
    { iFrame. iSplit; eauto. iApply EQSET. eauto. }
    iPureIntro. esplits; eauto.
    * eapply alist_upd_tail. ii. 
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      eapply H0. eapply in_map in H. rewrite List.map_map in H. apply H.
    * eapply alist_upd_tail. ii.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H1. eapply in_map in H. rewrite List.map_map in H. apply H.
Qed.

Lemma hmod_sim_reflL `{Σ : GRA} contextual A B C init_cond scopes Ist
  (SCOPES: scopes = HMod.scopes B)
  (MON : ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
           Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt)
  (SCOPE : sub_perm (HMod.scopes A) scopes)
  (MATCH : sub_perm (List.map fst (HMod.fnsems A)) (List.map fst (HMod.fnsems B)))
  (INIT : HSim.initial_valid A B init_cond (IstSB scopes Ist))
  (SIM : ∀ fn, HSim.sim_fun contextual
                 (HMod.add C A) (HMod.add C B) init_cond
                 (IstProd IstEq (IstSB scopes Ist)) fn)
  :
  HSim.t contextual (HMod.add C A) (HMod.add C B) init_cond
    (IstProd IstEq (IstSB scopes Ist)).
Proof.
  subst. econs; intro WF.
  - ii. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & HL & (% & HR))"; des; subst.
    do 4 (iExists _). iSplitR; eauto.
    iSplitL "HL"; et. iSplit; et. iApply MON; [|eauto]; nia.
  - s. apply sub_perm_cancel_head. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_head. eauto.
  - assert (WFCA: HMod.wf (C ★ A)).
    { destruct WF. econs.
      - eapply sub_perm_nodup; et. s. rewrite !map_app.
        eapply sub_perm_cancel_head. et.
      - eapply sub_perm_nodup; et. s.
        eapply sub_perm_cancel_head. et.
    }
    ii. ss. rewrite alist_find_map alist_find_app_o in H.
    destruct (alist_find None (HMod.fnsems C)) eqn: E; ss.
    destruct (alist_find None (HMod.fnsems B)) eqn: E0; ss.
    destruct (alist_find None (HMod.fnsems A)) eqn: E1; ss.
    { exploit (SIM None); et.
      - eapply WFCA.
      - eapply WF.
      - s. rewrite alist_find_app_o E. et.
      - i; des. rewrite alist_find_app_o E E0 in x0. ss.
    }
    rewrite map_app alist_find_app_o !alist_find_map_snd E. s.
    rewrite E1. s. split; et.
    exploit INIT; try rewrite !alist_find_map_snd.
    + rewrite E0. et.
    + i; des. rewrite x1. iIntros "[% H]". iExists _, _, _, _.
      do 3 (iSplit; et).
  - i. eapply HSim.sim_fun_strong. intro IN.
    rewrite map_app in IN. apply in_app_or in IN. des; cycle 1.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [[[img msk] scp] bd].
    assert (FND : alist_find fn (HMod.fnsems C) = Some (img,msk,scp,bd)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= HMod.wf_fns WFS). s in ND. rewrite map_app in ND.
      eapply NoDup_app_disjoint; try apply ND; eauto.
      eapply alist_find_some, (in_map fst) in FIND. eauto.
    }

    split.
    { eapply alist_find_some_iff; eauto.
      apply in_or_app. left. eapply alist_find_some. eauto. }

    destruct fn; ss.
    { eapply isim_reflL; et; cycle 2.
      + i. iIntros "%". subst. et.
      + apply WFT.
      + etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. erewrite FND. refl.
    }

    ii. iIntros "[% H]". des; subst.
    iApply isim_mono; cycle 1.
    { iApply isim_reflL; et; cycle 3.
      - iExists _, _, _, _. do 3 (iSplit; et).
        + iPureIntro. split; cycle 1.
          * eapply (HMod.well_scoped_init B).
          * etrans; [eapply (HMod.well_scoped_init A)|].
            eapply sub_perm_incl. et.
        + exploit INIT.
          { rewrite alist_find_map_snd.
            destruct (alist_find None (_ B)) eqn: E; et.
            rewrite map_app in NODUPFT.
            eapply NoDup_app_disjoint in NODUPFT; ss.
            - eapply (in_map fst), alist_find_some. et.
            - s. eapply alist_find_some, (in_map fst) in E. et.
          }
          i. des. rewrite x1. iDestruct "H" as "[% H]". et.
      - eapply WFT.
      - ii. exploit (HMod.well_scoped_fns C None).
        { rewrite /fnsems_scopes FND. et. }
        i. et.
      - i. iIntros "%". subst. et.
    }
    i. iIntros "[% H]". subst. et.
Qed.

Lemma hmod_sim_reflR `{Σ : GRA} contextual A B C init_cond scopes Ist
  (SCOPES: scopes = HMod.scopes B)
  (MON : ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
      Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt)
  (SCOPE : sub_perm (HMod.scopes A) scopes)
  (MATCH : sub_perm (List.map fst (HMod.fnsems A)) (List.map fst (HMod.fnsems B)))
  (INIT : HSim.initial_valid A B init_cond (IstSB scopes Ist))
  (SIM : ∀ fn, HSim.sim_fun contextual
                 (HMod.add A C) (HMod.add B C) init_cond
                 (IstProd (IstSB scopes Ist) IstEq) fn)
  :
  HSim.t contextual (HMod.add A C) (HMod.add B C) init_cond (IstProd (IstSB scopes Ist) IstEq).
Proof.
  subst. econs; intro WF.
  - ii. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & HL) & HR)"; des; subst.
    do 4 (iExists _). iSplitR; eauto.
    iSplitL "HL"; et. iSplit; et. iApply MON; [|eauto]; nia.
  - s. apply sub_perm_cancel_tail. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_tail. eauto.
  - assert (WFCA: HMod.wf (A ★ C)).
    { destruct WF. econs.
      - eapply sub_perm_nodup; et. s. rewrite !map_app.
        eapply sub_perm_cancel_tail. et.
      - eapply sub_perm_nodup; et. s.
        eapply sub_perm_cancel_tail. et.
    }
    ii. ss. rewrite alist_find_map alist_find_app_o in H.
    destruct (alist_find None (HMod.fnsems B)) eqn: E; ss.
    destruct (alist_find None (HMod.fnsems C)) eqn: E0; ss.
    destruct (alist_find None (HMod.fnsems A)) eqn: E1; ss.
    { exploit (SIM None); et.
      - eapply WFCA.
      - eapply WF.
      - s. rewrite alist_find_app_o E1. et.
      - i; des. rewrite alist_find_app_o E E0 in x0. ss.
    }
    rewrite map_app alist_find_app_o !alist_find_map_snd E1. s.
    rewrite E0. s. split; et.
    exploit INIT; try rewrite !alist_find_map_snd.
    + rewrite E. et.
    + i; des. rewrite x1. iIntros "[% H]". iExists _, _, _, _.
      do 3 (iSplit; et).
  - i. eapply HSim.sim_fun_strong. intro IN.
    rewrite map_app in IN. apply in_app_or in IN. des.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [[[img msk] scp] bd].
    assert (FND : alist_find fn (HMod.fnsems C) = Some (img,msk,scp,bd)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= HMod.wf_fns WFS). s in ND. rewrite map_app in ND.
      eapply NoDup_app_disjoint; try apply ND; eauto.
      eapply alist_find_some, (in_map fst) in Heq. eauto.
    }

    split.
    { eapply alist_find_some_iff; eauto.
      apply in_or_app. right. eapply alist_find_some. eauto. }

    destruct fn; ss.
    { eapply isim_reflR; et; cycle 2.
      + i. iIntros "%". subst. et.
      + apply WFT.
      + etrans; [|eapply HMod.well_scoped_fns].
        unfold fnsems_scopes. erewrite FND. refl.
    }

    ii. iIntros "[% H]". des; subst.
    iApply isim_mono; cycle 1.
    { iApply isim_reflR; et; cycle 3.
      - iExists _, _, _, _. do 3 (iSplit; et).
        + iPureIntro. split; cycle 1.
          * eapply (HMod.well_scoped_init B).
          * etrans; [eapply (HMod.well_scoped_init A)|].
            eapply sub_perm_incl. et.
        + exploit INIT.
          { rewrite alist_find_map_snd.
            destruct (alist_find None (_ B)) eqn: E; et.
            rewrite map_app in NODUPFT.
            eapply NoDup_app_disjoint in NODUPFT; ss.
            - eapply (in_map fst), alist_find_some. et.
            - s. eapply alist_find_some, (in_map fst) in E. et.
          }
          i. des. rewrite x1. iDestruct "H" as "[% H]". et.
      - eapply WFT.
      - ii. exploit (HMod.well_scoped_fns C None).
        { rewrite /fnsems_scopes FND. et. }
        i. et.
      - i. iIntros "%". subst. et.
    }
    i. iIntros "[% H]". subst. et.
Qed.

Section Proph.
  Context `{Σ: GRA}.

  Variable contextual: contextuality.

  Lemma isim_fsem_proph_to_normal fsp bd_s bd_t msk sp scp fls flt
    (SIM: ∀ arg stid nths st (TID: stid < nths),
        ⊢ isim contextual fls flt IstEq stid ibot ibot (ist_with_eq IstEq) true true nths
          (st, SB.sandbox true  msk scp (SModTr.trans sp      (bd_s arg)))
          (st, SB.sandbox false msk scp (SModTr.trans sp_none (bd_t arg))))
    :
    isim_fsem fls flt IstEq contextual IstEq IstEq
      (SB.sandbox_body (SModTr.trans_ktree sp      (true ,msk,scp, (Some (to_fspec fsp), bd_s))))
      (SB.sandbox_body (SModTr.trans_ktree sp_none (false,msk,scp, (None, fspec_proph fsp bd_t)))).
  Proof.
    ii. iIntros "%". subst.
    rewrite /SB.sandbox_body /SModTr.trans_ktree /fspec_proph. s.
    rewrite /SModTr.HoareFun. s.
    isteps_l. iDestruct "ASM" as "[P %]"; subst.
    iforce_r. iFrame. iIntros (?) "Q". isteps_r.
    iApply isim_bind. iSplitR "Q"; [iApply SIM|]; try nia.
    iIntros (? ? ? ? ? ?) "[% %]". subst.
    isteps_r. iMod ("Q" with "GRT") as "Q".
    iforce_l. iforce_l. iFrame. iSplit; et.
    istep. iSplit; et.
  Qed.
  
End Proph.

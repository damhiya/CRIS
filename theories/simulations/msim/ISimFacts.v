Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimTactics MSim MSimFacts ISim TacticsCommon ITactics ISimNotations.

Set Implicit Arguments.

Section ISIM_FRAME.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

Lemma isim_ist_frame contextual Ist P Rs Rt RR fl_src fl_tgt
    ps pt (sti_s: _ * itree crisE Rs) (sti_t: _ * itree crisE Rt) :
  P ∗ isim contextual fl_src fl_tgt Ist ibot ibot RR ps pt sti_s sti_t ⊢
  isim contextual fl_src fl_tgt
    (λ x y, P ∗ Ist x y)%I ibot ibot (λ x y, P ∗ RR x y) ps pt sti_s sti_t.
Proof using.
  eapply entails_pointwise. i.
  destruct sti_s, sti_t. eapply isim_final.
  destruct (classic (✓ res)); [| gstep; econs; ii; ss].
  eapply Own_split in H; et; des.
  eapply isim_init in H2; et.
  gfinal. right.
  eapply paco8_mon; [eapply msim_ist_frame|]; ss.
  - ginit. eapply gpaco8_mon; eauto using iunlift_ibot.
  - rewrite H Own_op H1. et.
Qed.

End ISIM_FRAME.

Section ISIM_REFL.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

(* Reflexivity of the isim relation *)
Lemma isim_refl r g contextual Ist fl_src fl_tgt img msk scp
  ps pt st_src st_tgt {R} (it: itree crisE R)
  (EQGET : ∀ st_src st_tgt (k: key) (IN: In k.1 scp)
              (NODS: List.NoDup (map fst st_src))
              (NODT: List.NoDup (map fst st_tgt)),
      Ist st_src st_tgt ⊢ ⌜alist_find k st_src = alist_find k st_tgt⌝)
  (EQSET : ∀ st_src st_tgt (k: key) v (IN: In k.1 scp)
              (NODS: List.NoDup (map fst st_src))
              (NODT: List.NoDup (map fst st_tgt)),
      Ist st_src st_tgt ⊢ Ist (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  Ist st_src st_tgt ⊢
  isim contextual fl_src fl_tgt Ist r g (ist_with_eq Ist) ps pt
    (st_src, SB.sandbox img msk scp it)
    (st_tgt, SB.sandbox img msk scp it).
Proof using.
  revert it.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant ps.
  combine_quant pt.
  eapply isim_coind. intros g0 _ CIH [pt [ps [st_src [st_tgt it]]]].
  destruct_quant CIH. iIntros "IST".
  assert (CASE := case_itrH it); des; subst.
  - istep. iFrame. eauto.
  - isteps_l. isteps_r. iby_coind CIH; eauto.
  - destruct img.
    + isteps_l. iforces_r. iFrame. isteps_r. iby_coind CIH. eauto.
    + rewrite SBRed.bind SBRed.Assume. ired.
      iApply isim_take_src. iIntros (?). ss.
  - isteps_l. iforce_r; iFrame. isteps_l. isteps_r. iby_coind CIH. eauto.
  - isteps_r. iforces_l. iFrame. isteps_l. iby_coind CIH. eauto.
  - depdes c.
    + isteps_l. isteps_r. rewrite SBRed.call. des_ifs.
      * iApply isim_call. iSplitL "IST"; et.
        iIntros (???) "IST".
        iby_coind CIH. et.
      * isteps_l. ss.
    + isteps_l. isteps_r. rewrite SBRed.spawn. des_ifs.
      * iApply isim_spawn. iIntros "%"; iby_coind CIH. done.
      * isteps_l. ss.
    + isteps_l. isteps_r. des_ifs.
      * iyield "IST". iby_coind CIH. eauto.
      * isteps_l. ss.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup_src; iIntros (?); iApply isim_sput_src.
      iApply isim_nodup_tgt; iIntros (?); iApply isim_sput_tgt.
      iby_coind CIH. iApply EQSET; et.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst. et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup_src; iIntros (?); iApply isim_sget_src.
      iApply isim_nodup_tgt; iIntros (?); iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iPoseProof (EQGET with "IST") as "%"; et. rewrite H.
      iby_coind CIH. eauto.
  - destruct e.
    + isteps_r. iforce_l _q. isteps_l. iby_coind CIH. eauto.
    + destruct img.
      * isteps_l. iforce_r _q. isteps_r. iby_coind CIH. eauto.
      * rewrite SBRed.bind SBRed.take. s. des_ifs; isteps_l; ss.
        isteps_l. iforce_r _q. isteps_r. iby_coind CIH. eauto.
    + istep. iby_coind CIH. eauto.
Qed.

Lemma isim_reflL contextual Ist fl_src fl_tgt mask scopesL scopesR scopesF (EqL : ist_type Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesL)
    (EQGET : ∀ st_src st_tgt
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        EqL st_src st_tgt ⊢ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ st_src st_tgt (k : key) v
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        EqL st_src st_tgt ⊢ EqL (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd EqL (IstSB scopesR Ist)) contextual
    (IstProd EqL (IstSB scopesR Ist)) (IstProd EqL (IstSB scopesR Ist))
    (SB.sandbox_body (mask,scopesF,itr)) (SB.sandbox_body (mask,scopesF,itr)).
Proof using.
  ii. subst. unfold SB.sandbox_body. s.
  iIntros "IST _". iStopProof.
  eapply isim_refl; i; et.
  - iIntros "[% [% [% [% [% [EQ [% IST]]]]]]]". des; subst.
    iPoseProof (EQGET with "EQ") as "%".
    { rewrite map_app in NODS. eapply NoDup_app_remove_r. et. }
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
      - rewrite map_app in NODS. eapply NoDup_app_remove_r. et.
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

Lemma isim_reflR contextual Ist fl_src fl_tgt mask scopesL scopesR scopesF (EqR : ist_type Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesR)
    (EQGET : ∀ st_src st_tgt, EqR st_src st_tgt ⊢ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ st_src st_tgt (k : key) v,
        EqR st_src st_tgt ⊢ EqR (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) contextual
    (IstProd (IstSB scopesL Ist) EqR) (IstProd (IstSB scopesL Ist) EqR)
    (SB.sandbox_body (mask,scopesF,itr)) (SB.sandbox_body (mask,scopesF,itr)).
Proof using.
  ii. subst. unfold SB.sandbox_body. s.
  iIntros "IST _". iStopProof.
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

Lemma ISim_reflL contextual A B C init_cond scopes (Ist: ist_type Σ)
  (SCOPES: scopes = Mod.scopes B)
  (SCOPE : sub_perm (Mod.scopes A) scopes)
  (MATCH : sub_perm (List.map fst (Mod.fnsems A)) (List.map fst (Mod.fnsems B)))
  (INIT : ISim.initial_valid A B init_cond (IstSB scopes Ist))
  (SIM : ∀ fn, In fn (List.map fst (Mod.fnsems A)) →
    ISim.sim_fun contextual
    (Mod.add C A) (Mod.add C B) init_cond
    (IstProd IstEq (IstSB scopes Ist)) fn)
  :
  ISim.t contextual (Mod.add C A) (Mod.add C B) init_cond
    (IstProd IstEq (IstSB scopes Ist)).
Proof using.
  subst. econs; intro WF.

  - s. apply sub_perm_cancel_head. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_head. eauto.
  - assert (WFCA: Mod.wf (C ★ A)).
    { destruct WF. econs.
      - eapply sub_perm_nodup; et. s. rewrite !map_app.
        eapply sub_perm_cancel_head. et.
      - eapply sub_perm_nodup; et. s.
        eapply sub_perm_cancel_head. et.
    }
    ii. ss. rewrite alist_find_map alist_find_app_o in H.
    destruct (alist_find None (Mod.fnsems C)) eqn: E; ss.
    destruct (alist_find None (Mod.fnsems B)) eqn: E0; ss.
    destruct (alist_find None (Mod.fnsems A)) eqn: E1; ss.
    { exploit (SIM None); et.
      - by eapply alist_find_fst_some.
      - eapply WFCA.
      - eapply WF.
      - s. rewrite alist_find_app_o E. et.
      - i; des. rewrite alist_find_app_o E E0 in x0. ss.
    }
    rewrite map_app alist_find_app_o !alist_find_map_snd E. s.
    rewrite E1. s. split; et.
    exploit INIT; try rewrite !alist_find_map_snd.
    + rewrite E0. et.
    + i; des. rewrite x1. iIntros ">[% H]". iExists _, _, _, _. iModIntro.
      do 3 (iSplit; et).
  - i. eapply ISim.sim_fun_strong. intro IN.
    rewrite map_app in IN. apply in_app_or in IN. des; cycle 1.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [[[img msk] scp] bd].
    assert (FND : alist_find fn (Mod.fnsems C) = Some (img,msk,scp,bd)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= Mod.wf_fns WFS). s in ND. rewrite map_app in ND.
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
      + etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. erewrite FND. refl.
    }

    ii. iIntros "[% H] INV". des; subst.
    iApply isim_mono; cycle 1.
    { exploit INIT.
      i. des.
      iMod (x1 with "H") as "H".
      iApply (isim_reflL with "[H]"); et; cycle 3.
      - iExists _, _, _, _. do 3 (iSplit; et).
      - eapply WFT.
      - ii. exploit (Mod.well_scoped_fns C None).
        { rewrite /fnsems_scopes FND. et. }
        i. et.
      - i. iIntros "%". subst. et.
    }
    i. iIntros "[% H]". subst. et.

  Unshelve.
    rewrite alist_find_map_snd.
    destruct (alist_find None (_ B)) eqn: E; et.
    rewrite map_app in NODUPFT.
    eapply NoDup_app_disjoint in NODUPFT; ss.
    { eapply (in_map fst), alist_find_some. et. }
    { s. eapply alist_find_some, (in_map fst) in E. et. }
Qed.

Lemma ISim_reflR contextual A B C init_cond scopes Ist
    (SCOPES: scopes = Mod.scopes B)
    (SCOPE : sub_perm (Mod.scopes A) scopes)
    (MATCH : sub_perm (List.map fst (Mod.fnsems A)) (List.map fst (Mod.fnsems B)))
    (INIT : ISim.initial_valid A B init_cond (IstSB scopes Ist))
    (SIM : ∀ fn, In fn (map fst (Mod.fnsems A)) →
      ISim.sim_fun contextual
                  (Mod.add A C) (Mod.add B C) init_cond
                  (IstProd (IstSB scopes Ist) IstEq) fn) :
  ISim.t contextual (Mod.add A C) (Mod.add B C) init_cond (IstProd (IstSB scopes Ist) IstEq).
Proof using.
  subst. econs; intro WF.
  - s. apply sub_perm_cancel_tail. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_tail. eauto.
  - assert (WFCA: Mod.wf (A ★ C)).
    { destruct WF. econs.
      - eapply sub_perm_nodup; et. s. rewrite !map_app.
        eapply sub_perm_cancel_tail. et.
      - eapply sub_perm_nodup; et. s.
        eapply sub_perm_cancel_tail. et.
    }
    ii. ss. rewrite alist_find_map alist_find_app_o in H.
    destruct (alist_find None (Mod.fnsems B)) eqn: E; ss.
    destruct (alist_find None (Mod.fnsems C)) eqn: E0; ss.
    destruct (alist_find None (Mod.fnsems A)) eqn: E1; ss.
    { exploit (SIM None); et.
      - by eapply alist_find_fst_some.
      - eapply WFCA.
      - eapply WF.
      - s. rewrite alist_find_app_o E1. et.
      - i; des. rewrite alist_find_app_o E E0 in x0. ss.
    }
    rewrite map_app alist_find_app_o !alist_find_map_snd E1. s.
    rewrite E0. s. split; et.
    exploit INIT; try rewrite !alist_find_map_snd.
    + rewrite E. et.
    + i; des. rewrite x1. iIntros ">[% H]". iExists _, _, _, _. iModIntro.
      do 3 (iSplit; et).
  - i. eapply ISim.sim_fun_strong. intro IN.
    rewrite map_app in IN. apply in_app_or in IN. des.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [[[img msk] scp] bd].
    assert (FND : alist_find fn (Mod.fnsems C) = Some (img,msk,scp,bd)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= Mod.wf_fns WFS). s in ND. rewrite map_app in ND.
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
      + etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. erewrite FND. refl.
    }

    ii. iIntros "[% H] INV". des; subst.
    iApply isim_mono; cycle 1.
    { exploit INIT. i; des.
      iMod (x1 with "H") as "H".
      iApply (isim_reflR with "[H]"); et; cycle 3.
      - iExists _, _, _, _. do 3 (iSplit; et).
      - eapply WFT.
      - ii. exploit (Mod.well_scoped_fns C None).
        { rewrite /fnsems_scopes FND. et. }
        i. et.
      - i. iIntros "%". subst. et.
    }
    i. iIntros "[% H]". subst. et.

  Unshelve.
    rewrite alist_find_map_snd.
    destruct (alist_find None (_ B)) eqn: E; et.
    rewrite map_app in NODUPFT.
    eapply NoDup_app_disjoint in NODUPFT; ss.
    { eapply (in_map fst), alist_find_some. et. }
    { s. eapply alist_find_some, (in_map fst) in E. et. }
Qed.

End ISIM_REFL.

Section ISIM_ADEQUACY.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

Lemma ISim_wf contextual ms mt cond Ist
  (SIM: ISim.t contextual ms mt cond Ist)
  (WF: Mod.wf mt)
  :
  Mod.wf ms.
Proof using.
  inv SIM. dup WF. inv WF. econs.
  - eapply sub_perm_nodup; eauto.
  - eapply sub_perm_nodup; eauto.
Qed.

Lemma ISim_match contextual ms mt cond Ist fn
    (SIM: ISim.t contextual ms mt cond Ist)
    (WF: Mod.wf mt)
    (IN: In fn (List.map fst (Mod.fnsems ms))) :
  In fn (List.map fst (Mod.fnsems mt)).
Proof using.
  dup WF. destruct WF. eapply sub_perm_incl; eauto. apply SIM; et.
Qed.

Lemma ISim_adequacy (ms mt : Mod.t) (rs rt : Σ) (IC : iProp Σ) Ist
    (SUB : Own rs ⊢ |==> Own rt ∗ (IC ∗ winv (∅,∅)))
    (WF : ✓ rs)
    (WFS : Mod.wf ms)
    (WFT : Mod.wf mt)
    (SIM : ISim.t closed ms mt IC Ist) :
  LSim.t (Mod.to_lmod ms rs) (Mod.to_lmod mt rt).
Proof using.
  dup SIM. dup WFS. dup WFT. destruct SIM0, WFS0, WFT0.
  econs; i; ss.
  - ii; subst; eauto.
  (* - instantiate (1:= interp_inv (λ x y, winv (∅, ∅) ∗ Ist x y)%I).
    inv WF0. econs; eauto.
    rewrite MR. iIntros ">[I H]". iFrame. iModIntro.
    iApply sim_mon; eauto. *)
  - instantiate (1 := Σ).
    instantiate (2 := interp_inv (λ x y, winv (∅, ∅) ∗ Ist x y)%I).
    instantiate (1 := ε).
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

    specialize (x1 arg (Mod.initial_st ms) (Mod.initial_st mt)).
    rewrite /ModTr.trans_ktree /SB.sandbox_body. s.
    eapply lsim_mon_rr.
    { instantiate (1:= interp_inv IstTrue). et. }
    assert (NDS:= ms.(Mod.nodup_init) wf_scopes).
    assert (NDT:= mt.(Mod.nodup_init) wf_scopes0).

    exploit Own_bupd_split; et. i; des.
    exploit Own_split; i; des; et.
    { eapply Own_wand_valid, WF. rewrite x2. iIntros ">[_ ?]". et. }
    
    eapply msim_adequacy; et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems ms)).
      rewrite map_map fst_map_snd. et.
    + instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems mt)).
      rewrite map_map fst_map_snd. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + rewrite map_map. f_equal. extensionalities. destruct H. et.
    + eapply le_mine_refl. et.
    + ginit. eapply isim_init.
      * iIntros "P". iApply isim_mono; cycle 1; i.
        { iApply isim_ist_frame; et. }
        { instantiate (1:= (ist_with_eq IstTrue)). s.
          iIntros "[? [? ?]]". iFrame. }
      * instantiate (1:= a0 ⋅ a3). rewrite !Own_op x6 x7.
        iIntros "[H I]".
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et; iFrame.
        iApply (x1 with "[H]"); et. iSplit; et.
      * eauto using iunlift_ibot.
      * eauto using iunlift_ibot.
    + rewrite x2 x3 x5 !Own_op -Own_unit. iIntros ">[? [? ?]]"; iFrame. et.
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
      eapply gpaco8_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
      eapply isim_init; eauto.
      iIntros "H". iApply isim_upd. iMod (MR with "H") as "[I H]".
      iPoseProof (x1 with "[H]") as "SIM"; cycle 2; s; et.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iPoseProof ("SIM" with "I") as "SIM".
      iModIntro. iApply isim_mono; cycle 1; i.
      { iApply isim_ist_frame; et. iFrame. }
      { s. iIntros "[? [? ?]]". iFrame. }
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

End ISIM_ADEQUACY.

Section LAT.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

  Lemma isim_lat_real_to_img peeking fsp lbody_s lbody_t body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQITL: eqit eq false true 
             (SB.sandbox true msk scp (SModTr.trans sp_none lbody_s))
             (SB.sandbox false msk scp (SModTr.trans sp_none lbody_t)))
    (EQIT: eqit eq false true 
             (SB.sandbox true msk scp (SModTr.trans sp_none (body_s arg)))
             (SB.sandbox false msk scp (SModTr.trans sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.trans sp_none (lat_img peeking fsp lbody_s body_s arg)))
      (st, SB.sandbox false msk scp (SModTr.trans sp_none (lat_real peeking fsp lbody_t body_t arg))).
  Proof using.
    iApply isim_reset. clear ps pt. iStopProof. revert st.
    eapply isim_coind. intros g Hg CIH st. iIntros. destruct_quant CIH.
    rewrite /lat_img /lat_real.
    unfold_iter_l. unfold_iter_r. rewrite {1}/lat_img_body {1}/lat_real_body.
    norm_l. norm_r. iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    destruct (peeking); cycle 1.
    {
      isteps_l. isteps_r.
      iApply isim_bind. iSplitL "".
      { iApply isim_eqit_tgt; et.
        iApply isim_refl; et; i; iIntros "%"; subst; et.
      }
      
      iIntros (????) "%"; des; subst.
      isteps_l. isteps_r.
      iforce_r. iFrame. iIntros "GRT".
      iforce_l. iFrame. isteps_l. isteps_r.
      istep; et.
    }

    isteps_r. destruct _q0.
    { iforce_r. iFrame. iIntros "GRT".
      iforce_l true. isteps_l. iforce_l. iFrame. isteps_l. isteps_r.
      iby_coind CIH; et.
    }

    iforce_l false. isteps_l. isteps_r.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    iforce_r. iFrame. iIntros "GRT".
    iforce_l. iFrame. isteps_l. isteps_r.
    istep; et.
  Qed.

  Lemma isim_lat_img_to_hoare fsp body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox true msk scp (SModTr.trans sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox true msk scp (SModTr.trans sp_none (lat_img false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_l. rewrite /lat_img /lat_img_body. unfold_iter_r. isteps_r.
    iDestruct "ASM" as "[P %]"; subst.
    iforces_r. iFrame. isteps_r.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (?????). des; subst.
    isteps_r. iforces_l. iFrame.
    iSplit; et. istep. et.
  Qed.

  Lemma isim_lat_real_to_hoare fsp body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox false msk scp (SModTr.trans sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox false msk scp (SModTr.trans sp_none (lat_real false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_l. rewrite /lat_real /lat_real_body. unfold_iter_r. isteps_r.
    iDestruct "ASM" as "[P %]"; subst.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    iforce_r. iFrame. iIntros "GRT".
    iforces_l. iFrame. iSplit; et.
    isteps_l. isteps_r. istep; et.
  Qed.
  
End LAT.

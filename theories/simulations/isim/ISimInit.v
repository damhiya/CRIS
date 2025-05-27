Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import HMod SMod PMod.
Require Export ISim TacticsCommon ITactics ISimNotations.

Set Implicit Arguments.

(* HModProd *)

Definition IstProd `{Σ : GRA} (IstL IstR : nat -> alist key Any.t -> alist key Any.t -> iProp Σ) :=
  fun nths (st_src st_tgt : alist key Any.t) =>
    (∃ st_srcL st_tgtL st_srcR st_tgtR,
     ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
     IstL nths st_srcL st_tgtL ∗ IstR nths st_srcR st_tgtR)%I.

Definition IstSB `{Σ : GRA} scopes (Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ) :=
  fun nths st_src st_tgt =>
    (⌜incl (state_scopes st_src) scopes ∧
      incl (state_scopes st_tgt) scopes⌝
     ∗ Ist nths st_src st_tgt)%I.

Definition IstEq `{Σ : GRA} : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
  (fun _ st_src st_tgt => ⌜st_src = st_tgt⌝)%I.

Definition IstTrue `{Σ : GRA} : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
  (fun _ _ _ => ⌜True⌝)%I.

Lemma state_scopes_update k v st:
  state_scopes (alist_upd k v st) = state_scopes st.
Proof.
  rewrite /state_scopes -!List.map_map alist_upd_keys. eauto.
Qed.

Lemma isim_refl `{Σ : GRA} r g Ist contextual fl_src fl_tgt mask scopes
  ps pt nths st_src st_tgt {R} (it: itree hmodE R)
  (MON: Ist_monotone Ist)
  (EQGET : ∀ nths st_src st_tgt (k: key) (IN: In k.1 scopes),
      Ist nths st_src st_tgt -∗ ⌜alist_find k st_src = alist_find k st_tgt⌝)
  (EQSET : ∀ nths st_src st_tgt (k: key) v (IN: In k.1 scopes),
      Ist nths st_src st_tgt -∗ Ist nths (alist_upd k v st_src) (alist_upd k v st_tgt))
  :
  Ist nths st_src st_tgt
  ⊢ isim contextual fl_src fl_tgt Ist r g (ist_with_eq Ist) ps pt nths
    (st_src, HModTr.sandbox mask scopes it)
    (st_tgt, HModTr.sandbox mask scopes it).
Proof.
  revert it.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant nths.
  combine_quant ps.
  combine_quant pt.
  eapply isim_coind. intros g0 a _.
  destruct a as [pt [ps [nths [st_src [st_tgt it]]]]]. s.
  iIntros "[IST CIH]".
  assert (CASE := case_itrH it); des; subst.
  - istep. iFrame. eauto.
  - isteps_l. isteps_r. iby_coind "CIH"; eauto.
  - isteps_l. iforces_r. iFrame. isteps_r. iby_coind "CIH". eauto.
  - isteps_l. isteps_r. istep. isteps_l. isteps_r. iby_coind "CIH". eauto.
  - isteps_r. iforces_l. iFrame. isteps_l. iby_coind "CIH". eauto.
  - depdes c.
    + isteps_l. isteps_r. rewrite SBRed.call. des_ifs.
      * iApply isim_call. iSplitL "IST"; et.
        iIntros (? ? ? ? ? ?) "IST".
        iby_coind "CIH". et.
      * isteps_l. ss.
    + isteps_l. isteps_r. rewrite SBRed.spawn. des_ifs.
      * iApply isim_spawn. iby_coind "CIH". iApply MON; [|eauto]; nia.
      * isteps_l. ss.
    + iyield "IST"; eauto. iby_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_sput_src. iApply isim_sput_tgt.
      iby_coind "CIH". iApply EQSET; et.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst. et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iPoseProof (EQGET with "IST") as "%"; et. rewrite H.
      iby_coind "CIH". eauto.
  - destruct e.
    + isteps_r. iforce_l q. isteps_l. iby_coind "CIH". eauto.
    + isteps_l. iforce_r q. isteps_r. iby_coind "CIH". eauto.
    + istep. iby_coind "CIH". eauto.
Qed.

Lemma isim_reflL `{Σ : GRA} Ist contextual fl_src fl_tgt mask scopesL scopesR scopesF (EqL : _ → _ → _ → iProp Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesL)
    (EQGET : ∀ nths st_src st_tgt, EqL nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqL nths st_src st_tgt -∗ EqL nths0 (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd EqL (IstSB scopesR Ist)) contextual
    (HModTr.sandbox_body (mask,scopesF,itr)) (HModTr.sandbox_body (mask,scopesF,itr)).
Proof.
  ii. subst. unfold HModTr.sandbox_body. s.
  eapply isim_refl; i; et.
  - iIntros "[% [% [% [% [% [EQ [% IST]]]]]]]". des; subst.
    iPoseProof (EQGET with "EQ") as "%". subst.
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
    { iFrame. iSplit; eauto. iApply EQSET. eauto. }
    iPureIntro. esplits; eauto.
    * eapply alist_upd_not_tail. ii.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      eapply H0. eapply in_map in H. rewrite List.map_map in H. apply H.
    * eapply alist_upd_not_tail. ii.
      eapply NoDup_app_disjoint; try apply DISJ; eauto.
      apply H1. eapply in_map in H. rewrite List.map_map in H. apply H.
Qed.

Lemma isim_reflR `{Σ : GRA} Ist contextual fl_src fl_tgt mask scopesL scopesR scopesF (EqR : _ → _ → _ → iProp Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesR)
    (EQGET : ∀ nths st_src st_tgt, EqR nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqR nths st_src st_tgt -∗ EqR nths0 (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) contextual
    (HModTr.sandbox_body (mask,scopesF,itr)) (HModTr.sandbox_body (mask,scopesF,itr)).
Proof.
  ii. subst. unfold HModTr.sandbox_body. s.
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

Lemma hmod_sim_reflL `{Σ : GRA} A B C init_cond scopes Ist contextual (EqL : _ → _ → _ → iProp Σ)
  (SCOPES: scopes = HMod.scopes B)
  (EQGET : ∀ nths st_src st_tgt, EqL nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
  (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqL nths st_src st_tgt -∗ EqL nths0 (alist_upd k v st_src) (alist_upd k v st_tgt))  
  (INIT : init_cond -∗
          IstProd EqL (IstSB scopes Ist) 1
                  (HMod.initial_st (HMod.add C A))
                  (HMod.initial_st (HMod.add C B)))
  (MON : ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
      Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt)
  (SCOPE : sub_perm (HMod.scopes A) scopes)
  (MATCH : sub_perm (List.map fst (HMod.fnsems A)) (List.map fst (HMod.fnsems B)))
  (SIM : ∀ fn
          (IN : In fn (List.map fst (HMod.fnsems A))),
        HSim.sim_fun contextual
          (HMod.add C A) (HMod.add C B)
          (IstProd EqL (IstSB scopes Ist)) fn)
  :
  HSim.t contextual (HMod.add C A) (HMod.add C B) init_cond (IstProd EqL (IstSB scopes Ist)).
Proof.
  subst. econs.
  - iApply INIT.
  - i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & HL & (% & HR))"; des; subst.
    do 4 (iExists _). iSplitR; eauto.
    iSplitL "HL".
    + assert (NOTIN: ∃ k, ~ In k (map fst st_srcL) ∧ ~ In k (map fst st_tgtL)).
      { edestruct (string_ex_not_in (map fst (map fst st_srcL) ++ map fst (map fst st_tgtL))) as [sc NOTIN].
        exists (sc, "").
        split; ii; eapply (in_map fst) in H; eapply NOTIN; eauto using in_or_app.
      }
      des.
      iPoseProof (EQSET with "HL") as "HL".
      erewrite !alist_upd_not_in; et.
    + iSplitR; et. iApply MON; [|eauto]; nia.
  - s. apply sub_perm_cancel_head. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_head. eauto.
  - s. i. rewrite map_app in IN. apply in_app_or in IN. des; cycle 1.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [sc f].
    assert (FND : alist_find fn (HMod.fnsems C) = Some (sc,f)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= HMod.wf_fns WFS). s in ND. rewrite map_app in ND.
      eapply NoDup_app_disjoint; try apply ND; eauto.
      eapply alist_find_some, (in_map fst) in FIND. eauto.
    }

    split.
    { eapply alist_find_some_iff; eauto.
      apply in_or_app. left. eapply alist_find_some. eauto. }
    
    eapply isim_reflL; eauto.
    + apply WFT.
    + etrans; [|eapply HMod.well_scoped_fns].
      unfold fnsems_scopes. erewrite FND. refl.
Unshelve. all: exact( ()↑).
Qed.

Lemma hmod_sim_reflR `{Σ : GRA} A B C init_cond scopes Ist contextual (EqR : _ → _ → _ → iProp Σ)
  (SCOPES: scopes = HMod.scopes B)
  (EQGET : ∀ nths st_src st_tgt, EqR nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
  (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqR nths st_src st_tgt -∗ EqR nths0 (alist_upd k v st_src) (alist_upd k v st_tgt))  
  (INIT : init_cond -∗
          IstProd (IstSB scopes Ist) EqR 1
                  (HMod.initial_st (HMod.add A C))
                  (HMod.initial_st (HMod.add B C)))
  (MON : ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
      Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt)
  (SCOPE : sub_perm (HMod.scopes A) scopes)
  (MATCH : sub_perm (List.map fst (HMod.fnsems A)) (List.map fst (HMod.fnsems B)))
  (SIM : ∀ fn
          (IN : In fn (List.map fst (HMod.fnsems A))),
        HSim.sim_fun contextual
          (HMod.add A C) (HMod.add B C)
          (IstProd (IstSB scopes Ist) EqR) fn)
  :
  HSim.t contextual (HMod.add A C) (HMod.add B C) init_cond (IstProd (IstSB scopes Ist) EqR).
Proof.
  subst. econs.
  - iApply INIT.
  - i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & HL) & HR)"; des; subst.
    do 4 (iExists _). iSplitR; eauto.
    iSplitR "HR".
    + iSplitR; et. iApply MON; [|eauto]; nia.    
    + assert (NOTIN: ∃ k, ~ In k (map fst st_srcR) ∧ ~ In k (map fst st_tgtR)).
      { edestruct (string_ex_not_in (map fst (map fst st_srcR) ++ map fst (map fst st_tgtR))) as [sc NOTIN].
        exists (sc, "").
        split; ii; eapply (in_map fst) in H; eapply NOTIN; eauto using in_or_app.
      }
      des.
      iPoseProof (EQSET with "HR") as "HR".
      erewrite !alist_upd_not_in; et.
  - s. apply sub_perm_cancel_tail. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_tail. eauto.
  - s. i. rewrite map_app in IN. apply in_app_or in IN. des.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [sc f].
    assert (FND : alist_find fn (HMod.fnsems C) = Some (sc,f)).
    { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      exfalso. assert (ND:= HMod.wf_fns WFS). s in ND. rewrite map_app in ND.
      eapply NoDup_app_disjoint; try apply ND; eauto.
      eapply alist_find_some, (in_map fst) in Heq. eauto.
    }

    split.
    { eapply alist_find_some_iff; eauto.
      apply in_or_app. right. eapply alist_find_some. eauto. }
    
    eapply isim_reflR; eauto.
    + apply WFT.
    + etrans; [|eapply HMod.well_scoped_fns].
      unfold fnsems_scopes. erewrite FND. refl.
Unshelve. all: exact( ()↑).
Qed.

Section Proph.
  Context `{Σ : GRA}.

  Lemma isim_proph_to_normal fsp fbody_s fbody_t arg mask scopes
    ctx fls flt r g ps pt nths st
    :
    isim ctx fls flt IstEq r g (ist_with_eq IstEq) true true nths
      (st, HModTr.sandbox mask scopes (fbody_s arg))
      (st, HModTr.sandbox mask scopes (fbody_t arg))
    ⊢
    isim ctx fls flt IstEq r g (ist_with_eq IstEq) ps pt nths
      (st, HModTr.sandbox mask scopes
           (SModTr.HoareFun (to_fspec fsp).(precond) (to_fspec fsp).(postcond) fbody_s arg))
      (st, HModTr.sandbox mask scopes (fspec_proph fsp fbody_t arg)).
  Proof.
    rewrite /SModTr.HoareFun /fspec_proph. iIntros "H". s.
    isteps_l. iDestruct "ASM" as "[P %]"; subst.
    iforce_r. iFrame. iIntros (?) "Q". isteps_r.
    iApply isim_bind. iSplitR "Q"; iFrame.
    iIntros (? ? ? ? ?) "[% %]". subst.
    isteps_r. iMod ("Q" with "GRT") as "Q".
    iforce_l. iforce_l. iFrame. iSplit; et.
    istep. iSplit; et.
  Qed.

  Lemma isim_fsem_proph_to_normal fsp fbody_s fbody_t mask sp scopes ctx fls flt
    (SIM: ∀ arg nths st,
        ⊢ isim ctx fls flt IstEq ibot ibot (ist_with_eq IstEq) true true nths
          (st, HModTr.sandbox mask scopes (SModTr.trans sp (fbody_s arg)))
          (st, HModTr.sandbox mask scopes (PModTr.trans (fbody_t arg))))
    :
    isim_fsem fls flt IstEq ctx
      (HModTr.sandbox_body (mask,scopes, SModTr.HoareFun (to_fspec fsp).(precond) (to_fspec fsp).(postcond) (λ arg, SModTr.trans sp (fbody_s arg))))
      (HModTr.sandbox_body (mask,scopes, (λ arg, PModTr.trans (fspec_proph fsp fbody_t arg)))).
  Proof.
    ii. iIntros "%". subst. rewrite /HModTr.sandbox_body. s.
    rewrite PRed.fspec_proph.
    iApply isim_proph_to_normal. iApply SIM.
  Qed.
  
End Proph.

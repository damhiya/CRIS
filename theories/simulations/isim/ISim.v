Require Import Common.

Require Import HMod SMod.
Require Export ISimCore ITacticsCore.

Set Implicit Arguments.

(* LEMMAS *)

(***** Move and rename: HoareCall LEMMAS *****)

(* Goal forall Σ: GRA, ({| environments.env_intuitionistic := (environments.Esnoc environments.Enil (INamed "x") emp%I) ; *)
(*        environments.env_spatial := (environments.Esnoc environments.Enil (INamed "x") emp%I); *)
(*        environments.env_counter := 3%positive |} : environments.envs (iProp Σ)) *)
(*        = *)
(*        {| environments.env_intuitionistic := environments.Enil ; *)
(*        environments.env_spatial := environments.Enil ; *)
(*          environments.env_counter := 3%positive |}. *)

(*   intros. *)
(*   set (X := (emp%I : iProp Σ)) at 2. *)
  
Lemma hcall_clo Σ
  fls flt I contextual r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt
  fn varg arg X (x: shelve__ X) P Q :
  (P x varg arg
  ∗ I nths st_src st_tgt
  ∗ (∀ nths0 st_src0 st_tgt0 vret ret,
      (Q x vret ret ∗ I nths0 st_src0 st_tgt0)
      -∗ @isim Σ contextual fls flt I r g Rs Rt RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt ret)))
  ⊢ @isim _ contextual fls flt I r g Rs Rt RR ps pt nths
      (st_src, HoareCall (mk_fspec P Q) fn varg >>= k_src)
      (st_tgt, trigger (Call fn arg) >>= k_tgt).
Proof.
  iIntros "(P & IST & K)".
  steps_l.
  force_l x.
  force_l arg.
  forces_l. iSplitL "P"; [eauto|]. steps_l.

  call "IST"; [eauto|].
  steps_l. steps_r. iApply "K". iFrame.
Qed.

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

Lemma state_scopes_update k v st:
  state_scopes (alist_upd k v st) = state_scopes st.
Proof.
  rewrite /state_scopes -!List.map_map alist_upd_keys. eauto.
Qed.

Lemma isim_reflR `{Σ : GRA} Ist contextual fl_src fl_tgt scopesL scopesR scopesF (EqR : _ → _ → _ → iProp Σ) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesR)
    (EQGET : ∀ nths st_src st_tgt, EqR nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqR nths st_src st_tgt -∗ EqR nths0 (alist_upd k v st_src) (alist_upd k v st_tgt)) :
  isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) contextual
    (HMod.sandbox_body (scopesF,itr)) (HMod.sandbox_body (scopesF,itr)).
Proof.
  ii. subst. unfold HMod.sandbox_body. s.
  generalize (itr y) as it; clear itr y.
  combine_quant NODD.
  combine_quant NODS.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant nths.
  eapply isim_coind. intros g0 a _. destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
  iIntros "[IST CIH]".
  assert (CASE := case_itrH it); des; subst.
  - step. iFrame. eauto.
  - steps_l. steps_r. by_coind "CIH"; eauto.
  - steps_l. forces_r. iFrame. steps_r. by_coind "CIH". eauto.
  - steps_r. forces_l. iFrame. steps_l. by_coind "CIH". eauto.
  - depdes s.
    + step. by_coind "CIH". iApply IMON; [|eauto]; nia.
    + yield "IST"; eauto. by_coind "CIH". eauto.
  - destruct c. call "IST"; eauto. by_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { steps_r. force_l q. steps_l. by_coind "CIH". eauto. }
      iApply isim_sput_src. iApply isim_sput_tgt.
      by_coind "CIH". unfold IstProd.
      iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & EQR)". des; subst.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
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
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { steps_r. force_l q. steps_l. by_coind "CIH". eauto. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝ ∗
               IstProd (IstSB scopesL Ist) EqR nths st_src st_tgt)%I
        with "[IST]" as "(% & IST)".
      { iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & EQR)". des; subst.
        iPoseProof (EQGET with "EQR") as "%". subst.
        iSplitR; cycle 1.
        { repeat iExists _. iFrame. eauto. }
        rewrite alist_find_app_o; des_ifs.
        { exfalso. apply alist_find_fst_some in Heq0.
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          apply H0. eapply in_map in Heq0. rewrite List.map_map in Heq0. eauto.
        }
        rewrite alist_find_app_o; des_ifs.
        exfalso. apply alist_find_fst_some in Heq1.
        eapply NoDup_app_disjoint; try apply DISJ; eauto.
        apply H1. eapply in_map in Heq1. rewrite List.map_map in Heq1. eauto.
      }
      rewrite H. by_coind "CIH". eauto.
  - destruct e.
    + steps_r. force_l q. steps_l. by_coind "CIH". eauto.
    + steps_l. force_r q. steps_r. by_coind "CIH". eauto.
    + step. by_coind "CIH". eauto.
Unshelve. all : eauto.
{ eapply alist_upd_nodup. eauto. }
{ eapply alist_upd_nodup. eauto. }
Qed.

Lemma hmod_sim_reflR `{Σ : GRA} A B C init_cond scopes Ist contextual
  (SCOPES: scopes = HMod.scopes B)
  (INIT : init_cond -∗
          IstProd (IstSB scopes Ist) IstEq 1
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
          (IstProd (IstSB scopes Ist) IstEq) fn)
  :
  HSim.t contextual (HMod.add A C) (HMod.add B C) init_cond (IstProd (IstSB scopes Ist) IstEq).
Proof.
  subst. econs.
  - iApply INIT.
  - i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)"; des; subst.
    do 4 (iExists _). do 2 (iSplit; eauto). iSplitR; eauto.
    iApply MON; [|eauto]; nia.
  - s. apply sub_perm_cancel_tail. eapply SCOPE.
  - s. rewrite ?map_app. apply sub_perm_cancel_tail. eauto.
  - s. i. rewrite map_app in IN. apply in_app_or in IN. des.
    { eapply SIM; eauto. }
    ii. exists fs. destruct fs as [scp f].
    assert (FND : alist_find fn (HMod.fnsems C) = Some (scp,f)).
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
    + i. unfold IstEq. iIntros "%". subst. eauto.
Qed.

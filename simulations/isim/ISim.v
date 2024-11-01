Require Import Coqlib ITreelib sflib.
Require Import STS.
Require Import Events Behavior.
Require Import Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
From stdpp Require Import coPset gmap.

Require Import HMod SMod.
Require Import SubPerm.

Require Export ISimCore ITacticsCore.

Set Implicit Arguments.

Section LEMMAS.

(***** Move and rename: HoareCall LEMMAS *****)

  Lemma hcall_clo Σ
    fls flt I my_tid r g ps pt {R} RR nths st_src st_tgt k_src k_tgt
    fn varg arg X (x: shelve__ X) P Q
  :
    (P my_tid x varg arg 
      ∗ I nths st_src st_tgt 
      ∗ (∀ nths0 st_src0 st_tgt0 vret ret, 
             (Q my_tid x vret ret ∗ I nths0 st_src0 st_tgt0) 
          -∗ @isim Σ fls flt I my_tid r g R RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt ret)))
  -∗  
    @isim _ fls flt I my_tid r g R RR ps pt nths (st_src, HoareCall (mk_fspec P Q) fn varg >>= k_src) (st_tgt, trigger (Call fn arg) >>= k_tgt).
  Proof.
    iIntros "(P & IST & K)".
    unfold HoareCall. prep. steps_l.
    force_l x.
    force_l arg.
    forces_l. iSplitL "P"; [eauto|].

    call "IST"; [eauto|].
    steps_l. iApply "K". iFrame.
  Qed.

End LEMMAS.

Section HModProd.

  Context `{Σ : GRA.t}.

  Definition IstProd0 (IstL IstR : nat -> alist key Any.t -> alist key Any.t -> iProp) :=
    fun nths (st_src st_tgt : alist key Any.t) =>
      (∃ st_srcL st_tgtL st_srcR st_tgtR,
       ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
       IstL nths st_srcL st_tgtL ∗ IstR nths st_srcR st_tgtR)%I.

  Definition IstProd IstL IstR :=
    fun (sk : Sk.t) => IstProd0 (IstL sk) (IstR sk).

  Definition IstSB0 scopes (Ist : nat -> alist key Any.t -> alist key Any.t -> iProp) :=
    fun nths st_src st_tgt =>
      (⌜incl (state_scopes st_src) scopes ∧
        incl (state_scopes st_tgt) scopes⌝
       ∗ Ist nths st_src st_tgt)%I.

  Definition IstSB ms Ist :=
    fun (sk : Sk.t) => IstSB0 (HMod.scopes ms sk) (Ist sk).

  Definition IstEq0 : nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ st_src st_tgt => ⌜st_src = st_tgt⌝)%I.

  Definition IstEq :=
    fun (sk : Sk.t) => IstEq0.

  Lemma state_scopes_update k v st:
    state_scopes (alist_upd k v st) = state_scopes st.
  Proof.
    rewrite /state_scopes -!List.map_map alist_upd_keys. eauto.
  Qed.
  
  Lemma isim_reflR Ist fl_src fl_tgt scopesL scopesR scopesF (EqR : _->_->_->iProp) itr
    (DISJ : List.NoDup (scopesL ++ scopesR))
    (INCL : incl scopesF scopesR)
    (EQGET : ∀ nths st_src st_tgt,
        EqR nths st_src st_tgt -∗ ⌜st_src = st_tgt⌝)
    (EQSET : ∀ nths st_src st_tgt nths0 (k : key) v,
        EqR nths st_src st_tgt -∗
          EqR nths0 (alist_upd k v st_src) (alist_upd k v st_tgt))
    :
    isim_fsem fl_src fl_tgt (IstProd0 (IstSB0 scopesL Ist) EqR)
      (HModSem.sandbox_body (scopesF,itr)) (HModSem.sandbox_body (scopesF,itr)).
  Proof.
    ii. subst. unfold HModSem.sandbox_body. s.
    generalize (itr y) as it; clear itr y.
    revert NODD. apply combine_quant.
    revert NODS. apply combine_quant.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert nths. apply combine_quant.
    eapply isim_coind. i. destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
    iIntros "(#(_ & CIH) & IST)".
    assert (CASE := case_itrH _ it); des; subst.
    - step. iFrame. eauto.
    - steps_l. steps_r. by_coind "CIH". eauto.
    - steps_l. forces_r. iFrame. by_coind "CIH". eauto.
    - steps_r. forces_l. iFrame. by_coind "CIH". eauto.
    - depdes s.
      + step. by_coind "CIH". iApply IMON; [|eauto]; nia.
      + yield "IST"; eauto. by_coind "CIH". eauto.
      + steps_l. steps_r. by_coind "CIH". eauto.
    - destruct c. call "IST"; eauto. by_coind "CIH". eauto.
    - depdes s.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1.
        { steps_r. force_l q. by_coind "CIH". eauto. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        by_coind "CIH". iClear "CIH". unfold IstProd.
        iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & EQR)". des; subst.
        apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
        iExists st_srcL, st_tgtL, (alist_upd k v st_srcR), (alist_upd k v st_tgtR).
        iSplitR; cycle 1.
        { iFrame. iSplit; eauto. iApply EQSET. eauto. }
        iPureIntro. esplits; eauto.
        * eapply alist_upd_tail. ii. 
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          eapply H0. eapply in_map in H. rewrite map_map in H. apply H.
        * eapply alist_upd_tail. ii.
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          apply H1. eapply in_map in H. rewrite map_map in H. apply H.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { steps_r. force_l q. by_coind "CIH". eauto. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
        iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝ ∗
                 IstProd0 (IstSB0 scopesL Ist) EqR nths st_src st_tgt)%I
          with "[IST]" as "(% & IST)".
        { iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & EQR)". des; subst.
          iPoseProof (EQGET with "EQR") as "%". subst.
          iSplitR; cycle 1.
          { repeat iExists _. iFrame. eauto. }
          rewrite alist_find_app_o; des_ifs.
          { exfalso. apply alist_find_fst_some in Heq0.
            eapply NoDup_app_disjoint; try apply DISJ; eauto.
            apply H0. eapply in_map in Heq0. rewrite map_map in Heq0. eauto.
          }
          rewrite alist_find_app_o; des_ifs.
          exfalso. apply alist_find_fst_some in Heq1.
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          apply H1. eapply in_map in Heq1. rewrite map_map in Heq1. eauto.
        }
        rewrite H. by_coind "CIH". eauto.
    - destruct e.
      + steps_r. force_l q. by_coind "CIH". eauto.
      + steps_l. force_r q. by_coind "CIH". eauto.
      + step. by_coind "CIH". eauto.
  Unshelve. all : eauto.
  { eapply alist_upd_nodup. eauto. }
  { eapply alist_upd_nodup. eauto. }
  Qed.

  Lemma mod_sim_reflR A B C init_cond Ist
    (INIT : ∀ sk, init_cond sk -∗
                    IstProd (IstSB A Ist) IstEq sk 1
                    (HModSem.initial_st (HMod.modsem (HMod.add A C) sk))
                    (HModSem.initial_st (HMod.modsem (HMod.add B C) sk)))
    (MON : ∀ sk nths nths' (LE : nths <= nths') st_src st_tgt,
        Ist sk nths st_src st_tgt -∗ Ist sk nths' st_src st_tgt)
    (SCOPE : ∀ sk, sub_perm (HMod.scopes B sk) (HMod.scopes A sk))
    (LEN : ∀ sk, List.length (HModSem.fnsems (HMod.modsem A sk)) =
                List.length (HModSem.fnsems (HMod.modsem B sk)))
    (MATCH : ∀ sk fn,
           In fn (List.map fst (HModSem.fnsems (HMod.modsem A sk))) →
           In fn (List.map fst (HModSem.fnsems (HMod.modsem B sk))))
    (SIM : ∀ sk fn
            (IN : In fn (List.map fst (HModSem.fnsems (HMod.modsem A sk)))),
          HSSim.sim_fun (HMod.modsem (HMod.add A C) sk) (HMod.modsem (HMod.add B C) sk)
            (IstProd (IstSB A Ist) IstEq sk) fn)
    (SK : HMod.sk A = HMod.sk B)
    :
    HSim.t (HMod.add A C) (HMod.add B C) init_cond (IstProd (IstSB A Ist) IstEq).
  Proof.
    econs; cycle 1.
    { rr. eapply Permutation_app_tail. rewrite SK. refl. }
    econs.
    - apply INIT.
    - i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)"; des; subst.
      do 4 (iExists _). do 2 (iSplit; eauto). iSplitR; eauto.
      iApply MON; [|eauto]; nia.
    - s. apply sub_perm_cancel_tail. eapply SCOPE.
    - s. rewrite !app_length. rewrite LEN. eauto.
    - s. i. rewrite map_app in *. apply in_or_app. apply in_app_or in IN.
      des; eauto.
    - s. i. rewrite map_app in IN. apply in_app_or in IN. des.
      { eapply SIM; eauto. }
      ii. exists fs. destruct fs as [scp f].
      assert (FND : alist_find fn (HModSem.fnsems (HMod.modsem C sk))
                   = Some (scp,f)).
      { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
        exfalso. assert (ND:= HModSem.wf_fns WFS). s in ND. rewrite map_app in ND.
        eapply NoDup_app_disjoint; try apply ND; eauto.
        eapply alist_find_some, (in_map fst) in Heq. eauto.
      }

      split.
      { eapply alist_find_some_iff; eauto.
        apply in_or_app. right. eapply alist_find_some. eauto. }
      
      eapply isim_reflR; eauto.
      + apply WFS.
      + ii. eapply (HMod.modsem C sk). unfold fnsems_scopes. rewrite FND. eauto.
      + i. unfold IstEq, IstEq0. iIntros "%". subst. eauto.
Qed.
  
End HModProd.

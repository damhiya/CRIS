Require Import Coqlib ITreelib sflib.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IModL.
Require Import Any.
Require Import STB ModSim.
Require Import Events HMod HMod2Mod.
Require Import ModSimTactics.

Require Import Relation_Definitions.

Require Import Relation_Operators.

Require Import RelationPairs.

From ExtLib Require Import
     Data.Map.FMapAList.
     
Require Import Red IRed.

Require Import ModSimStrict HPSim.

 (****************************************)

Section HPSIM_ADD_DUMMY.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hmodE Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Variable Ist: nat -> alist key Any.t -> alist key Any.t -> iProp.
  Variable my_tid: nat.
  
  Local Notation _hpsim := (@_hpsim Σ fl_src fl_tgt Ist my_tid).
  Local Notation hpsim := (@hpsim Σ fl_src fl_tgt Ist my_tid).

  Definition itreeH_dummy R (itr itr': itree hmodE R) :=
    exists with_dummy Q i (k: Q -> _),
      itr = (i >>= k) /\
      itr' = (x <- i;; (dummy_term with_dummy) ;;; k x).
  Hint Unfold itreeH_dummy.
            
  Lemma itreeH_dummy_refl R i:
    itreeH_dummy R i i.
  Proof.
    exists false, R, i, (fun x => Ret x).
    unfold dummy_term. grind. esplits; eauto.
    rewrite -{1}[i](bind_ret_r i). f_equal.
    extensionality x. grind.
  Qed.
  Hint Resolve itreeH_dummy_refl.


  Lemma itreeH_dummy_dummy with_dummy Q R i (k: Q -> _):
    itreeH_dummy R (i >>= k) (x <- i;; (dummy_term with_dummy);;; k x).
  Proof.
    r; esplits; eauto.
  Qed.
  Hint Resolve itreeH_dummy_dummy.

  Variant hpsim_dummyC_src (r: forall R (RR: nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop):
    forall R (RR: nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop
  :=
  | hpsim_dummyC_src_intro R RR ps pt nths st_src i_src i_src' st_tgt i_tgt fmr
      (SIM: r R RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
      (DUMMY: itreeH_dummy R i_src i_src')
    :
    hpsim_dummyC_src r R RR ps pt nths (st_src, i_src') (st_tgt, i_tgt) fmr
  .
  
  Lemma hpsim_dummyC_src_mon
        r1 r2
        (LEr: r1 <8= r2)
    :
    hpsim_dummyC_src r1 <8= hpsim_dummyC_src r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma any_neq_unit: Any.t ≠ ()%type.
  Proof.
    assert (exists x y: Any.t, x ≠ y).
    { exists (true↑), (false↑). ii. eapply f_equal in H.
      rewrite !Any.upcast_downcast in H. inv H. }
    ii. rewrite H0 in H. des. apply H. destruct x, y; eauto.
  Qed.
  
  Lemma hpsim_dummyC_src_compatible:
    compatible8 (@_hpsim true) hpsim_dummyC_src.
  Proof.
    econs; eauto using hpsim_dummyC_src_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, nths, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs. ii.
    specialize (IN H). r in DUMMY. des. esplits; eauto.
    destruct IN; i; depdes Heqsti_src Heqsti_tgt;
      esplits; grind; eauto; try by econs; eauto 10.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      rewrite <-x; destruct with_dummy; grind; econs; eauto with imodL.
      econs. ii. esplits; eauto. econs; eauto with imodL.
      i. econs. econs. esplits; eauto. econs; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii; esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace c with (Call fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (@IO I R0 fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace c with (Call fn varg). econs; eauto. eapply K; eauto.
        eexists with_dummy, _, (x<-f varg;; trigger (Guarantee True);;; tau;; ktrH' x), k.
        esplits; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x. destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (Take R0); econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (Choose R0); eauto. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + depdes s; depdes x.
        * econs; eauto.
        * exfalso. apply any_neq_unit; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + depdes s; depdes x.
        * exfalso. apply any_neq_unit; eauto.
        * econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii. esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with (Spawn fn arg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii; esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with (Yield tid). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL. ii; esplits; eauto.
        eapply hpsim_tau_src; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with Tid. econs; eauto.
    - econs; eauto. econs; eauto.
  Qed.

  Lemma hpsim_dummyC_src_spec:
    hpsim_dummyC_src <9= gupaco8 (@_hpsim true) (cpn8 (@_hpsim true)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_src_compatible.
    eapply hpsim_dummyC_src_mon, PR; eauto with paco.
  Qed.

  Variant hpsim_dummyC_tgt (r: forall R (RR: nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop):
    forall R (RR: nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop
  :=
  | hpsim_dummyC_tgt_intro R RR ps pt nths st_src i_src st_tgt i_tgt i_tgt' fmr
      (SIM: r R RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
      (DUMMY: itreeH_dummy R i_tgt i_tgt')
    :
    hpsim_dummyC_tgt r R RR ps pt nths (st_src, i_src) (st_tgt, i_tgt') fmr
  .
  
  Lemma hpsim_dummyC_tgt_mon
        r1 r2
        (LEr: r1 <8= r2)
    :
    hpsim_dummyC_tgt r1 <8= hpsim_dummyC_tgt r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma hpsim_dummyC_tgt_compatible:
    compatible8 (@_hpsim true) hpsim_dummyC_tgt.
  Proof.
    econs; eauto using hpsim_dummyC_tgt_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, nths, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs. ii.
    specialize (IN H). r in DUMMY. des. esplits; eauto.
    destruct IN; i; depdes Heqsti_src Heqsti_tgt;
      esplits; grind; eauto; try by econs; eauto 10.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      rewrite <-x; destruct with_dummy; grind; econs; eauto; imodIntroL.
      econs. ii. esplits; eauto. econs; eauto with imodL.
      i. econs. ii. esplits; eauto. econs; eauto; imodIntroL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii; esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace c with (Call fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (@IO I R0 fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace c with (Call fn varg). econs; eauto. eapply K; eauto.
        eexists with_dummy, _, (x<-f varg;; trigger (Guarantee True);;; tau;; ktrH' x), k.
        esplits; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x. destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (Choose R0); econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace e with (Take R0); eauto. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + depdes s; depdes x.
        * econs; eauto.
        * exfalso. apply any_neq_unit; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + depdes s; depdes x.
        * exfalso. apply any_neq_unit; eauto.
        * econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL. ii. econs. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with (Spawn fn arg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with (Yield tid). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL. ii. esplits; eauto.
        eapply hpsim_tau_tgt; eauto. econs; ii; esplits; eauto.
        econs; eauto.
      + replace s with Tid. econs; eauto.
    - subst. econs; eauto. econs; eauto.
  Qed.

  Lemma hpsim_dummyC_tgt_spec:
    hpsim_dummyC_tgt <9= gupaco8 (@_hpsim true) (cpn8 (@_hpsim true)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_tgt_compatible.
    eapply hpsim_dummyC_tgt_mon, PR; eauto with paco.
  Qed.
  
  Lemma hpsim_le_gpaco r r':
    @hpsim <8= gpaco8 (@_hpsim true) (cpn8 (@_hpsim true)) r r'.
  Proof.
    gcofix CIH. i. punfold PR.
    eapply _hpsim_tarski, PR; i.
    guclo hpsim_wfC_spec. econs; i. specialize (IN H); des.
    destruct IN; des; pclearbot;
      try (by gstep; econs; econs; eauto 7 using @_hpsim' with paco);
      guclo hpsimC_spec; econs; ii; esplits; eauto using @_hpsim' with paco.
    - econs; eauto. guclo hpsim_dummyC_src_spec. econs; eauto.
      exists true. esplits; eauto. grind.
    - econs; eauto. guclo hpsim_dummyC_tgt_spec. econs; eauto.
      exists true. esplits; eauto. grind.
  Qed.

  Corollary hpsim_add_dummy:
    @hpsim <8= paco8 (@_hpsim true) bot8.
  Proof. ginit. i. eapply hpsim_le_gpaco. eauto. Qed.

End HPSIM_ADD_DUMMY.

Section INTERP_RECONF.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hmodE Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable my_tid: nat.

  Definition hp_reconf_eq cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      <<RELr: Own fr ⊢ #=> Own (fr' ⋅ cr)>> /\      
      <<STR: str' = str>>.
  
  Definition hp_reconf_equiv cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      hp_reconf_eq cr (str,fr) (str',fr')
      \/
      (exists st (mr mr': Σ),
       <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
       <<STR: str = Any.pair st mr↑>> /\
       <<STR': str' = Any.pair st mr'↑>>).

  Definition hp_reconf_rel R (eqv: Σ -> _) cr : relation (Any.t * (Σ * R)) :=
    fun '(str,(fr,x)) '(str',(fr',x')) =>
      eqv cr (str,fr) (str',fr') /\ x = x'.

  Lemma hp_reconf_equiv_strong
    cr str str' (fr fr': Σ)
    (EQV: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    (hp_reconf_eq cr (str,fr) (str',fr') /\
     <<FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑>>)
    \/
    (exists st (mr mr': Σ),
     <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
     <<STR: str = Any.pair st mr↑>> /\
     <<STR': str' = Any.pair st mr'↑>>).
  Proof.
    ss. des; subst; [|right]; esplits; eauto.
    destruct (classic (exists stx (mrx:Σ), str = Any.pair stx mrx↑)); eauto.
    des. subst. right. esplits; eauto.
    eapply own_ctx with (ctx := mrx) in RELr. revert RELr. r_solve. i.
    rewrite-> URA.add_comm, (URA.add_comm fr' mrx). eauto.
  Qed.
  
  Lemma hp_reconf_fail
    r R RR nths str i i'
    (FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑)
    :
    paco5 (_sim_strict my_tid) r R RR nths
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i mr)
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i' mr).
  Proof.
    destruct (Any.split str) eqn:STR; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn:T0; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    apply Any.split_pair in STR. apply Any.downcast_upcast in T0.
    exfalso. eapply FAIL. des; subst. eauto.
  Qed.

  Lemma handle_Guarantee_reconf
    P nths str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict my_tid _ (fun _ => hp_reconf_rel _ hp_reconf_equiv cr) nths
      (str, handle_Guarantee P fr)
      (str', handle_Guarantee P fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget_res, mput_res.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1, c2⋅cr).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
      iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. right. esplits; eauto.
    r_solve. eauto.
  Qed.

  Lemma handle_Guarantee_reconf_true
    nths str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict my_tid _ (fun _ => hp_reconf_rel _ hp_reconf_eq cr) nths
      (str, handle_Guarantee True fr)
      (str', handle_Guarantee True fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget_res, mput_res.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1⋅cr, c2).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]".
      rewrite -URA.add_assoc (URA.add_comm cr c2) URA.add_assoc.
      iSplitL "X"; eauto. iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. split; eauto.
  Qed.

  Lemma trigger_agE_simpl R (P: iProp) (e : agE R):
    (trigger (e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma trigger_schE_simpl R (P: iProp) (e : schE R):
    (trigger (|e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.
  
  Lemma trigger_callE_simpl R (P: iProp) (e : callE R):
    (trigger (|e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma trigger_pgE_simpl R (P: iProp) (e : pgE R):
    (trigger (|e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma interp_hp_reconf
    R itrH nths str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict my_tid _ (fun _ => hp_reconf_rel R hp_reconf_equiv cr) nths
      (str, interp_hp itrH fr)
      (str', interp_hp itrH fr').
  Proof.
    (* A workaround for a bug in Qed *)
    assert (BUGFIX := @handle_Guarantee_reconf). move BUGFIX at top.
    
    revert_until Ist. ginit. gcofix CIH; i.
    assert (CASE := case_itrH _ itrH). des; subst.
    - rewrite !interp_hp_ret.
      gstep. econs. rr. esplits; eauto.
    - rewrite-> !interp_hp_tau.
      grind; gstep; econs; i. eauto 10 with paco.
    - rewrite-> !interp_hp_bind, !interp_hp_Assume.
      unfold handle_Assume, assume, mget_res, mput_res.
      grind; gstep; econs; i. exists x.
      grind; gstep; econs; i.
      grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
      { gfinal. right. apply hp_reconf_fail. eauto. }
      rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
      grind; gstep; econs; i. eexists.
      { eapply own_ctx with (ctx := x) in RELr0. rewrite !URA.add_assoc in RELr0.
        eapply own_wf in RELr0; eauto. eapply URA.wf_mon; eauto. }
      grind; gstep; econs; i. eexists. { eauto. }
      grind; gstep; econs; i.
      gfinal. left. eapply CIH. right. esplits; eauto.
      { eapply own_ctx with (ctx := x) in RELr0.
        rewrite !URA.add_assoc in RELr0. eauto using own_wf. }
    - rewrite-> !interp_hp_bind, !interp_hp_Guarantee. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco5_mon_bot; eauto.
        eapply handle_Guarantee_reconf. eauto. }
      i. grind; gstep; econs; i.
      gfinal. left. eapply CIH. destruct v0, v0'. rr in REL. des; subst. ss.
    - destruct s.
      + rewrite-> !interp_hp_bind, !interp_hp_spawn.
        repeat (grind; gstep; econs; i). gbase. eauto.
      + rewrite-> !interp_hp_bind, !interp_hp_yield. grind.
        guclo sim_strict_bindC_spec. econs.
        { gfinal. right. eapply paco5_mon_bot; eauto.
          eapply handle_Guarantee_reconf_true. eauto. }
        i. destruct v0, v0'. repeat (rr in REL; des; subst).
        repeat (grind; gstep; econs; i).
        gfinal. left. eapply CIH. left. s. eauto.
      + rewrite-> !interp_hp_bind, !interp_hp_tid.
        repeat (grind; gstep; econs; i). gbase. eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_call. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco5_mon_bot; eauto.
        eapply handle_Guarantee_reconf_true. eauto. }
      i. destruct v0, v0', c. repeat (rr in REL; des; subst).
      repeat (grind; gstep; econs; i).
      gfinal. left. eapply CIH. left. s. eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_pg.
      destruct s.
      + unfold handle_pgE, mput_kv.
        repeat (grind; gstep; econs; i).
        grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
        { rewrite !Any.pair_split. repeat (grind; gstep; econs).
          gfinal. left. eapply CIH. right. esplits; eauto. }
        destruct (Any.split str) as [[]|] eqn: STR; cycle 1.
        { s. unfold triggerUB. grind. gstep. econs. i. ss. }
        apply Any.split_pair in STR. des; subst.
        repeat (grind; gstep; econs).
        gfinal. left. eapply CIH. econs. econs; eauto.
      + unfold handle_pgE, mget_kv.
        repeat (grind; gstep; econs; i).
        grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
        { rewrite !Any.pair_split. repeat (grind; gstep; econs).
          gfinal. left. eapply CIH. right. esplits; eauto. }
        destruct (Any.split str) as [[]|] eqn: STR; cycle 1.
        { s. unfold triggerUB. grind. gstep. econs. i. ss. }
        apply Any.split_pair in STR. des; subst.
        repeat (grind; gstep; econs).
        gfinal. left. eapply CIH. econs. econs; eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_core.
      destruct e.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + repeat (grind; gstep; econs; i). eauto 10 with paco.
  Qed.

  Lemma hp_fun_tail_reconf
    nths str str' (fr fr' cr: Σ) x
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict my_tid _ (fun _ => eq) nths
      (str, hp_fun_tail (fr,x))
      (str', hp_fun_tail (fr',x)).
  Proof.
    ginit. unfold hp_fun_tail. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst).
    eauto with paco.
  Qed.

  Lemma interp_hp_body_reconf
    itrH nths str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict my_tid _ (fun _ => eq) nths
      (str, interp_hp_body itrH fr)
      (str', interp_hp_body itrH fr').
  Proof.
    ginit. unfold interp_hp_body.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst); cycle 1.
    - gfinal. right. eapply hp_fun_tail_reconf. right. esplits; eauto.
    - gfinal. right. eapply hp_fun_tail_reconf. left. esplits; eauto.
      rr. esplits; eauto.
  Qed.

  Lemma interp_strict_inline_src
    nths itrH ktrH st (fr mr: Σ)
    :
    sim_strict my_tid Any.t (fun _ => eq) nths
      (Any.pair st (fr ⋅ mr)↑, x <- interp_hp_body itrH ε;; tau;; '(rr,rv) <- (tau;; Ret (ε,x));; interp_hp_body (ktrH rv) rr)
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True);;; tau;; ktrH x) fr).
  Proof.
    ginit. guclo sim_strict_transC_spec. econs; cycle 1.
    { gfinal. right. eapply interp_hp_body_reconf with (fr := (ε:Σ)) (cr:=(ε:Σ)).
      right. esplits; eauto. instantiate (1:= fr ⋅ mr). r_solve. eauto. }
    { instantiate (1:= fun _ => eq). i. destruct PR. subst. eauto. }
    unfold interp_hp_body. rewrite !interp_hp_bind.
    grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. apply sim_strict_refl. }
    i. depdes REL. rewrite-> interp_hp_bind, interp_hp_Guarantee.
    destruct v0' as [fr' st']. unfold hp_fun_tail at 1. grind.
    unfold handle_Guarantee, mget_res, mput_res, guarantee, sGet, sPut.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, ε, c1 ⋅ c2).
    grind; gstep; econs; i.
    ss. destruct (Any.split st0') eqn: ST0'; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn: T0; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    apply Any.split_pair in ST0'. rr in ST0'. subst.
    apply Any.downcast_upcast in T0. rr in T0. subst.
    grind; gstep; econs; i. eexists. { r_solve. eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    repeat (grind; gstep; econs; i).
    grind. rewrite/__ !Any.pair_split interp_hp_tau.
    repeat (grind; gstep; econs; i).
    gfinal. right. eapply interp_hp_body_reconf with (cr:=(ε:Σ)).
    right. esplits; eauto. r_solve. eauto.
  Qed.

  Lemma interp_strict_inline_tgt
    nths itrH ktrH st (fr mr fr' mr': Σ)
    (RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr'))
    :
    sim_strict my_tid Any.t (fun _ => eq) nths
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; tau;; ktrH x) fr)
      (Any.pair st mr'↑, x <- interp_hp_body itrH ε;; tau;; '(rr,rv) <- (tau;; Ret (fr',x));; interp_hp_body (ktrH rv) rr).
  Proof.
    ginit. unfold interp_hp_body. rewrite-> !interp_hp_bind. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf with (cr:=fr').
      right. esplits; eauto. r_solve.
      rewrite (URA.add_comm mr' fr'). eauto. }
    i. rewrite-> !interp_hp_bind, interp_hp_Guarantee. unfold hp_fun_tail. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      destruct v0. ss. des; subst; eauto.
      right. esplits; eauto. }
    i. grind; gstep; econs; i. rewrite interp_hp_tau. grind. gstep. econs; i.
    destruct v0. rr in REL; des; subst. simpl. destruct v1, v0'.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right.  eapply interp_hp_reconf with (cr:=c2).
      s in REL0; des; subst. left. s. esplits; eauto.
      rewrite URA.add_comm. eauto. }
    i. grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      r in REL1. des; subst. eauto. }
    i. gstep; econs. rr in REL1. des; subst.
    destruct v0, v0'. s in REL2; des; subst. eauto.
  Qed.

End INTERP_RECONF.


  
Section HPSIM_ADEQUACY. 
  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hmodE Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Variable Ist: nat -> alist key Any.t -> alist key Any.t -> iProp.
  Variable my_tid: nat.

(******* Move ******)
  Lemma own_ctx_r a b
      (OWN: Own a ⊢ #=> Own b)
    :
      forall ctx, Own (a ⋅ ctx) ⊢ #=> Own (b ⋅ ctx)
  .
  Proof.
    i. iIntros "[H H0]".
    iPoseProof (OWN with "H") as "H".
    iSplitL "H"; et.
  Qed.

  (*** Used only in hpsim_adequacy. ***)
  Lemma own_upd_in_middle fr_src mr_src fr_tgt mr_tgt ctx fmr fmr0
    (UPD: Own (fr_src ⋅ mr_src) ⊢ #=> Own (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt))
    (FMR: Own fmr ⊢ #=> Own fmr0)
  :
    Own (fr_src ⋅ mr_src) ⊢ #=> Own (ctx ⋅ fmr0 ⋅ fr_tgt ⋅ mr_tgt).
  Proof.
    eapply own_trans; eauto. 
    iIntros "[[[CTX FMR] FRT] MRT]". iPoseProof (FMR with "FMR") as "FMR". iMod "FMR".
    iModIntro. iSplitR "MRT"; eauto. iSplitR "FRT"; eauto. iSplitR "FMR"; eauto.
  Qed.

  Definition ctx_sem (ctx: list Σ) : Σ :=
    foldr URA.add ε ctx.

  Definition ctx_set (ctx: list Σ) (r: Σ) : list Σ :=
    <[my_tid := r]> ctx.
  
  Definition ctx_add (ctx: list Σ) (r: Σ) : list Σ :=
    ctx_set ctx ((or_else (ctx !! my_tid) ε) ⋅ r).

  Lemma ctx_set_sem ctx r r'
    (IN: my_tid < List.length ctx):
    ctx_sem (ctx_set ctx (r ⋅ r')) = ctx_sem (ctx_set ctx r) ⋅ r'.
  Proof.
    unfold ctx_set. revert my_tid r r' IN.
    induction ctx; i; ss; try nia.
    destruct my_tid; s; r_solve.
    eapply IHctx; try nia.
  Qed.
  
  Lemma ctx_add_sem ctx r
    (IN: my_tid < List.length ctx):
    ctx_sem (ctx_add ctx r) = ctx_sem ctx ⋅ r.
  Proof.
    unfold ctx_add, ctx_set. revert my_tid r IN.
    induction ctx; i; ss; try nia.
    destruct my_tid; s; r_solve.
    eapply IHctx; try nia.
  Qed.

  Lemma le_mine_in (ctx0 ctx: list Σ)
    (CTXLE: le_mine eq my_tid ctx0 ctx)
    (IN: my_tid < List.length ctx0)
    :
    my_tid < List.length ctx.
  Proof.
    unfold le_mine in *.
    eapply lookup_lt_is_Some_2 in IN. rdes IN.
    eapply CTXLE in IN. des. subst.
    eapply lookup_lt_is_Some_1. eauto.
  Qed.

  Lemma ctx_set_le_others ctx r:
    le_others my_tid ctx (ctx_set ctx r).
  Proof.
    unfold ctx_set. r; esplits.
    - rewrite list.insert_length. eauto.
    - i. rewrite list_lookup_insert_ne; eauto.
  Qed.

  Lemma ctx_le_mine_sem (w0 w1: list Σ)
    (IN: my_tid < List.length w0)
    (LE: le_mine eq my_tid w0 w1)
    :
    ctx_sem w1 = ctx_sem (ctx_set w1 (or_else (w0 !! my_tid) ε)).
  Proof.
    unfold ctx_sem, ctx_set.
    move w1 before Ist. revert_until w1.
    induction w1; i; eauto.
    destruct w0; ss; try nia.
    destruct my_tid; ss.
    - exploit LE; ss. i; des. inv x0. eauto.
    - erewrite IHw1; eauto. nia.
  Qed.

  Variant interp_inv: list Σ -> nat * Any.t * Any.t -> Prop :=
  | interp_inv_intro
      (ctx: list Σ) (mr_src mr_tgt: Σ) nths st_src st_tgt mr
      (WF: URA.wf mr_src)
      (MRS: Own mr_src ⊢ #=> Own (ctx_sem ctx ⋅ mr ⋅ mr_tgt))
      (MR: Own mr ⊢ #=> Ist nths st_src st_tgt)
      (NODUPS: List.NoDup (List.map fst st_src))
      (NODUPT: List.NoDup (List.map fst st_tgt))
    :
    interp_inv ctx (nths, Any.pair (alist_encode st_src) mr_src↑, Any.pair (alist_encode st_tgt) mr_tgt↑)
  .

  Lemma hpsim_adequacy:
    forall
      (NODUPFS: List.NoDup (List.map fst fl_src))
      (NODUPFT: List.NoDup (List.map fst fl_tgt))
      (fl_src0 fl_tgt0: alist gname (Any.t -> itree modE Any.t))
      (FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
      (FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
      ps pt nths st_src st_tgt itr_src itr_tgt
      (NODUPS: List.NoDup (List.map fst st_src))
      (NODUPT: List.NoDup (List.map fst st_tgt))
      (ctx0 ctx: list Σ) (mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (CTXLE: @le_mine Σ eq my_tid ctx0 ctx)
      (TID: my_tid < List.length ctx0)
      (SIM: hpsim_body fl_src fl_tgt Ist my_tid ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
      (WF: URA.wf (fr_src ⋅ mr_src))
      (FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own ((ctx_sem ctx) ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)),
    @sim_itree fl_src0 fl_tgt0 Σ ε interp_inv eq my_tid ctx0 ps pt ctx nths
      (Any.pair (alist_encode st_src) mr_src↑, interp_hp_body itr_src fr_src)
      (Any.pair (alist_encode st_tgt) mr_tgt↑, interp_hp_body itr_tgt fr_tgt).
  Proof.
    i. apply hpsim_add_dummy in SIM; cycle 1; eauto.
    revert_until FLT. ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before FLT. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    exploit IN; i; des.
    { eapply own_wf in FMR; eauto. rewrite (URA.add_comm _ fmr) in FMR.
      repeat eapply URA.wf_mon in FMR. eauto. }
    assert (URA.wf fmr).
    { eapply own_wf, WF.
      eapply own_trans; et. rewrite <- !URA.add_assoc.
      iIntros "[_ [FMR _]]". eauto. }
    assert (URA.wf fmr0).
    { eapply own_wf; eauto. }

    destruct x0; i; des.
    - unfold interp_hp_body, hp_fun_tail, handle_Guarantee, guarantee, mget_res, mput_res.
      clarify. hide Choose 1. steps. unhide.
      force_l. instantiate (1 := (c0, c1, (ctx_sem ctx) ⋅ fmr0 ⋅ c)).
      hide Choose 1. step. unhide.
      force_l.
      { eapply own_trans; et. rewrite <- !URA.add_assoc.
        iIntros "[CTX [FMR TGT]]". iPoseProof (x with "TGT") as "C".
        iMod "C" as "[[C0 C1] C]". iSplitL "C0"; eauto.
        iSplitL "C1"; eauto. iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
        iApply x1; eauto.
      }
      steps. econs; eauto.
      unfold hpsim_tail in RET.
      esplits; et; cycle 1.
      { eapply own_pure; eauto.
        iIntros "H". iPoseProof (RET with "H") as "[EQ _]".
        iApply Upd_Pure.  eauto. }
      econs; et; cycle 1.
      { iIntros "H". iPoseProof (RET with "H") as "[_ H]". et. }
      eapply own_wf, WF. eapply own_trans; et. rewrite <- !URA.add_assoc.
      iIntros "[CTX [FMR TGT]]". iPoseProof (x with "TGT") as "C".
      iMod "C" as "[[C0 C1] C]". iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
      iApply x1; eauto.
    - unfold interp_hp_body.
      exploit iProp_sepconj_upd; eauto. i; des.
      rename rq into fr, rp into mr.
      steps. unfold handle_Guarantee, guarantee, mget_res, mput_res.
      hide Choose 1. hide Call 2. steps. unhide.
      rename c1 into frt, c into mrt.
      force_l. instantiate (1:= (ε, ε, c0 ⋅ (ctx_sem ctx) ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      assert (UPD: Own ((ctx_sem ctx) ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)
                    ⊢ #=> Own (c0 ⋅ (ctx_sem ctx) ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      { rewrite <-!URA.add_assoc.
        iIntros "[CTX [FMR TGT]]".
        iPoseProof (x with "TGT") as "TGT". iMod "TGT".
        iPoseProof (x1 with "FMR") as "FMR". iMod "FMR".
        iPoseProof (x0 with "FMR") as "FMR". iMod "FMR".
        iCombine "CTX FMR TGT" as "RES". iModIntro. iStopProof.
        eapply eq_ind; eauto. f_equal. r_solve.
      }
      hide Choose 1. hide Call 2. step. unhide.
      force_l.
      { etrans; eauto. r_solve. iIntros "H". iMod "H". iApply UPD. eauto. }
      force_l; et.
      hide Call 1. hide Call 1. do 2 step. unhide.
      _step; swap 1 2.
      { instantiate (1:= (ctx_add ctx (fr ⋅ frt))).
        econs; cycle 2; eauto.
        { iIntros "H". iApply x2. eauto. }
        { eapply own_wf, WF. etrans. apply FMR.
          iIntros "H". iMod "H". iApply UPD. eauto. }
        { iIntros "H". iModIntro. iStopProof. apply Own_extends.
          do 2 apply URA.extends_add.
          rewrite/__ -!URA.add_assoc [c0 ⋅ _]URA.add_comm.
          r; esplits. rewrite ctx_add_sem; eauto using le_mine_in.
        }
      }
      { apply ctx_set_le_others. }

      guclo lflagC_spec. econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε)); eauto; cycle 1.
      { apply ctx_set_le_others. }

      assert (LT0: my_tid < strings.length ctx).
      { eauto using le_mine_in. }
      assert (LT: my_tid < strings.length w1).
      {
        eapply le_mine_in; eauto.
        unfold ctx_add, ctx_set.
        rewrite list.insert_length. eauto.
      }
      
      do 2 step. grind.
      inv WF0. eapply K with (fmr0 := fr ⋅ mr0); r_solve; et; i.
      { iIntros "[FR MR]". iSplitR "FR"; [iApply MR|iApply x3]; eauto. }
      { eapply le_mine_trans; [ii; subst; eauto|..]; eauto.
        ii. esplits; eauto. unfold ctx_set. rewrite IN0. s.
        rewrite list_lookup_insert; eauto.
      }
      { iIntros "H". iMod (MRS with "H") as "H". iModIntro.
        iStopProof. apply Own_extends.
        apply URA.extends_add.
        rewrite/__ -!URA.add_assoc [mr0 ⋅ _]URA.add_comm.
        erewrite (ctx_le_mine_sem _ w1); try apply WLE; eauto.
        - unfold ctx_add, ctx_set.
          rewrite list_lookup_insert; eauto.
          setoid_rewrite (ctx_set_sem w1 _ (fr ⋅ frt)); eauto.
          exists ε. r_solve.
        - unfold ctx_add, ctx_set. rewrite list.insert_length. nia.
      }
    - unfold interp_hp_body. do 4 step. grind. eapply K; et.
      eapply own_upd_in_middle; eauto.
    - exploit K; cycle 3; eauto; inv Heqp; eauto.
      { eapply own_upd_in_middle; eauto. }
      i. rewrite-> interp_hp_body_bind, interp_hp_call.
      unfold handle_Guarantee, mget_res, mput_res, guarantee.
      force_l. instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
      step. force_l. { r_solve; et. }
      force_l; et. steps.
      {	instantiate (1:= interp_hp_fun f).
        rewrite alist_find_map. rewrite FUN. et. }
      guclo sim_strictC_spec. econs; eauto.
      + unfold interp_hp_fun. grind.
        eapply eq_ind; [eapply interp_strict_inline_src|].
        do 2 f_equal. grind.
      + apply sim_strict_refl.
    - exploit K; cycle 3; eauto; inv Heqp0; eauto.
      { eapply own_upd_in_middle; eauto. }
      i. steps. rewrite-> interp_hp_body_bind, interp_hp_call.
      unfold handle_Guarantee, mget_res, mput_res, guarantee.
      steps.
      {	instantiate (1:= interp_hp_fun f).
      rewrite alist_find_map. rewrite FUN. et. }
      guclo sim_strictC_spec. econs; eauto.
      + apply sim_strict_refl.
      + unfold interp_hp_fun. grind.
        match goal with [|-_ ?x _] => pattern x end.
        eapply eq_ind; [eapply interp_strict_inline_tgt|].
        * eapply own_trans; eauto.
          iIntros "[[C0 C1] C]". iModIntro. iSplitR "C"; eauto.
        * do 2 f_equal. grind.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mput_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto.
      + eapply alist_upd_nodup. eauto.
      + eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mput_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto.
      + eapply alist_upd_nodup. eauto.
      + eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mget_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mget_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. rewrite interp_hp_Assume. unfold handle_Assume, mget_res, mput_res.
      steps. eapply K with (fmr0 := x ⋅ fmr0); et.
      {
        iIntros "[X FMR]". iPoseProof (_ASSUME0 with "X") as "iP".
        iPoseProof (CUR with "FMR") as "FMR". iMod "FMR".
        iModIntro. iFrame.
      }
      eapply own_ctx with (ctx := x) in FMR; et. rewrite URA.add_assoc in FMR.
      replace (x ⋅ (ctx_sem ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx_sem ctx ⋅ x ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) in FMR; r_solve.
      eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps.
      rewrite interp_hp_Guarantee. unfold handle_Guarantee, guarantee, mget_res, mput_res.
      steps. eapply K with (fmr0 := c0 ⋅ fmr0); et.
      { iIntros "[P FMR]". iPoseProof (x0 with "P") as "P". iPoseProof (CUR with "FMR") as "FMR". iFrame. eauto. }
      eapply own_trans; et.
      replace (ctx_sem ctx ⋅ (c0 ⋅ fmr0) ⋅ c1 ⋅ c) with (ctx_sem ctx ⋅ fmr0 ⋅ (c0 ⋅ c1 ⋅ c)); [|r_solve].
      rewrite <- URA.add_assoc. eapply own_trans with (b:= (ctx_sem ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c))).
      { eapply own_ctx. et. }
      iIntros "[[CTX FMR] C]". iPoseProof (x1 with "FMR") as "FMR". iMod "FMR".
      iModIntro. iSplitR "C"; eauto. iSplitR "FMR"; eauto.
    - unfold interp_hp_body. steps.
      rewrite interp_hp_Guarantee. assert (H1 := CUR).
      eapply iProp_sepconj_upd in H1; eauto. des. rename rq into fmr1.
      unfold handle_Guarantee, guarantee, mget_res, mput_res. grind.
      force_l. instantiate (1:= (rp, fmr1 ⋅ fr_tgt, ctx_sem ctx ⋅ mr_tgt)).
      do 2 step.
      {
        replace (rp ⋅ (fmr1 ⋅ fr_tgt) ⋅ (ctx_sem ctx ⋅ mr_tgt)) with (ctx_sem ctx ⋅ rp ⋅ fmr1 ⋅ fr_tgt ⋅ mr_tgt); r_solve.
        iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        rewrite <- URA.add_assoc.
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        iStopProof. eapply own_trans; eauto.
      }
      steps. eapply K with (fmr0 := fmr1); et.
      { iIntros "H". iApply H3; eauto. }
      {
        eapply own_wf in FMR; et.
        replace (ctx_sem ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with (fmr ⋅ (ctx_sem ctx ⋅ fr_tgt ⋅ mr_tgt)) in FMR; r_solve.
        eapply own_ctx_r in x1, H1. eapply own_wf in x1, H1; eauto.
        replace (rp ⋅ fmr1 ⋅ (ctx_sem ctx ⋅ fr_tgt ⋅ mr_tgt)) with (fmr1 ⋅ fr_tgt ⋅ ctx_sem ctx ⋅ mr_tgt ⋅ rp) in H1; r_solve.
        eapply URA.wf_mon; eauto.
      }
      replace (fmr1 ⋅ fr_tgt ⋅ (ctx_sem ctx ⋅ mr_tgt)) with (ctx_sem ctx ⋅ fmr1 ⋅ fr_tgt ⋅ mr_tgt); r_solve; eauto.
    - unfold interp_hp_body. steps. rewrite interp_hp_Assume. assert (H1 := CUR).
      eapply iProp_sepconj_upd in H1; eauto. des. rename rq into fmr1.
      unfold handle_Assume, assume, mget_res, mput_res.
      step. instantiate (1:= rp).
      do 2 step.
      {
        eapply own_wf in FMR; et. replace (ctx_sem ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with ((fmr ⋅ (fr_tgt ⋅ mr_tgt) ⋅ ctx_sem ctx)) in FMR; r_solve.
        eapply URA.wf_mon in FMR. eapply own_ctx_r in x1, H1. eapply own_wf in x1, H1; eauto.
        replace (rp ⋅ fmr1 ⋅ (fr_tgt ⋅ mr_tgt)) with (rp ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr1) in H1; r_solve.
        eapply URA.wf_mon; eauto.
      }
      steps. eapply K with (fmr0 := fmr1); eauto using iProp_Own.
      { iIntros "H". iApply H3; eauto. }
      eapply own_trans; eauto.
      eapply own_trans. { eapply own_upd_in_middle; eauto. }
      replace (ctx_sem ctx ⋅ fmr1 ⋅ (rp ⋅ fr_tgt) ⋅ mr_tgt) with (ctx_sem ctx ⋅ (rp ⋅ fmr1) ⋅ fr_tgt ⋅ mr_tgt); [|r_solve].
      eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. rewrite !interp_hp_spawn. do 3 step. grind.
      eapply K; et.
      + eapply le_mine_trans; [ii; subst; eauto|..]; eauto.
        ii. esplits; eauto. rewrite lookup_app_l; eauto using lookup_lt_is_Some_1.
      + iIntros "H". iMod (FMR with "H") as "H".
        unfold ctx_sem. rewrite foldr_app. s. r_solve.
        iDestruct "H" as "(((CTX & FMR) & FR) & MR)".
        iMod (x1 with "FMR") as "FMR".
        iCombine "CTX FR MR FMR" as "H". iModIntro. iStopProof. apply Own_extends.
        exists ε. r_solve.
    - unfold interp_hp_body.
      exploit iProp_sepconj_upd; eauto. i; des.
      rename rq into fr, rp into mr.
      steps. unfold handle_Guarantee, guarantee, mget_res, mput_res.
      hide Choose 1. hide Yield 2. steps. unhide.
      rename c1 into frt, c into mrt.
      force_l. instantiate (1:= (ε, ε, c0 ⋅ (ctx_sem ctx) ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      assert (UPD: Own ((ctx_sem ctx) ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)
                    ⊢ #=> Own (c0 ⋅ (ctx_sem ctx) ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      { rewrite <-!URA.add_assoc.
        iIntros "[CTX [FMR TGT]]".
        iPoseProof (x with "TGT") as "TGT". iMod "TGT".
        iPoseProof (x1 with "FMR") as "FMR". iMod "FMR".
        iPoseProof (x0 with "FMR") as "FMR". iMod "FMR".
        iCombine "CTX FMR TGT" as "RES". iModIntro. iStopProof.
        eapply eq_ind; eauto. f_equal. r_solve.
      }
      hide Choose 1. hide Yield 2. step. unhide.
      force_l.
      { etrans; eauto. r_solve. iIntros "H". iMod "H". iApply UPD. eauto. }
      force_l; et.
      hide Yield 1. hide Yield 1. do 2 step. unhide.
      _step; swap 1 2.
      { instantiate (1:= (ctx_add ctx (fr ⋅ frt))).
        econs; cycle 2; eauto.
        { iIntros "H". iApply x2. eauto. }
        { eapply own_wf, WF. etrans. apply FMR.
          iIntros "H". iMod "H". iApply UPD. eauto. }
        { iIntros "H". iModIntro. iStopProof. apply Own_extends.
          do 2 apply URA.extends_add.
          rewrite/__ -!URA.add_assoc [c0 ⋅ _]URA.add_comm.
          r; esplits. rewrite ctx_add_sem; eauto using le_mine_in.
        }
      }
      { apply ctx_set_le_others. }

      guclo lflagC_spec. econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε)); eauto; cycle 1.
      { apply ctx_set_le_others. }

      assert (LT0: my_tid < strings.length ctx).
      { eauto using le_mine_in. }
      assert (LT: my_tid < strings.length w1).
      {
        eapply le_mine_in; eauto.
        unfold ctx_add, ctx_set.
        rewrite list.insert_length. eauto.
      }
                              
      do 2 step. grind.
      inv WF0. eapply K with (fmr0 := fr ⋅ mr0); r_solve; et; i.
      { iIntros "[FR MR]". iSplitR "FR"; [iApply MR|iApply x3]; eauto. }
      { eapply le_mine_trans; [ii; subst; eauto|..]; eauto.
        ii. esplits; eauto. unfold ctx_set. rewrite IN0. s.
        rewrite list_lookup_insert; eauto.
      }
      { iIntros "H". iMod (MRS with "H") as "H". iModIntro.
        iStopProof. apply Own_extends.
        apply URA.extends_add.
        rewrite/__ -!URA.add_assoc [mr0 ⋅ _]URA.add_comm.
        erewrite (ctx_le_mine_sem _ w1); try apply WLE; eauto.
        - unfold ctx_add, ctx_set.
          rewrite list_lookup_insert; eauto.
          setoid_rewrite (ctx_set_sem w1 _ (fr ⋅ frt)); eauto.
          exists ε. r_solve.
        - unfold ctx_add, ctx_set. rewrite list.insert_length. nia.
      }
    - unfold interp_hp_body. steps. rewrite !interp_hp_tid. do 3 step.
      eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. rewrite !interp_hp_tid. do 3 step.
      eapply K; et. eapply own_upd_in_middle; eauto.
    - subst. pclearbot. gstep. econs. econs; [apply le_others_refl|].
      gfinal. left. eapply CIH; et. eapply own_upd_in_middle; eauto.
  Qed.

End HPSIM_ADEQUACY.

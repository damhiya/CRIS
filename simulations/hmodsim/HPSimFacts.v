Require Import Coqlib ITreelib sflib.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IModL.
Require Import Any.
Require Import STB ModSim ModSimTactics.
Require Import Events HMod HMod2Mod.

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
  Variable Ist: alist string Any.t -> alist string Any.t -> iProp.
  
  Local Notation _hpsim := (@_hpsim Σ fl_src fl_tgt Ist).
  Local Notation hpsim := (@hpsim Σ fl_src fl_tgt Ist).

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

  Variant hpsim_dummyC_src (r: forall R (RR: (alist string Any.t) * R -> (alist string Any.t) * R -> iProp), bool -> bool -> (alist string Any.t) * itree hmodE R -> (alist string Any.t) * itree hmodE R -> Σ -> Prop):
    forall R (RR: (alist string Any.t) * R -> (alist string Any.t) * R -> iProp), bool -> bool -> (alist string Any.t) * itree hmodE R -> (alist string Any.t) * itree hmodE R -> Σ -> Prop
  :=
  | hpsim_dummyC_src_intro R RR ps pt st_src i_src i_src' st_tgt i_tgt fmr
      (SIM: r R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
      (DUMMY: itreeH_dummy R i_src i_src')
    :
    hpsim_dummyC_src r R RR ps pt (st_src, i_src') (st_tgt, i_tgt) fmr
  .
  
  Lemma hpsim_dummyC_src_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_dummyC_src r1 <7= hpsim_dummyC_src r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma hpsim_dummyC_src_compatible:
    compatible7 (@_hpsim true) hpsim_dummyC_src.
  Proof.
    econs; eauto using hpsim_dummyC_src_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs. ii.
    specialize (IN H). r in DUMMY. des. esplits; eauto.
    destruct IN; i; depdes Heqsti_src Heqsti_tgt;
      esplits; grind; eauto; try by econs; eauto 10.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      rewrite <-x; destruct with_dummy; grind; econs; eauto with imodL.
      i. econs. ii. esplits; eauto. econs; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL.
        ii; esplits; eauto. econs; eauto.
      + replace c with (Call fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL.
        ii. esplits; eauto. econs; eauto.
      + replace e with (@IO I R0 fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; try econs; eauto with imodL.
        ii. esplits; eauto. econs; eauto.
      + replace c with (Call fn varg). econs; eauto. eapply K; eauto.
        eexists with_dummy, _, (x<-f varg;; trigger (Guarantee True);;; ktrH' x), k.
        esplits; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x. destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + replace e with (Take R0); econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + replace e with (Choose R0); eauto. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + depdes s; depdes x. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'. 
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + depdes s; depdes x. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_src; eauto with imodL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - econs; eauto. econs; eauto.
  Qed.

  Lemma hpsim_dummyC_src_spec:
    hpsim_dummyC_src <8= gupaco7 (@_hpsim true) (cpn7 (@_hpsim true)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_src_compatible.
    eapply hpsim_dummyC_src_mon, PR; eauto with paco.
  Qed.

  Variant hpsim_dummyC_tgt (r: forall R (RR: (alist string Any.t) * R -> (alist string Any.t) * R -> iProp), bool -> bool -> (alist string Any.t) * itree hmodE R -> (alist string Any.t) * itree hmodE R -> Σ -> Prop):
    forall R (RR: (alist string Any.t) * R -> (alist string Any.t) * R -> iProp), bool -> bool -> (alist string Any.t) * itree hmodE R -> (alist string Any.t) * itree hmodE R -> Σ -> Prop
  :=
  | hpsim_dummyC_tgt_intro R RR ps pt st_src i_src st_tgt i_tgt i_tgt' fmr
      (SIM: r R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
      (DUMMY: itreeH_dummy R i_tgt i_tgt')
    :
    hpsim_dummyC_tgt r R RR ps pt (st_src, i_src) (st_tgt, i_tgt') fmr
  .
  
  Lemma hpsim_dummyC_tgt_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_dummyC_tgt r1 <7= hpsim_dummyC_tgt r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma hpsim_dummyC_tgt_compatible:
    compatible7 (@_hpsim true) hpsim_dummyC_tgt.
  Proof.
    econs; eauto using hpsim_dummyC_tgt_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs. ii.
    specialize (IN H). r in DUMMY. des. esplits; eauto.
    destruct IN; i; depdes Heqsti_src Heqsti_tgt;
      esplits; grind; eauto; try by econs; eauto 10.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      rewrite <-x; destruct with_dummy; grind; econs; eauto; imodIntroL.
      i. econs. ii. esplits; eauto. econs; eauto; imodIntroL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
        ii; esplits; eauto. econs; eauto.
      + replace c with (Call fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
        ii. esplits; eauto. econs; eauto.
      + replace e with (@IO I R0 fn varg). econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
        ii. esplits; eauto. econs; eauto.
      + replace c with (Call fn varg). econs; eauto. eapply K; eauto.
        eexists with_dummy, _, (x<-f varg;; trigger (Guarantee True);;; ktrH' x), k.
        esplits; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x. destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + replace e with (Choose R0); econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + replace e with (Take R0); eauto. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + depdes s; depdes x. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + depdes s; depdes x. econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'. 
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        destruct with_dummy; grind; eauto using @_hpsim'.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
        ii. econs. ii. esplits; eauto. econs; eauto.
      + econs; eauto.
    - subst. econs; eauto. econs; eauto.
  Qed.

  Lemma hpsim_dummyC_tgt_spec:
    hpsim_dummyC_tgt <8= gupaco7 (@_hpsim true) (cpn7 (@_hpsim true)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_tgt_compatible.
    eapply hpsim_dummyC_tgt_mon, PR; eauto with paco.
  Qed.
  
  Lemma hpsim_le_gpaco r r':
    @hpsim <7= gpaco7 (@_hpsim true) (cpn7 (@_hpsim true)) r r'.
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
    @hpsim <7= paco7 (@_hpsim true) bot7.
  Proof. ginit. i. eapply hpsim_le_gpaco. eauto. Qed.

End HPSIM_ADD_DUMMY.




Section INTERP_RECONF.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hmodE Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Variable Ist: Any.t -> Any.t -> iProp.

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
    r R RR str i i'
    (FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑)
    :
    paco4 _sim_strict r R RR
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
    P str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_equiv cr)
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
    str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_eq cr)
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

  Lemma trigger_callE_simpl R (P: iProp) (e : callE R):
    (trigger (|e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma trigger_pgE_simpl R (P: iProp) (e : pgE R):
    (trigger (|e|)%sum : itree hmodE R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma interp_hp_reconf
    R itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel R hp_reconf_equiv cr)
      (str, interp_hp itrH fr)
      (str', interp_hp itrH fr').
    Proof.
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
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf. eauto. }
      i. grind; gstep; econs; i.
      gfinal. left. eapply CIH. destruct v0, v0'. rr in REL. des; subst. ss.
    - rewrite-> !interp_hp_bind, !interp_hp_call. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf_true. eauto. }
      i. destruct v0, v0', c. repeat (rr in REL; des; subst).
      repeat (grind; gstep; econs; i).
      gfinal. left. eapply CIH. left. s. eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggers.
      destruct s. 
      + unfold handle_pgE_tgt, mput_kv.
        repeat (grind; gstep; econs; i).
        grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
        { rewrite !Any.pair_split. repeat (grind; gstep; econs).
          gfinal. left. eapply CIH. right. esplits; eauto. }
        destruct (Any.split str) as [[]|] eqn: STR; cycle 1.
        { s. unfold triggerUB. grind. gstep. econs. i. ss. }        
        apply Any.split_pair in STR. des; subst.
        repeat (grind; gstep; econs).
        gfinal. left. eapply CIH. econs. econs; eauto.
      + unfold handle_pgE_tgt, mget_kv.
        repeat (grind; gstep; econs; i).
        grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
        { rewrite !Any.pair_split. repeat (grind; gstep; econs).
          gfinal. left. eapply CIH. right. esplits; eauto. }
        destruct (Any.split str) as [[]|] eqn: STR; cycle 1.
        { s. unfold triggerUB. grind. gstep. econs. i. ss. }        
        apply Any.split_pair in STR. des; subst.
        repeat (grind; gstep; econs).
        gfinal. left. eapply CIH. econs. econs; eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggere.
      destruct e.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + repeat (grind; gstep; econs; i). eauto 10 with paco.
  Qed.

  Lemma hp_fun_tail_reconf
    str str' (fr fr' cr: Σ) x
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
      (str, hp_fun_tail (fr,x))
      (str', hp_fun_tail (fr',x)).
  Proof.
    ginit. unfold hp_fun_tail. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst).
    eauto with paco.
  Qed.

  Lemma interp_hp_body_reconf
    itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
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
    itrH ktrH st (fr mr: Σ)
    :
    sim_strict Any.t eq
      (Any.pair st (fr ⋅ mr)↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (ε,x));; interp_hp_body (ktrH rv) rr)
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr).
  Proof.
    ginit. guclo sim_strict_transC_spec. econs; cycle 1.
    { gfinal. right. eapply interp_hp_body_reconf with (fr := (ε:Σ)) (cr:=(ε:Σ)).
      right. esplits; eauto. instantiate (1:= fr ⋅ mr). r_solve. eauto. }
    { i. destruct PR. subst. eauto. }
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
    grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    gfinal. right. eapply interp_hp_body_reconf with (cr:=(ε:Σ)).
    right. esplits; eauto. r_solve. eauto.
  Qed.

  Lemma interp_strict_inline_tgt
    itrH ktrH st (fr mr fr' mr': Σ)
    (RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr'))
    :
    sim_strict Any.t eq
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr)
      (Any.pair st mr'↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (fr',x));; interp_hp_body (ktrH rv) rr).
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
    i. grind; gstep; econs; i.
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
  Variable Ist: alist string Any.t -> alist string Any.t -> iProp.

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

  Variant interp_inv: Σ -> Any.t * Any.t -> Prop :=
  | interp_inv_intro
      (ctx mr_src mr_tgt: Σ) st_src st_tgt mr
      (WF: URA.wf mr_src)
      (MRS: Own mr_src ⊢ #=> Own (ctx ⋅ mr ⋅ mr_tgt))
      (MR: Own mr ⊢ #=> Ist st_src st_tgt)
      (NODUPS: List.NoDup (List.map fst st_src))
      (NODUPT: List.NoDup (List.map fst st_tgt))
    :
    interp_inv ctx (Any.pair (alist_encode st_src) mr_src↑, Any.pair (alist_encode st_tgt) mr_tgt↑)
  .

  Lemma hpsim_adequacy:
    forall
      (fl_src0 fl_tgt0: alist string (Any.t -> itree modE Any.t))
      (FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
      (FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
      ps pt st_src st_tgt itr_src itr_tgt
      (NODUPS: List.NoDup (List.map fst st_src))
      (NODUPT: List.NoDup (List.map fst st_tgt))
      (ctx mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim_body fl_src fl_tgt Ist ps pt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
      (WF: URA.wf (fr_src ⋅ mr_src))
      (FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)),
    @sim_itree Σ interp_inv eq fl_src0 fl_tgt0 ps pt ctx
      (Any.pair (alist_encode st_src) mr_src↑, interp_hp_body itr_src fr_src)
      (Any.pair (alist_encode st_tgt) mr_tgt↑, interp_hp_body itr_tgt fr_tgt).
  Proof.
    i. apply hpsim_add_dummy in SIM; cycle 1; eauto.
    revert_until FLT. ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before FLT. revert_until SIM. punfold SIM.
    pattern ps, pt, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    exploit IN; i; des.
    { eapply own_wf in FMR; eauto. rewrite (URA.add_comm ctx fmr) in FMR.
      repeat eapply URA.wf_mon in FMR. eauto. }
    assert (URA.wf fmr).
    { eapply own_wf, WF.
      eapply own_trans; et. rewrite <- !URA.add_assoc.
      iIntros "[_ [FMR _]]". eauto. }
    assert (URA.wf fmr0).
    { eapply own_wf; eauto. }
    
    destruct x0; i; des.
    - unfold interp_hp_body, hp_fun_tail, handle_Guarantee, guarantee, mget_res, mput_res.
      steps. force_l. instantiate (1 := (c0, c1, ctx ⋅ fmr0 ⋅ c)). steps.
      force_l.
      { eapply own_trans; et. rewrite <- !URA.add_assoc.
        iIntros "[CTX [FMR TGT]]". iPoseProof (x with "TGT") as "C".
        iMod "C" as "[[C0 C1] C]". iSplitL "C0"; eauto.
        iSplitL "C1"; eauto. iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
        iApply x1; eauto.
      }
      steps. force_l; et. 
      steps. econs.
      unfold hpsim_tail in RET.
      esplits; et; cycle 1.
      { eapply own_pure; eauto.
        iIntros "H". iPoseProof (RET with "H") as "[_ EQ]".
        iApply Upd_Pure.  eauto. }
      econs; et; cycle 1.
      { iIntros "H". iPoseProof (RET with "H") as "[H _]". et. }
      eapply own_wf, WF. eapply own_trans; et. rewrite <- !URA.add_assoc.
      iIntros "[CTX [FMR TGT]]". iPoseProof (x with "TGT") as "C".
      iMod "C" as "[[C0 C1] C]". iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
      iApply x1; eauto.
    - unfold interp_hp_body.
      exploit iProp_sepconj_upd; eauto. i; des.
      rename rq into fr, rp into mr.
      steps_safe. unfold handle_Guarantee, guarantee, mget_res, mput_res.
      steps_safe. rename c1 into frt, c into mrt.
      force_l. instantiate (1:= (ε, ε, c0 ⋅ ctx ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      assert (UPD: Own (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)
                    ⊢ #=> Own (c0 ⋅ ctx ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)).
      { rewrite <-!URA.add_assoc.
        iIntros "[CTX [FMR TGT]]".
        iPoseProof (x with "TGT") as "TGT". iMod "TGT".
        iPoseProof (x1 with "FMR") as "FMR". iMod "FMR".
        iPoseProof (x0 with "FMR") as "FMR". iMod "FMR".
        iCombine "CTX FMR TGT" as "RES". iModIntro. iStopProof.
        eapply eq_ind; eauto. f_equal. r_solve.
      }
      steps_safe. force_l.
      { etrans; eauto. r_solve. iIntros "H". iMod "H". iApply UPD. eauto. }
      steps_safe. force_l; et.
      steps_safe. eapply safe_sim_sim; econs. esplits; i.
      { instantiate (1:= ctx ⋅ fr ⋅ frt). econs; cycle 2; eauto.
        { iIntros "H". iApply x2. eauto. }
        { eapply own_wf, WF. etrans. apply FMR.
          iIntros "H". iMod "H". iApply UPD. eauto. }
        { rewrite -!URA.add_assoc URA.add_comm.
          iIntros "H". iModIntro. iStopProof. apply Own_extends.
          r; esplits; eauto. }
      }
      steps_safe.
      inv WF0. eapply K with (fmr0 := fr ⋅ mr0); r_solve; et; i.
      { iIntros "[FR MR]". iSplitR "FR"; [iApply MR|iApply x3]; eauto. }
      { eapply eq_ind; eauto. do 2 f_equal. r_solve. }
    - unfold interp_hp_body. steps. eapply K; et.
      eapply own_upd_in_middle; eauto. 
    - exploit K; cycle 3; eauto; inv Heqp; eauto.
      { eapply own_upd_in_middle; eauto. }
      i. steps. rewrite-> interp_hp_body_bind, interp_hp_call.
      unfold handle_Guarantee, mget_res, mput_res, guarantee. 
      steps. force_l. instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
      steps. force_l. { r_solve; et. }
      steps. force_l; et. steps.
      {	instantiate (1:= interp_hp_fun f).
      rewrite alist_find_map. rewrite FUN. et. }
      guclo sim_strictC_spec. econs; eauto.
      + unfold interp_hp_fun. grind.
        pattern (` r0 : Any.t <- f varg;; ` x : Any.t <- (trigger (Guarantee True);;; Ret r0);; k_src x).
        replace (` r0 : Any.t <- f varg;; ` x : Any.t <- (trigger (Guarantee True);;; Ret r0);; k_src x)
           with (` x: Any.t <- f varg;; trigger (Guarantee True);;; k_src x); grind.
        apply interp_strict_inline_src.
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
        pattern (` r0 : Any.t <- f varg;; ` x3 : Any.t <- (trigger (Guarantee True);;; Ret r0);; k_tgt x3).
        replace (` r0 : Any.t <- f varg;; ` x3 : Any.t <- (trigger (Guarantee True);;; Ret r0);; k_tgt x3)
           with (` x: Any.t <- f varg;; trigger (Guarantee True);;; k_tgt x); grind.
        apply interp_strict_inline_tgt. eapply own_trans; eauto.
        iIntros "[[C0 C1] C]". iModIntro. iSplitR "C"; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. force_l. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. force_r. steps. eapply K; et. eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mput_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto.
      + eapply alist_add_nodup. eauto.
      + eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps. unfold mput_kv. steps.
      rewrite alist_encode_decode.
      des_ifs. eapply K; eauto.
      + eapply alist_add_nodup. eauto.
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
      replace (x ⋅ (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ x ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) in FMR; r_solve.
      eapply own_upd_in_middle; eauto.
    - unfold interp_hp_body. steps.
      rewrite interp_hp_Guarantee. unfold handle_Guarantee, guarantee, mget_res, mput_res.
      steps. eapply K with (fmr0 := c0 ⋅ fmr0); et.
      { iIntros "[P FMR]". iPoseProof (x0 with "P") as "P". iPoseProof (CUR with "FMR") as "FMR". iFrame. eauto. }
      eapply own_trans; et.
      replace (ctx ⋅ (c0 ⋅ fmr0) ⋅ c1 ⋅ c) with (ctx ⋅ fmr0 ⋅ (c0 ⋅ c1 ⋅ c)); [|r_solve].
      rewrite <- URA.add_assoc. eapply own_trans with (b:= (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c))).
      { eapply own_ctx. et. }
      iIntros "[[CTX FMR] C]". iPoseProof (x1 with "FMR") as "FMR". iMod "FMR". 
      iModIntro. iSplitR "C"; eauto. iSplitR "FMR"; eauto. 
    - unfold interp_hp_body. steps.
      rewrite interp_hp_Guarantee. assert (H1 := CUR).
      eapply iProp_sepconj_upd in H1; eauto. des. rename rq into fmr1.
      unfold handle_Guarantee, guarantee, mget_res, mput_res.
      steps. force_l. instantiate (1:= (rp, fmr1 ⋅ fr_tgt, ctx ⋅ mr_tgt)).
      steps. force_l. 
      {
        replace (rp ⋅ (fmr1 ⋅ fr_tgt) ⋅ (ctx ⋅ mr_tgt)) with (ctx ⋅ rp ⋅ fmr1 ⋅ fr_tgt ⋅ mr_tgt); r_solve. 
        iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        rewrite <- URA.add_assoc. 
        iDestruct "H" as "[H H0]". iSplitL "H"; et.
        iStopProof. eapply own_trans; eauto. 
      }
      steps. force_l; eauto using iProp_Own.
      steps. eapply K with (fmr0 := fmr1); et.
      { iIntros "H". iApply H3; eauto. }
      {
        eapply own_wf in FMR; et.
        replace (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with (fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) in FMR; r_solve.
        eapply own_ctx_r in x1, H1. eapply own_wf in x1, H1; eauto.
        replace (rp ⋅ fmr1 ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) with (fmr1 ⋅ fr_tgt ⋅ ctx ⋅ mr_tgt ⋅ rp) in H1; r_solve.
        eapply URA.wf_mon; eauto.
      }
      replace (fmr1 ⋅ fr_tgt ⋅ (ctx ⋅ mr_tgt)) with (ctx ⋅ fmr1 ⋅ fr_tgt ⋅ mr_tgt); r_solve; eauto.
    - unfold interp_hp_body. steps. rewrite interp_hp_Assume. assert (H1 := CUR). 
      eapply iProp_sepconj_upd in H1; eauto. des. rename rq into fmr1.
      unfold handle_Assume, assume, mget_res, mput_res. 
      steps. force_r. instantiate (1:= rp).
      steps. force_r.
      {
        eapply own_wf in FMR; et. replace (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with ((fmr ⋅ (fr_tgt ⋅ mr_tgt) ⋅ ctx)) in FMR; r_solve.
        eapply URA.wf_mon in FMR. eapply own_ctx_r in x1, H1. eapply own_wf in x1, H1; eauto. 
        replace (rp ⋅ fmr1 ⋅ (fr_tgt ⋅ mr_tgt)) with (rp ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr1) in H1; r_solve.
        eapply URA.wf_mon; eauto.
      }
      steps. force_r; eauto using iProp_Own.
      steps. eapply K with (fmr0 := fmr1); eauto using iProp_Own.
      { iIntros "H". iApply H3; eauto. }
      eapply own_trans; eauto.
      eapply own_trans. { eapply own_upd_in_middle; eauto. }
      replace (ctx ⋅ fmr1 ⋅ (rp ⋅ fr_tgt) ⋅ mr_tgt) with (ctx ⋅ (rp ⋅ fmr1) ⋅ fr_tgt ⋅ mr_tgt); [|r_solve].
      eapply own_upd_in_middle; eauto.
    - steps. pclearbot. gstep. econs. gfinal. left. eapply CIH; et. eapply own_upd_in_middle; eauto.
  Qed.

End HPSIM_ADEQUACY.

Require Import Coqlib sflib ITreelib.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IModL.
Require Import Any.
Require Import Events STB ModSim.

Require Import Relation_Definitions.

Require Import Relation_Operators.

Require Import RelationPairs.

From ExtLib Require Import
     Data.Map.FMapAList.
     
Require Import Red IRed.


Section SIM_STRICT.

  Variant _sim_strict (sim_strict: forall R, relation (Any.t * R) -> relation (Any.t * itree modE R))
    : forall R, relation (Any.t * R) -> relation (Any.t * itree modE R)
  :=
  | sim_strict_ret R RR st st' v v'
      (RET: RR (st,v) (st',v'): Prop)
    :
    _sim_strict sim_strict R RR
      (st, Ret v)
      (st', Ret v')
  | sim_strict_call R RR
      st fn varg k k'
      (K: forall st0 vret,
          sim_strict R RR (st0, k vret) (st0, k' vret))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Call fn varg) >>= k)
      (st, trigger (Call fn varg) >>= k')
  | sim_strict_io R RR
      I O st st' fn (varg: I) k k'
      (K: forall (vret: O),
          sim_strict R RR (st, k vret) (st', k' vret))
    :
    _sim_strict sim_strict R RR
      (st, trigger (IO fn varg) >>= k)
      (st', trigger (IO fn varg) >>= k')
  | sim_strict_tau R RR
      st st' i i'
      (K: sim_strict R RR (st, i) (st', i'))
    :
    _sim_strict sim_strict R RR
      (st, tau;; i)
      (st', tau;; i')
  | sim_strict_choose R RR
      st st' X X' k k'
      (K: forall x', exists x, sim_strict R RR (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Choose X) >>= k)
      (st', trigger (Choose X') >>= k')
  | sim_strict_take R RR
      st st' X X' k k'
      (K: forall x, exists x', sim_strict R RR (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Take X) >>= k)
      (st', trigger (Take X') >>= k')
  | sim_strict_supdate R RR
      st st' X k X' k' (run: Any.t -> Any.t * X) (run': Any.t -> Any.t * X')
      (K: sim_strict R RR
            (fst (run st), k (snd (run st)))
            (fst (run' st'), k' (snd (run' st'))))
    :
    _sim_strict sim_strict R RR
      (st, trigger (SUpdate run) >>= k)
      (st', trigger (SUpdate run') >>= k')
  .

  Definition sim_strict := paco4 _sim_strict bot4.

  Lemma sim_strict_mon: monotone4 _sim_strict.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_strict.
  Hint Unfold sim_strict.
  Hint Resolve sim_strict_mon: paco.
  Hint Resolve cpn4_wcompat: paco.

  Lemma sim_strict_refl
    R sti
    :
    sim_strict R eq sti sti.
  Proof.
    revert_until R. ginit. gcofix CIH; i.
    destruct sti as [st i]. ides i; eauto with paco.
    gstep. destruct e; [destruct c|destruct s; [destruct s|destruct c]];
      rewrite <-(bind_ret_l_eta _ k); rewrite <-bind_vis;
      econs; eauto with paco.
  Qed.

  Lemma sim_strict_le
    R RR RR'
    (LE: RR <2= RR')
    :
    sim_strict R RR <2= sim_strict R RR'.
  Proof.
    ginit. gcofix CIH. i. punfold PR.
    inv PR; grind; depdes H0; try itree_clarify x;
      gstep; econs; i; try edestruct K; pclearbot; eauto with paco.
  Qed.

  Variant sim_strict_bindC (r: forall R, relation (Any.t*R) -> relation (Any.t * itree modE R)) :
    forall R, relation (Any.t*R) -> relation (Any.t * itree modE R)
  :=
  | sim_strict_bindC_intro R RR Q QQ st st' i i' k k'
      (HD: r R RR (st,i) (st',i'))
      (TL: forall st0 v0 st0' v0' (REL: RR (st0,v0) (st0',v0')),
           r Q QQ (st0, k v0) (st0', k' v0'))
    :
    sim_strict_bindC r Q QQ (st, i >>= k) (st', i' >>= k')
  .

  Lemma sim_strict_bindC_mon
        r1 r2
        (LEr: r1 <4= r2)
    :
    sim_strict_bindC r1 <4= sim_strict_bindC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_bindC_wrespectful:
    wrespectful4 _sim_strict sim_strict_bindC.
  Proof.
    econs; eauto using sim_strict_bindC_mon; i.
    destruct PR. apply GF in HD. inv HD; grind; depdes H3 H0; grind;
      try (by econs; i; econs 2; eauto; econs; eauto using rclo4).
    - eapply sim_strict_mon; eauto using rclo4.
    - econs. i. specialize (K x'). des.
      eexists. econs 2; eauto. econs; eauto using rclo4.
    - econs. i. specialize (K x). des.
      eexists. econs 2; eauto. econs; eauto using rclo4.
  Qed.

  Lemma sim_strict_bindC_spec:
    sim_strict_bindC <5= gupaco4 _sim_strict (cpn4 _sim_strict).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco.
    apply sim_strict_bindC_wrespectful.
  Qed.

  Variant sim_strict_transC (r: forall R, relation (Any.t*R) -> relation (Any.t * itree modE R)) :
    forall R, relation (Any.t*R) -> relation (Any.t * itree modE R)
  :=
  | sim_strict_transC_intro R RR0 RR1 RR st st' st'' i i' i''
      (REL0: r R RR0 (st,i) (st',i'))
      (REL1: r R RR1 (st',i') (st'',i''))
      (LE: rcompose RR0 RR1 <2= RR)
    :
    sim_strict_transC r R RR (st, i) (st'', i'')
  .

  Lemma sim_strict_transC_mon
        r1 r2
        (LEr: r1 <4= r2)
    :
    sim_strict_transC r1 <4= sim_strict_transC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_transC_wrespectful:
    wrespectful4 _sim_strict sim_strict_transC.
  Proof.
    econs; eauto using sim_strict_transC_mon; i.
    destruct PR. apply GF in REL0. apply GF in REL1.
    inv REL0; grind; depdes H3 H0; try itree_clarify x;
      inv REL1; grind; depdes H3 H0; try itree_clarify x;
        econs; i; eauto using sim_strict_transC, rclo4.
    - destruct (K0 x'), (K x). eauto using sim_strict_transC, rclo4.
    - destruct (K x), (K0 x0). eauto using sim_strict_transC, rclo4.
  Qed.

  Lemma sim_strict_transC_spec:
    sim_strict_transC <5= gupaco4 _sim_strict (cpn4 _sim_strict).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco.
    apply sim_strict_transC_wrespectful.
  Qed.

  Lemma sim_strict_inv_ret R RR sti st' v'
      (EQV: sim_strict R RR sti (st', Ret v')):
    exists st v, sti = (st, Ret v) /\ RR (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
  Qed.

  Lemma sim_strict_inv_ret' R RR st v sti'
      (EQV: sim_strict R RR (st, Ret v) sti'):
    exists st' v', sti' = (st', Ret v') /\ RR (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
  Qed.
  
  Lemma sim_strict_inv_call R RR sti st fn varg k'
      (EQV: sim_strict R RR sti (st, trigger (Call fn varg) >>= k')):
    exists k,
    sti = (st, trigger (Call fn varg) >>= k) /\
    forall st0 vret, sim_strict R RR (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_call' R RR st fn varg k sti' 
      (EQV: sim_strict R RR (st, trigger (Call fn varg) >>= k) sti'):
    exists k',
    sti' = (st, trigger (Call fn varg) >>= k') /\
    forall st0 vret, sim_strict R RR (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.
  
  Lemma sim_strict_inv_io R RR sti st' I O fn (varg: I) k'
      (EQV: sim_strict R RR sti (st', trigger (IO fn varg) >>= k')):
    exists st k,
    sti = (st, trigger (IO fn varg) >>= k) /\
    forall (vret: O), sim_strict R RR (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_io' R RR st I O fn (varg: I) k sti'
      (EQV: sim_strict R RR (st, trigger (IO fn varg) >>= k) sti'):
    exists st' k',
    sti' = (st', trigger (IO fn varg) >>= k') /\
    forall (vret: O), sim_strict R RR (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.
  
  Lemma sim_strict_inv_tau R RR sti st' i'
      (EQV: sim_strict R RR sti (st', tau;; i')):
    exists st i,
    sti = (st, tau;; i) /\
    sim_strict R RR (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
  Qed.

  Lemma sim_strict_inv_tau' R RR st i sti' 
      (EQV: sim_strict R RR (st, tau;; i) sti'):
    exists st' i',
    sti' = (st', tau;; i') /\
    sim_strict R RR (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
  Qed.
  
  Lemma sim_strict_inv_choose R RR sti st' X' k'
      (EQV: sim_strict R RR sti (st', trigger (Choose X') >>= k')):
    exists st X k,
    sti = (st, trigger (Choose X) >>= k) /\
    forall x', exists x, sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_choose' R RR st X k sti' 
      (EQV: sim_strict R RR (st, trigger (Choose X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Choose X') >>= k') /\
    forall x', exists x, sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_take R RR sti st' X' k'
      (EQV: sim_strict R RR sti (st', trigger (Take X') >>= k')):
    exists st X k,
    sti = (st, trigger (Take X) >>= k) /\
    forall x, exists x', sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_take' R RR st X k sti'
      (EQV: sim_strict R RR (st, trigger (Take X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Take X') >>= k') /\
    forall x, exists x', sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_update R RR sti st' X' (run': Any.t -> Any.t * X') k'
      (EQV: sim_strict R RR sti (st', trigger (SUpdate run') >>= k')):
    exists X (run: Any.t -> Any.t * X) st k,
    sti = (st, trigger (SUpdate run) >>= k) /\
    sim_strict R RR ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_update' R RR st X (run: Any.t -> Any.t * X) k sti'
      (EQV: sim_strict R RR (st, trigger (SUpdate run) >>= k) sti'):
    exists X' (run': Any.t -> Any.t * X') st' k',
    sti' = (st', trigger (SUpdate run') >>= k') /\
    sim_strict R RR ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  (** **)

  Variant sim_strictC W
      (r: forall S_src S_tgt (RR: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> W -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop):
      forall S_src S_tgt (RR: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> W -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop
    :=
  | sim_strictC_intro RR p_src p_tgt w sti_src sti_tgt sti_src' sti_tgt'
      (SIM: r Any.t Any.t RR p_src p_tgt w sti_src' sti_tgt')
      (EQVSRC: sim_strict Any.t eq sti_src sti_src')
      (EQVTGT: sim_strict Any.t eq sti_tgt' sti_tgt)
    : sim_strictC W r Any.t Any.t RR p_src p_tgt w sti_src sti_tgt
  .

  Lemma sim_strictC_mon W r1 r2
    (LEr: r1 <8= r2)
    :
    sim_strictC W r1 <8= sim_strictC W r2.
  Proof. ii. destruct PR. econs; et. Qed.

  Lemma sim_strictC_compatible: forall W wf le fl_src fl_tgt, 
      compatible8 (@_sim_itree W wf le fl_src fl_tgt) (sim_strictC W).
  Proof.
    econs; i; eauto using sim_strictC_mon. depdes PR.
    move SIM before RR. revert_until SIM.
    induction SIM; i; subst.
    - apply sim_strict_inv_ret in EQVSRC. apply sim_strict_inv_ret' in EQVTGT.
      des. subst. clarify. eauto using _sim_itree.
    - apply sim_strict_inv_call in EQVSRC. apply sim_strict_inv_call' in EQVTGT.
      des. subst. clarify. eauto using _sim_itree.
    - apply sim_strict_inv_io in EQVSRC. apply sim_strict_inv_io' in EQVTGT.
      des. subst. eauto using _sim_itree.
    - apply sim_strict_inv_call in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto. eapply IHSIM; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gfinal. right. apply EQVSRC0.
    - apply sim_strict_inv_call' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto. eapply IHSIM; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gfinal. right. apply EQVTGT0.
    - apply sim_strict_inv_tau in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_tau' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto.
    - apply sim_strict_inv_choose in EQVSRC. des. subst.
      specialize (EQVSRC0 x). des. destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_choose' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto. i. specialize (EQVTGT0 x). des; eauto.
    - apply sim_strict_inv_take in EQVSRC. des. subst.
      destruct sti_tgt. econs. i. specialize (EQVSRC0 x). des. eauto.
    - apply sim_strict_inv_take' in EQVTGT. des. subst.
      specialize (EQVTGT0 x). des. destruct sti_src. econs; eauto.
    - apply sim_strict_inv_update in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_update' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto.
    - destruct sti_src, sti_tgt. econs; eauto. econs; eauto.
  Qed.

  Lemma sim_strictC_spec: forall W wf le fl_src fl_tgt,
      sim_strictC W <9= gupaco8 (@_sim_itree W wf le fl_src fl_tgt) (cpn8 (@_sim_itree W wf le fl_src fl_tgt)).
  Proof.
    intros. gclo. econs; eauto using sim_strictC_compatible.
    eapply sim_strictC_mon, PR; eauto with paco.
  Qed.
  
End SIM_STRICT.

Hint Constructors _sim_strict.
Hint Unfold sim_strict.
Hint Resolve sim_strict_mon: paco.
Hint Resolve cpn4_wcompat: paco.

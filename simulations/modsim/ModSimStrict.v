Require Import Coqlib sflib ITreelib.
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

  Variable my_tid : nat.

  Variant _sim_strict (sim_strict : forall R, (nat -> relation (Any.t * R)) -> nat -> relation (Any.t * itree modE R))
    : forall R, (nat -> relation (Any.t * R)) -> nat -> relation (Any.t * itree modE R)
  :=
  | sim_strict_ret R RR nths st st' v v'
      (RET : RR nths (st,v) (st',v') : Prop)
    :
    _sim_strict sim_strict R RR nths
      (st, Ret v)
      (st', Ret v')
  | sim_strict_call R RR nths
      st fn varg k k'
      (K : forall nths0 st0 vret,
          sim_strict R RR nths0 (st0, k vret) (st0, k' vret))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (Call fn varg) >>= k)
      (st, trigger (Call fn varg) >>= k')
  | sim_strict_io R RR nths
      I O st st' fn (varg : I) k k'
      (K : forall (vret : O),
          sim_strict R RR nths (st, k vret) (st', k' vret))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (IO fn varg) >>= k)
      (st', trigger (IO fn varg) >>= k')
  | sim_strict_tau R RR nths
      st st' i i'
      (K : sim_strict R RR nths (st, i) (st', i'))
    :
    _sim_strict sim_strict R RR nths
      (st, tau;; i)
      (st', tau;; i')
  | sim_strict_choose R RR nths
      st st' X X' k k'
      (K : forall x', exists x, sim_strict R RR nths (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (Choose X) >>= k)
      (st', trigger (Choose X') >>= k')
  | sim_strict_take R RR nths
      st st' X X' k k'
      (K : forall x, exists x', sim_strict R RR nths (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (Take X) >>= k)
      (st', trigger (Take X') >>= k')
  | sim_strict_supdate R RR nths
      st st' X k X' k' (run : Any.t -> Any.t * X) (run' : Any.t -> Any.t * X')
      (K : sim_strict R RR nths
            (fst (run st), k (snd (run st)))
            (fst (run' st'), k' (snd (run' st'))))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (SUpdate run) >>= k)
      (st', trigger (SUpdate run') >>= k')
  | sim_strict_spawn R RR nths
      st st'
      fn arg k k'
      (K : sim_strict R RR (S nths) (st, k nths) (st', k' nths))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (Spawn fn arg) >>= k)
      (st', trigger (Spawn fn arg) >>= k')
  | sim_strict_yield R RR nths
      st tid k k'
      (K : forall nths0 st0,
          sim_strict R RR nths0 (st0, k tt) (st0, k' tt))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger (Yield tid) >>= k)
      (st, trigger (Yield tid) >>= k')
  | sim_strict_tid R RR nths
      st st' k k'
      (K : sim_strict R RR nths (st, k my_tid) (st', k' my_tid))
    :
    _sim_strict sim_strict R RR nths
      (st, trigger Tid >>= k)
      (st', trigger Tid >>= k')
  .

  Definition sim_strict := paco5 _sim_strict bot5.

  Lemma sim_strict_mon : monotone5 _sim_strict.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_strict.
  Hint Unfold sim_strict.
  Hint Resolve sim_strict_mon : paco.
  Hint Resolve cpn5_wcompat : paco.

  Lemma sim_strict_refl
    R nths sti
    :
    sim_strict R (fun _ => eq) nths sti sti.
  Proof.
    revert_until R. ginit. gcofix CIH; i.
    destruct sti as [st i]. ides i; eauto with paco.
    gstep.
    destruct e; [destruct s|destruct s; [destruct c|destruct s; [destruct s|destruct c]]];
      rewrite <-(bind_ret_l_eta _ k); rewrite <-bind_vis;
      econs; eauto with paco.
  Qed.

  Lemma sim_strict_le
    R RR RR'
    (LE : RR <3= RR')
    :
    sim_strict R RR <3= sim_strict R RR'.
  Proof.
    ginit. gcofix CIH. i. punfold PR.
    inv PR; grind; depdes H0; try itree_clarify x;
      gstep; econs; i; try edestruct K; pclearbot; eauto with paco.
  Qed.

  Variant sim_strict_bindC (r : forall R, (nat -> relation (Any.t*R)) -> nat -> relation (Any.t * itree modE R)) :
    forall R, (nat -> relation (Any.t*R)) -> nat -> relation (Any.t * itree modE R)
  :=
  | sim_strict_bindC_intro R RR Q QQ nths st st' i i' k k'
      (HD : r R RR nths (st,i) (st',i'))
      (TL : forall nths0 st0 v0 st0' v0' (REL : RR nths0 (st0,v0) (st0',v0')),
           r Q QQ nths0 (st0, k v0) (st0', k' v0'))
    :
    sim_strict_bindC r Q QQ nths (st, i >>= k) (st', i' >>= k')
  .

  Lemma sim_strict_bindC_mon
        r1 r2
        (LEr : r1 <5= r2)
    :
    sim_strict_bindC r1 <5= sim_strict_bindC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_bindC_wrespectful:
    wrespectful5 _sim_strict sim_strict_bindC.
  Proof.
    econs; eauto using sim_strict_bindC_mon; i.
    destruct PR. apply GF in HD. inv HD; grind; depdes H4 H0; grind;
      try (by econs; i; econs 2; eauto; econs; eauto using rclo5).
    - eapply sim_strict_mon; eauto using rclo5.
    - econs. i. specialize (K x'). des.
      eexists. econs 2; eauto. econs; eauto using rclo5.
    - econs. i. specialize (K x). des.
      eexists. econs 2; eauto. econs; eauto using rclo5.
  Qed.

  Lemma sim_strict_bindC_spec:
    sim_strict_bindC <6= gupaco5 _sim_strict (cpn5 _sim_strict).
  Proof.
    intros. eapply wrespect5_uclo; eauto with paco.
    apply sim_strict_bindC_wrespectful.
  Qed.

  Variant sim_strict_transC (r : forall R, (nat -> relation (Any.t*R)) -> nat -> relation (Any.t * itree modE R)) :
    forall R, (nat -> relation (Any.t*R)) -> nat -> relation (Any.t * itree modE R)
  :=
  | sim_strict_transC_intro R RR0 RR1 RR nths st st' st'' i i' i''
      (REL0 : r R RR0 nths (st,i) (st',i'))
      (REL1 : r R RR1 nths (st',i') (st'',i''))
      (LE : forall nths0, rcompose (RR0 nths0) (RR1 nths0) <2= RR nths0)
    :
    sim_strict_transC r R RR nths (st, i) (st'', i'')
  .

  Lemma sim_strict_transC_mon
        r1 r2
        (LEr : r1 <5= r2)
    :
    sim_strict_transC r1 <5= sim_strict_transC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_transC_wrespectful:
    wrespectful5 _sim_strict sim_strict_transC.
  Proof.
    econs; eauto using sim_strict_transC_mon; i.
    destruct PR. apply GF in REL0. apply GF in REL1.
    inv REL0; grind; depdes H4 H0; try itree_clarify x;
      inv REL1; grind; depdes H4 H0; try itree_clarify x;
        econs; i; eauto using sim_strict_transC, rclo5 with itree.
    - destruct (K0 x'), (K x). eauto using sim_strict_transC, rclo5.
    - destruct (K x), (K0 x0). eauto using sim_strict_transC, rclo5.
  Qed.

  Lemma sim_strict_transC_spec:
    sim_strict_transC <6= gupaco5 _sim_strict (cpn5 _sim_strict).
  Proof.
    intros. eapply wrespect5_uclo; eauto with paco.
    apply sim_strict_transC_wrespectful.
  Qed.

  Lemma sim_strict_inv_ret R RR nths sti st' v'
      (EQV : sim_strict R RR nths sti (st', Ret v')):
    exists st v, sti = (st, Ret v) /\ RR nths (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
  Qed.

  Lemma sim_strict_inv_ret' R RR nths st v sti'
      (EQV : sim_strict R RR nths (st, Ret v) sti'):
    exists st' v', sti' = (st', Ret v') /\ RR nths (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
  Qed.
  
  Lemma sim_strict_inv_call R RR nths sti st fn varg k'
      (EQV : sim_strict R RR nths sti (st, trigger (Call fn varg) >>= k')):
    exists k,
    sti = (st, trigger (Call fn varg) >>= k) /\
    forall nths0 st0 vret, sim_strict R RR nths0 (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_call' R RR nths st fn varg k sti' 
      (EQV : sim_strict R RR nths (st, trigger (Call fn varg) >>= k) sti'):
    exists k',
    sti' = (st, trigger (Call fn varg) >>= k') /\
    forall nths0 st0 vret, sim_strict R RR nths0 (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.
  
  Lemma sim_strict_inv_io R RR nths sti st' I O fn (varg : I) k'
      (EQV : sim_strict R RR nths sti (st', trigger (IO fn varg) >>= k')):
    exists st k,
    sti = (st, trigger (IO fn varg) >>= k) /\
    forall (vret : O), sim_strict R RR nths (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_io' R RR nths st I O fn (varg : I) k sti'
      (EQV : sim_strict R RR nths (st, trigger (IO fn varg) >>= k) sti'):
    exists st' k',
    sti' = (st', trigger (IO fn varg) >>= k') /\
    forall (vret : O), sim_strict R RR nths (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.
  
  Lemma sim_strict_inv_tau R RR nths sti st' i'
      (EQV : sim_strict R RR nths sti (st', tau;; i')):
    exists st i,
    sti = (st, tau;; i) /\
    sim_strict R RR nths (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
  Qed.

  Lemma sim_strict_inv_tau' R RR nths st i sti' 
      (EQV : sim_strict R RR nths (st, tau;; i) sti'):
    exists st' i',
    sti' = (st', tau;; i') /\
    sim_strict R RR nths (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
  Qed.
  
  Lemma sim_strict_inv_choose R RR nths sti st' X' k'
      (EQV : sim_strict R RR nths sti (st', trigger (Choose X') >>= k')):
    exists st X k,
    sti = (st, trigger (Choose X) >>= k) /\
    forall x', exists x, sim_strict R RR nths (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_choose' R RR nths st X k sti' 
      (EQV : sim_strict R RR nths (st, trigger (Choose X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Choose X') >>= k') /\
    forall x', exists x, sim_strict R RR nths (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_take R RR nths sti st' X' k'
      (EQV : sim_strict R RR nths sti (st', trigger (Take X') >>= k')):
    exists st X k,
    sti = (st, trigger (Take X) >>= k) /\
    forall x, exists x', sim_strict R RR nths (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_take' R RR nths st X k sti'
      (EQV : sim_strict R RR nths (st, trigger (Take X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Take X') >>= k') /\
    forall x, exists x', sim_strict R RR nths (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_update R RR nths sti st' X' (run' : Any.t -> Any.t * X') k'
      (EQV : sim_strict R RR nths sti (st', trigger (SUpdate run') >>= k')):
    exists X (run : Any.t -> Any.t * X) st k,
    sti = (st, trigger (SUpdate run) >>= k) /\
    sim_strict R RR nths ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_update' R RR nths st X (run : Any.t -> Any.t * X) k sti'
      (EQV : sim_strict R RR nths (st, trigger (SUpdate run) >>= k) sti'):
    exists X' (run' : Any.t -> Any.t * X') st' k',
    sti' = (st', trigger (SUpdate run') >>= k') /\
    sim_strict R RR nths ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_spawn R RR nths sti st' fn arg k'
      (EQV : sim_strict R RR nths sti (st', trigger (Spawn fn arg) >>= k')):
    exists st k,
    sti = (st, trigger (Spawn fn arg) >>= k) /\
    sim_strict R RR (S nths) (st, k nths) (st', k' nths).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_spawn' R RR nths st fn arg k sti'
      (EQV : sim_strict R RR nths (st, trigger (Spawn fn arg) >>= k) sti'):
    exists st' k',
    sti' = (st', trigger (Spawn fn arg) >>= k') /\
    sim_strict R RR (S nths) (st, k nths) (st', k' nths).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_yield R RR nths sti st tid k'
      (EQV : sim_strict R RR nths sti (st, trigger (Yield tid) >>= k')):
    exists k,
    sti = (st, trigger (Yield tid) >>= k) /\
    forall nths0 st0, sim_strict R RR nths0 (st0, k tt) (st0, k' tt).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H3; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_yield' R RR nths st tid k sti' 
      (EQV : sim_strict R RR nths (st, trigger (Yield tid) >>= k) sti'):
    exists k',
    sti' = (st, trigger (Yield tid) >>= k') /\
    forall nths0 st0, sim_strict R RR nths0 (st0, k tt) (st0, k' tt).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; eauto; try itree_clarify x.
    pclearbot. esplits; eauto.
  Qed.
  
  Lemma sim_strict_inv_tid R RR nths sti st' k'
      (EQV : sim_strict R RR nths sti (st', trigger Tid >>= k')):
    exists st k,
    sti = (st, trigger Tid >>= k) /\
    sim_strict R RR nths (st, k my_tid) (st', k' my_tid).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
    depdes H0. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_tid' R RR nths st k sti' 
      (EQV : sim_strict R RR nths (st, trigger Tid >>= k) sti'):
    exists st' k',
    sti' = (st', trigger Tid >>= k') /\
    sim_strict R RR nths (st, k my_tid) (st', k' my_tid).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; pclearbot; eauto; itree_clarify x.
    esplits; eauto.
  Qed.
  

  Variant sim_strictC world
      (r: forall S_src S_tgt (RR: list world -> nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop):
      forall S_src S_tgt (RR: list world -> nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop
    :=
  | sim_strictC_intro RR p_src p_tgt w nths sti_src sti_tgt sti_src' sti_tgt'
      (SIM: r Any.t Any.t RR p_src p_tgt w nths sti_src' sti_tgt')
      (EQVSRC: sim_strict Any.t (fun _ => eq) nths sti_src sti_src')
      (EQVTGT: sim_strict Any.t (fun _ => eq) nths sti_tgt' sti_tgt)
    : sim_strictC world r Any.t Any.t RR p_src p_tgt w nths sti_src sti_tgt
  .

  Lemma sim_strictC_mon world r1 r2
    (LEr: r1 <9= r2)
    :
    sim_strictC world r1 <9= sim_strictC world r2.
  Proof. ii. destruct PR. econs; et. Qed.

  Lemma sim_strictC_compatible: forall world wi wf le fl_src fl_tgt, 
      compatible9 (@_sim_itree fl_src fl_tgt world wi wf le my_tid) (sim_strictC world).
  Proof.
    econs; i; eauto using sim_strictC_mon. depdes PR.
    move SIM before RR. revert_until SIM.
    pattern p_src, p_tgt, w, nths, sti_src', sti_tgt'.
    eapply sim_itree_tarski, SIM. i. inv PR; subst.
    (* induction SIM; i; subst. *)
    - apply sim_strict_inv_ret in EQVSRC. apply sim_strict_inv_ret' in EQVTGT.
      des. subst. clarify. econs; eauto using sim_itree_def.
    - apply sim_strict_inv_call in EQVSRC. apply sim_strict_inv_call' in EQVTGT.
      des. subst. clarify. econs; eauto using sim_itree_def.
    - apply sim_strict_inv_io in EQVSRC. apply sim_strict_inv_io' in EQVTGT.
      des. subst. econs; eauto using sim_itree_def.
    - apply sim_strict_inv_call in EQVSRC. des. subst.
      destruct sti_tgt. do 2 (econs; eauto). eapply K; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gstep. econs; eauto.
        gfinal. right. rr in EQVSRC0. apply EQVSRC0.
    - apply sim_strict_inv_call' in EQVTGT. des. subst.
      destruct sti_src. do 2 (econs; eauto). eapply K; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gstep. econs; eauto.
        gfinal. right. apply EQVTGT0.
    - apply sim_strict_inv_tau in EQVSRC. des. subst.
      destruct sti_tgt. do 2 (econs; eauto).
    - apply sim_strict_inv_tau' in EQVTGT. des. subst.
      destruct sti_src. do 2 (econs; eauto).
    - apply sim_strict_inv_choose in EQVSRC. des. subst.
      specialize (EQVSRC0 x). des. destruct sti_tgt. do 2 (econs; eauto).
    - apply sim_strict_inv_choose' in EQVTGT. des. subst.
      destruct sti_src. do 2 (econs; eauto). i. specialize (EQVTGT0 x). des; eauto.
    - apply sim_strict_inv_take in EQVSRC. des. subst.
      destruct sti_tgt. do 2 (econs; eauto). i. specialize (EQVSRC0 x). des. eauto.
    - apply sim_strict_inv_take' in EQVTGT. des. subst.
      specialize (EQVTGT0 x). des. destruct sti_src. do 2 (econs; eauto).
    - apply sim_strict_inv_update in EQVSRC. des. subst.
      destruct sti_tgt. do 2 (econs; eauto).
    - apply sim_strict_inv_update' in EQVTGT. des. subst.
      destruct sti_src. do 2 (econs; eauto).
    - apply sim_strict_inv_spawn in EQVSRC. apply sim_strict_inv_spawn' in EQVTGT.
      des. subst. econs; eauto using sim_itree_def.
    - apply sim_strict_inv_yield in EQVSRC. apply sim_strict_inv_yield' in EQVTGT.
      des. subst. clarify. econs; eauto using sim_itree_def.
    - apply sim_strict_inv_tid in EQVSRC. des. subst.
      destruct sti_tgt. do 2 (econs; eauto).
    - apply sim_strict_inv_tid' in EQVTGT. des. subst.
      destruct sti_src. do 2 (econs; eauto).
    - destruct sti_src, sti_tgt. do 2 (econs; eauto). do 2 (econs; eauto).
  Qed.

  Lemma sim_strictC_spec: forall fl_src fl_tgt world wi wf le,
      sim_strictC world <10= gupaco9 (@_sim_itree fl_src fl_tgt world wi wf le my_tid) (cpn9 (@_sim_itree fl_src fl_tgt world wi wf le my_tid)).
  Proof.
    intros. gclo. econs; eauto using sim_strictC_compatible.
    eapply sim_strictC_mon, PR; eauto with paco.
  Qed.
  
End SIM_STRICT.

Hint Constructors _sim_strict.
Hint Unfold sim_strict.
Hint Resolve sim_strict_mon : paco.
Hint Resolve cpn5_wcompat : paco.

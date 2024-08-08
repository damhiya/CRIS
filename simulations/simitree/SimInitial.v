Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import EventsRed Events.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
Require Import SimSTS SimGlobal.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIM.
  Inductive _simT
          (simT: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree takeE R0) -> (itree takeE R1) -> Prop :=
  | simT_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
      _simT simT RR f_src f_tgt (Ret r_src) (Ret r_tgt)

  | simT_tauL
      itr_src0 itr_tgt0
      (TAUL: True)
      (SIM: @_simT simT _ _ RR true f_tgt itr_src0 itr_tgt0)
    :
      _simT simT RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
  | simT_tauR
      itr_src0 itr_tgt0
      (TAUR: True)
      (SIM: @_simT simT _ _ RR f_src true itr_src0 itr_tgt0)
    :
      _simT simT RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

  | simT_takeL
      X ktr_src0 itr_tgt0
      (TAKEL: True)
      (SIM: forall x, _simT simT RR true f_tgt (ktr_src0 x) itr_tgt0)
    :
      _simT simT RR f_src f_tgt (trigger (take X) >>= ktr_src0) (itr_tgt0)
  | simT_takeR
      X x itr_src0 ktr_tgt0
      (TAKER: True)
      (SIM: _simT simT RR f_src true itr_src0 (ktr_tgt0 x))
    :
      _simT simT RR f_src f_tgt (itr_src0) (trigger (take X) >>= ktr_tgt0)

  | simT_progress
      itr_src itr_tgt
      (SIM: simT _ _ RR false false itr_src itr_tgt)
      (SRC: f_src = true)
      (TGT: f_tgt = true)
    :
      _simT simT RR f_src f_tgt itr_src itr_tgt
  .        

  Definition simT: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop := paco7 _simT bot7.

  Lemma simT_mon: monotone7 _simT.
  Proof.
    ii. induction IN; econs; eauto.
  Qed.

  Hint Resolve simT_mon: paco.
  Hint Resolve cpn7_wcompat: paco.


  Inductive simT_indC
            (simT: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree takeE R0) -> (itree takeE R1) -> Prop :=
  | simT_indC_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
      simT_indC simT RR f_src f_tgt (Ret r_src) (Ret r_tgt)

  | simT_indC_tauL
      itr_src0 itr_tgt0
      (TAUL: True)
      (SIM: simT _ _ RR true f_tgt itr_src0 itr_tgt0)
    :
      simT_indC simT RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
  | simT_indC_tauR
      itr_src0 itr_tgt0
      (TAUR: True)
      (SIM: simT _ _ RR f_src true itr_src0 itr_tgt0)
    :
      simT_indC simT RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

  | simT_indC_takeL
      X ktr_src0 itr_tgt0
      (TAKEL: True)
      (SIM: forall x, simT _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
    :
      simT_indC simT RR f_src f_tgt (trigger (take X) >>= ktr_src0) (itr_tgt0)
  | simT_indC_takeR
      X x itr_src0 ktr_tgt0
      (TAKER: True)
      (SIM: simT _ _ RR f_src true itr_src0 (ktr_tgt0 x))
    :
      simT_indC simT RR f_src f_tgt (itr_src0) (trigger (take X) >>= ktr_tgt0)
  .

  Lemma simT_indC_mon: monotone7 simT_indC.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.
  Hint Resolve simT_indC_mon: paco.

  Lemma simT_indC_spec:
    simT_indC <8= gupaco7 _simT (cpn7 _simT).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs; eauto with paco.
  Qed.


  Lemma simT_ind R0 R1 (RR: R0 -> R1 -> Prop)
      (P: bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (TAUL: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: simT RR true f_tgt itr_src0 itr_tgt0)
          (IH: P true f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: simT RR f_src true itr_src0 itr_tgt0)
          (IH: P f_src true itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (TAKEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: simT RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_src f_tgt
          X x itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: simT RR f_src true itr_src0 (ktr_tgt0 x))
          (IH: P f_src true itr_src0 (ktr_tgt0 x)),
          P f_src f_tgt (itr_src0) (trigger (take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src f_tgt
          itr_src itr_tgt
          (SIM: simT RR false false itr_src itr_tgt)
          (SRC: f_src = true)
          (TGT: f_tgt = true),
          P f_src f_tgt itr_src itr_tgt)
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: simT RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
  Proof.
    i. punfold SIM. induction SIM; i; clarify.
    { eapply RET; eauto. }
    { eapply TAUL; eauto. pfold. auto. }
    { eapply TAUR; eauto. pfold. auto. }
    { eapply TAKEL; eauto. i. hexploit (SIM x); eauto. i. des. esplits; eauto. pfold. auto. }
    { eapply TAKER; eauto. des. esplits; eauto. pfold. auto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Hint Constructors _simT.
  Hint Unfold simT.
  Hint Resolve simT_mon: paco.
  Hint Resolve cpn7_wcompat: paco.

  Variant tflagC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree takeE S0) -> (itree takeE S1) -> Prop):
    forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree takeE S0) -> (itree takeE S1) -> Prop :=
  | flagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
      (SIM: r _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
    :
      tflagC r RR f_src1 f_tgt1 itr_src itr_tgt
  .
  Hint Constructors tflagC: core.

  Lemma tflagC_mon
        r1 r2
        (LE: r1 <7= r2)
    :  
      tflagC r1 <7= tflagC r2.
  Proof. ii. destruct PR; econs; et. Qed.
  Hint Resolve tflagC_mon: paco.

  Lemma tflagC_wrespectful: wrespectful7 (_simT) tflagC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. csc. eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM; econs; eauto with paco.
  Qed.

  Lemma tflagC_spec: tflagC <8= gupaco7 (_simT) (cpn7 (_simT)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco. eapply tflagC_wrespectful.
  Qed.

  Lemma simT_flag
        r R0 R1 RR itr_src itr_tgt f_src0 f_tgt0 f_src1 f_tgt1
        (SIM: @_simT r R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_simT r R0 R1 RR f_src1 f_tgt1 itr_src itr_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT. induction SIM; econs; eauto.
  Qed.

  Lemma simT_progress_flag R0 R1 RR r g itr_src itr_tgt
        (SIM: gpaco7 _simT (cpn7 _simT) g g R0 R1 RR false false itr_src itr_tgt)
    :
      gpaco7 _simT (cpn7 _simT) r g R0 R1 RR true true itr_src itr_tgt.
  Proof.
    gstep. econs; eauto.
  Qed.

  Lemma simT_flag_down R0 R1 RR r g itr_src itr_tgt f_src f_tgt
        (SIM: gpaco7 _simT (cpn7 _simT) r g R0 R1 RR false false itr_src itr_tgt)
    :
      gpaco7 _simT (cpn7 _simT) r g R0 R1 RR f_src f_tgt itr_src itr_tgt.
  Proof.
    guclo tflagC_spec. econs; [..|eauto]; ss.
  Qed.

  Lemma simT_bot_flag_up R0 R1 RR st_src st_tgt f_src f_tgt
        (SIM: @simT R0 R1 RR true true st_src st_tgt)
    :
      simT RR f_src f_tgt st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. i. revert f_src f_tgt. 
    induction SIM using simT_ind.
    { guclo simT_indC_spec. econs; eauto. }
    { guclo simT_indC_spec. econs; eauto. }
    { guclo simT_indC_spec. econs; eauto. }
    { guclo simT_indC_spec. econs; eauto. i. specialize (SIM x). des. esplits; eauto. }
    { guclo simT_indC_spec. econs; eauto. }
    { i. eapply simT_flag_down. gfinal. right. eapply paco7_mon; eauto. ss. }
  Qed.


  Variant tbindR (r s: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree takeE S0) -> (itree takeE S1) -> Prop):
    forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree takeE S0) -> (itree takeE S1) -> Prop :=
  | tbindR_intro
      f_src f_tgt

      R0 R1 RR
      (i_src: itree takeE R0) (i_tgt: itree takeE R1)
      (SIM: r _ _ RR f_src f_tgt i_src i_tgt)

      S0 S1 SS
      (k_src: ktree takeE R0 S0) (k_tgt: ktree takeE R1 S1)
      (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ _ SS false false (k_src vret_src) (k_tgt vret_tgt))
  :
    tbindR r s SS f_src f_tgt (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

  Hint Constructors tbindR: core.

  Lemma tbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <7= r2) (LEs: s1 <7= s2)
    :
      tbindR r1 s1 <7= tbindR r2 s2.
  Proof. ii. destruct PR; econs; et. Qed.

  Definition tbindC r := tbindR r r.
  Hint Unfold tbindC: core.

  Lemma tbindC_wrespectful: wrespectful7 (_simT) tbindC.
  Proof.
    econs.
    { ii. eapply tbindR_mon; eauto. }
    i. inv PR. csc. eapply GF in SIM.
    revert k_src k_tgt SIMK. induction SIM; i.
    { 
      irw. hexploit SIMK; eauto. i. eapply GF in H.
      eapply simT_mon; eauto. eapply simT_flag.
      { eapply simT_mon; eauto. i. eapply rclo7_base. auto. }
      { ss. }
      { ss. }
    }
    { rewrite ! bind_tau. econs; eauto. }
    { rewrite ! bind_tau. econs; eauto. }
    { rewrite ! bind_bind. econs; eauto. }
    { rewrite ! bind_bind. econs; eauto. }
    { clarify. econs; eauto. eapply rclo7_clo_base. econs; eauto. }
  Qed.

  Lemma tbindC_spec: tbindC <8= gupaco7 (_simT) (cpn7 (_simT)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco. eapply tbindC_wrespectful.
  Qed.


  (*******************)
  Definition add_tau R (itr itr': itree takeE R) :=
    exists Q i (k: Q -> _),
      itr = (i >>= k) /\ itr' = (x <- i;; tau;; k x).
  Hint Unfold add_tau.

  Variant simT_add_tau (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop):
    forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree takeE R0) -> (itree takeE R1) -> Prop 
  :=
  | simT_add_middle_intro R0 R1 RR ps pt is is' it it'
      (SIM: r R0 R1 RR ps pt is it)
      (SRC: add_tau is is') 
      (TGT: add_tau it it')
    :
    simT_add_tau r RR ps pt is' it'
  .

  Lemma simT_add_tau_mon 
        r1 r2 
        (LE: r1 <7= r2)
    :
    simT_add_tau r1 <7= simT_add_tau r2.
  Proof.
    i. destruct PR; econs; eauto. 
  Qed.

  Lemma simT_add_tau_compatible:
    compatible7 _simT simT_add_tau.
  Proof. Admitted.
  
  Lemma simT_add_tau_spec:
    simT_add_tau <8= gupaco7 _simT (cpn7 _simT).
  Proof.
    i. gclo. econs; eauto using simT_add_tau_compatible.
    eapply simT_add_tau_mon, PR; eauto with paco.
  Qed.
  (*******************)


  Lemma self_simT: 
    forall (wf: Any.t -> Any.t -> Prop) (WF: forall x, wf x x) (itr: itree takeE Any.t), simT wf false false itr itr.
  Proof.
    ginit. gcofix CIH. i. ides itr.
    { gstep. econs. eauto. }
    { gstep. econs; eauto. econs; eauto. econs; eauto. gbase. eauto. }
    destruct e; rewrite <- bind_trigger; resub.
    gstep. econs; eauto. econs; eauto. econs; eauto. gbase. eauto.
  Qed. 

  Theorem adequacy_initial
          T wf (its itt: itree takeE T) ps pt
          (SIM: simT wf ps pt its itt)
      :
          simg wf ps pt (interp_takeE its) (interp_takeE itt).
  Proof.
    revert_until wf. ginit. gcofix CIH. i. 
    remember its. remember itt. move SIM before T. revert_until SIM.
    pattern ps, pt, i, i0.
    match goal with
    | |- ?P ps pt i i0 => set P 
    end.
    revert ps pt i i0 SIM. eapply simT_ind; subst P; ss; i; clarify.
    - rewrite! interp_takeE_ret. gstep. econs. eauto.
    - rewrite interp_takeE_tau. guclo simg_indC_spec. 
    - rewrite interp_takeE_tau. guclo simg_indC_spec. 
    - rewrite interp_takeE_bind. rewrite interp_takeE_take.
      unfold handle_takeE. rewrite bind_bind. 
      guclo simg_indC_spec. econs; eauto. i.
      specialize (SIM x). des. grind. guclo simg_indC_spec.
    - rewrite interp_takeE_bind. rewrite interp_takeE_take.
      unfold handle_takeE. rewrite bind_bind. 
      guclo simg_indC_spec. econs; eauto.
      exists x. grind. guclo simg_indC_spec.
    - gstep. econs; eauto. gbase. eauto.
  Qed.

End SIM.

Ltac stepT := guclo simT_indC_spec; econs; eauto; i.

Hint Constructors _simT.
Hint Unfold simT.
Hint Resolve simT_mon: paco.
Hint Constructors tflagC: core.
Hint Resolve tflagC_mon: paco.
Hint Constructors tbindR: core.
Hint Unfold tbindC: core.
Hint Constructors simT_indC: core.
Hint Resolve simT_indC_mon: paco.

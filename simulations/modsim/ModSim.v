Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import Mod Events.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Require Import SimGlobal.
Require Import Red IRed.


Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIM_ITREE.

  Variable fl_src fl_tgt: alist gname (Any.t -> itree modE Any.t).
  
  Variable world: Type.
  Variable winit : world.
  Variable wf : list world -> nat * (Any.t) * (Any.t) -> Prop.
  Variable wle: relation world.
  Variable my_tid : nat.

  Hypothesis le_refl: Reflexive wle.
  Hypothesis le_trans: Transitive wle.

  Definition le_mine (w w': list world) :=
    forall wi (IN: base.lookup my_tid w = Some wi),
    exists wi', base.lookup my_tid w' = Some wi' /\ wle wi wi'.
  
  Definition le_others (w w': list world) : Prop :=
    List.length w = List.length w' /\
    forall i (OTH: i <> my_tid), base.lookup i w = base.lookup i w'.

  Variant sim_itree_def
    (sim_itree: forall R_src R_tgt (RR: list world -> nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
    {R_src} {R_tgt} (RR: list world -> nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    (self: bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
    : bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
    
  | sim_itree_ret
      ps pt w w0 nths st_src st_tgt
      v_src v_tgt
      (WLE: le_others w w0)
      (RET: RR w0 nths st_src st_tgt v_src v_tgt)
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  
  | sim_itree_call
      ps pt w w0 nths st_src st_tgt
      fn varg k_src k_tgt
      (WLE: le_others w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 vret nths0 st_src0 st_tgt0 (WLE: le_mine w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          self true true w1 nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
    sim_itree_def sim_itree RR self ps pt w nths
      (st_src, trigger (Call fn varg) >>= k_src)
      (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_io
      ps pt w nths st_src st_tgt
      I O fn (varg: I) k_src k_tgt
      (K: forall (vret: O),
          self true true w nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
    sim_itree_def sim_itree RR self ps pt w nths
      (st_src, trigger (IO fn varg) >>= k_src)
      (st_tgt, trigger (IO fn varg) >>= k_tgt)

  | sim_itree_inline_src
      ps pt w nths st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: self true pt w nths (st_src, x <- f varg;; tau;; k_src x) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths
      (st_src, trigger (Call fn varg) >>= k_src)
      (st_tgt, i_tgt)

  | sim_itree_inline_tgt
      ps pt w nths st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: self ps true w nths (st_src, i_src) (st_tgt, x <- f varg;; tau;; k_tgt x))
    :
    sim_itree_def sim_itree RR self ps pt w nths
      (st_src, i_src)
      (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_tau_src
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: self true pt w nths (st_src, i_src) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_tau_tgt
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: self ps true w nths (st_src, i_src) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_choose_src
      ps pt w nths st_src st_tgt
      X x k_src i_tgt
      (K: self true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths
      (st_src, trigger (Choose X) >>= k_src)
      (st_tgt, i_tgt)

  | sim_itree_choose_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), self ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, i_src)
      (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_take_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), self true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, trigger (Take X) >>= k_src)
      (st_tgt, i_tgt)

  | sim_itree_take_tgt
      ps pt w nths st_src st_tgt
      X x i_src k_tgt
      (K: self ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, i_src)
      (st_tgt, trigger (Take X) >>= k_tgt)

  | sim_itree_supdate_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: self true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)  

  | sim_itree_supdate_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: self ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_spawn
      ps pt w nths st_src st_tgt
      fn varg k_src k_tgt
      (K: self true true (w++[winit]) (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, trigger (Spawn fn varg) >>= k_src)
      (st_tgt, trigger (Spawn fn varg) >>= k_tgt)

  | sim_itree_yield
      ps pt w w0 nths st_src st_tgt
      tid k_src k_tgt
      (WLE: le_others w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 nths0 st_src0 st_tgt0 (WLE: le_mine w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          self true true w1 nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, trigger (Yield tid) >>= k_src)
      (st_tgt, trigger (Yield tid) >>= k_tgt)
                 
  | sim_itree_tid_src
      ps pt w nths st_src st_tgt
      k_src i_tgt
      (K: self true pt w nths (st_src, k_src my_tid) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, trigger Tid >>= k_src)
      (st_tgt, i_tgt)

  | sim_itree_tid_tgt
      ps pt w nths st_src st_tgt
      i_src k_tgt
      (K: self ps true w nths (st_src, i_src) (st_tgt, k_tgt my_tid))
    :
    sim_itree_def sim_itree RR self ps pt w nths (st_src, i_src)
      (st_tgt, trigger Tid >>= k_tgt)
      
  | sim_itree_progress
      w w0 nths st_src st_tgt 
      i_src i_tgt
      (WLE: le_others w w0)
      (SIM: sim_itree _ _ RR false false w0 nths (st_src, i_src) (st_tgt, i_tgt))
    :
    sim_itree_def sim_itree RR self true true w nths (st_src, i_src) (st_tgt, i_tgt)
  .

  Inductive _sim_itree sim_itree {R_src} {R_tgt} RR ps pt w nths src tgt : Prop :=
  | _sim_itree_intro (SAT: @sim_itree_def sim_itree R_src R_tgt RR (_sim_itree sim_itree RR) ps pt w nths src tgt)
  .
  
  Definition final_rel w0 w1 (nths: nat) (st_src st_tgt ret_src ret_tgt: Any.t) :=
    le_mine w0 w1 /\ wf w1 (nths, st_src, st_tgt) /\ ret_src = ret_tgt.

  Definition sim_itree w0 ps pt w nths src tgt :=
    paco9 _sim_itree bot9 _ _ (final_rel w0) ps pt w nths src tgt.

  Lemma sim_itree_def_mon sim_itree sim_itree' R_src R_tgt RR P P'
    (LESIM: sim_itree <9= sim_itree')
    (LE: P <6= P')
    :
    @sim_itree_def sim_itree R_src R_tgt RR P <6= sim_itree_def sim_itree' RR P'.
  Proof.
    i. destruct PR; eauto using sim_itree_def.
  Defined.

  Lemma sim_itree_tarski sim_itree R_src R_tgt RR P
    (SIM: @sim_itree_def sim_itree R_src R_tgt RR P <6= P)
    :
    _sim_itree sim_itree RR <6= P.
  Proof.
    fix IH 7. i. destruct PR. eapply SIM.
    eapply sim_itree_def_mon, SAT; i.
    - apply PR.
    - eapply IH, PR.
  Qed.
  
  Lemma sim_itree_mon: monotone9 _sim_itree.
  Proof.
    ii. eapply sim_itree_tarski; eauto.
    econs; inv PR; econs; eauto.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

  Lemma le_mine_refl: Reflexive le_mine.
  Proof. ii. eexists; eauto. Qed.

  Lemma le_mine_trans: Transitive le_mine.
  Proof.
    ii. eapply H in IN. des. eapply H0 in IN. des. eauto.
  Qed.

  Lemma le_others_refl: Reflexive le_others.
  Proof. rr. esplits; eauto. Qed.

  Lemma le_others_trans: Transitive le_others.
  Proof.
    rr. unfold le_others. i; des. split; i.
    - etrans; eauto.
    - etrans; try apply H2; eauto.
  Qed.

  Lemma le_others_inc w1 w2 x:
    le_others w1 w2 -> le_others (w1++[x]) (w2++[x]).
  Proof.
    i. rdes H. split.
    - rewrite !app_length. nia.
    - i. assert (i < List.length w1 \/ i >= List.length w1) by nia; des.
      + rewrite !list.lookup_app_l; try nia. eauto.
      + rewrite !list.lookup_app_r; try nia. f_equal. nia.
  Qed.    

  Lemma sim_itree_wmon self R_src R_tgt RR w1 w2 ps pt nths src tgt
    (SIM: @_sim_itree self R_src R_tgt RR ps pt w2 nths src tgt)
    (WLE: le_others w1 w2)
    :
    _sim_itree self RR ps pt w1 nths src tgt.
  Proof.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, w2, nths, src, tgt.
    eapply sim_itree_tarski, SIM.
    i. econs. inv PR; eauto using sim_itree_def, le_others_refl, le_others_trans.
    econs. eapply K.
    destruct WLE. split.
    { rewrite !app_length. s. nia. }
    i. assert (CASE: i < List.length w1 \/ i = List.length w1 \/ i > List.length w1) by nia. des.
    - rewrite !list.lookup_app_l; try nia. eauto.
    - rewrite !(list.list_lookup_middle _ [] winit); try nia. eauto.
    - rewrite !list.lookup_ge_None_2; eauto; rewrite app_length; s; try nia.
  Qed.

  Lemma sim_itree_ind
        R_src R_tgt RR P
        (SIM: @sim_itree_def (paco9 _sim_itree bot9) R_src R_tgt RR (paco9 _sim_itree bot9 R_src R_tgt RR /6\ P) <6= P)
    :
    paco9 _sim_itree bot9 _ _ RR <6= P.
  Proof.
    i. punfold PR.
    assert (SIM': sim_itree_def (paco9 _sim_itree bot9) RR (paco9 _sim_itree bot9 R_src R_tgt RR /6\ P) <6= (paco9 _sim_itree bot9 R_src R_tgt RR /6\ P)).
    { i. split; eauto. pstep. econs.
      eapply sim_itree_def_mon, PR0; eauto.
      i. ss. des. punfold PR1. }

    eapply sim_itree_tarski in SIM'; des; eauto.
    eapply sim_itree_mon; eauto. i. pclearbot. eauto.
  Qed.

  Definition sim_itree_indC sim_itree {R_src R_tgt} RR :=
    @sim_itree_def bot9 R_src R_tgt RR (sim_itree R_src R_tgt RR).
    
  Lemma sim_itree_indC_mon: monotone9 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.
  
  Lemma sim_itree_indC_spec:
    sim_itree_indC <10= gupaco9 (_sim_itree) (cpn9 _sim_itree).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply sim_itree_mon; et. i. eapply rclo9_base. et. }
    { econs 3; eauto. i. eapply sim_itree_mon; et. i. eapply rclo9_base. eauto. }
    { econs 4; et. eapply sim_itree_mon; et. eapply rclo9_base. }
    { econs 5; et. eapply sim_itree_mon; et. eapply rclo9_base. }
    { econs 6; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 9; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto. }
    { econs 12; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { econs 13; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { econs 14; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { econs 15; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { econs 16; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { econs 17; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo9_base. eauto.  }
    { ss. }
  Qed.

  Definition sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: list world -> nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop) {R_src R_tgt} RR :=
    @sim_itree_def bot9 R_src R_tgt RR (r R_src R_tgt RR).

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <11= gpaco9 (_sim_itree) (cpn9 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs; econs 1; eauto. }
    { guclo sim_itree_indC_spec. econs 2; et. i. gbase. et. }
    { guclo sim_itree_indC_spec. econs 3; et. i. gbase. et. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 14; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 15; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 16; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 17; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 18; eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco9 (_sim_itree) (cpn9 _sim_itree) r g) (gpaco9 (_sim_itree) (cpn9 _sim_itree) g g)
      <9=
      gpaco9 (_sim_itree) (cpn9 _sim_itree) r g.
  Proof.
    i. eapply gpaco9_gpaco; [eauto with paco|].
    eapply gpaco9_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco9_mon; eauto. }
  Qed.
  
  Lemma sim_itree_progress_flag R0 R1 RR w r g nths st_src st_tgt
        (SIM: gpaco9 _sim_itree (cpn9 _sim_itree) g g R0 R1 RR false false w nths st_src st_tgt)
    :
      gpaco9 _sim_itree (cpn9 _sim_itree) r g R0 R1 RR true true w nths st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; econs; eauto using le_others_refl. 
  Qed.
  
  Lemma sim_itree_flag_mon
        sim_itree R_src R_tgt RR
        ps0 pt0 ps1 pt1 w nths st_src st_tgt
        (SIM: @_sim_itree sim_itree R_src R_tgt RR ps0 pt0 w nths st_src st_tgt)
        (SRC: ps0 = true -> ps1 = true)
        (TGT: pt0 = true -> pt1 = true)
    :
      _sim_itree sim_itree RR ps1 pt1 w nths st_src st_tgt.
  Proof.
    move SIM before sim_itree. revert_until SIM.
    pattern ps0, pt0, w, nths, st_src, st_tgt.
    eapply sim_itree_tarski, SIM.
    i. econs. inv PR; eauto using sim_itree_def.
    exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto.
  Qed.

  Definition sim_fsem: relation (Any.t -> itree modE Any.t) :=
    (eq ==> (fun it_src it_tgt =>
               forall w nths mrs_src mrs_tgt
                      (TID: my_tid < List.length w)
                      (SIMMRS: wf w (nths, mrs_src, mrs_tgt)),
                 sim_itree w false false w nths (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Variant lflagC (r: forall (R_src R_tgt: Type)
    (RR: list world -> nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: list world -> nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> list world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | lflagC_intro
      ps0 ps1 pt0 pt1 w0 w1 nths st_src st_tgt
      (SIM: r _ _ RR ps0 pt0 w0 nths st_src st_tgt)
      (WLE: le_others w1 w0)
      (SRC: ps0 = true -> ps1 = true)
      (TGT: pt0 = true -> pt1 = true)
    :
      lflagC r RR ps1 pt1 w1 nths st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1 <9= r2)
    :
      @lflagC r1 <9= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <10= gupaco9 (_sim_itree) (cpn9 _sim_itree).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 x5 WLE SRC TGT.
    pattern ps0, pt0, w0, x6, x7, x8.
    eapply sim_itree_tarski, SIM.
    i. econs. inv PR;
      eauto using sim_itree_def, sim_itree_wmon, le_others_refl, le_others_trans, le_others_inc.
    exploit SRC; auto. exploit TGT; auto. i. clarify.
    econs; cycle 1; eauto using rclo9, le_others_trans.
  Qed.

  Lemma sim_itree_flag_down  R0 R1 RR r g w nths st_src st_tgt ps pt
        (SIM: gpaco9 _sim_itree (cpn9 _sim_itree) r g R0 R1 RR false false w nths st_src st_tgt)
    :
      gpaco9 _sim_itree (cpn9 _sim_itree) r g R0 R1 RR ps pt w nths st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto using le_others_refl.
  Qed.

  Lemma sim_itree_bot_flag_up w0 w nths st_src st_tgt ps pt
        (SIM: paco9 _sim_itree bot9 _ _ (final_rel w0) true true w nths st_src st_tgt)
    :
      paco9 _sim_itree bot9 _ _ (final_rel w0) ps pt w nths st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w nths st_src st_tgt ps pt b b0 SIM.
    gcofix CIH. 
    i. revert ps pt. pattern b, b0, w, nths, st_src, st_tgt.
    eapply sim_itree_ind, SIM. i.
    inv PR; ss; i; clarify; try (guclo sim_itree_indC_spec; hdes; econs; eauto).
    eapply sim_itree_flag_down. gfinal. right.
    eapply paco9_mon.
    - punfold SIM0. pstep. eapply sim_itree_wmon; eauto using le_others_refl.
    - ss.
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: list world -> nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop):
    forall S_src S_tgt (SS: list world -> nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> list world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop :=

  | lbindR_intro
      ps pt w R_src R_tgt RR nths (st_src st_tgt: Any.t) (i_src: itree modE R_src) (i_tgt: itree modE R_tgt)
      (SIM: r R_src R_tgt RR ps pt w nths (st_src, i_src) (st_tgt, i_tgt))

      S_src S_tgt SS (k_src: ktree modE R_src S_src) (k_tgt: ktree modE R_tgt S_tgt)
      (SIMK: forall w0 nths0 st_src0 st_tgt0 vret_src vret_tgt (SIM: RR w0 nths0 st_src0 st_tgt0 vret_src vret_tgt), s _ _ SS false false w0 nths0 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt))
    :
      lbindR r s SS ps pt w nths (st_src, ITree.bind i_src k_src) (st_tgt, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon 
        r1 r2 s1 s2
        (LEr: r1 <9= r2) (LEs: s1  <9= s2)
    :
      lbindR r1 s1 <9= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.
  Hint Resolve lbindR_mon: paco.

  Lemma lbindC_wrespectful: wrespectful9 (_sim_itree) lbindC.
  Proof.
    econs; eauto with paco.
    i. inv PR; csc.
    remember (st_src, i_src). remember(st_tgt, i_tgt).
    move SIM before GF. revert_until SIM. eapply GF in SIM.
    pattern x3, x4, x5, x6, p, p0.
    eapply sim_itree_tarski, SIM.
    i. inv PR; clarify; grind; try (econs; econs; eauto).
    - exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon with (ps0 := false) (pt0 := false); ss.
      eapply sim_itree_mon.
      + eapply sim_itree_wmon; eauto.
      + eauto using rclo9.
    - exploit K; et. i. rewrite !bind_bind in *.
      erewrite equal_f; eauto. do 3 eapply f_equal.
      extensionalities. rewrite bind_tau. eauto.
    - exploit K; et. i. rewrite ! bind_bind in *.
      erewrite f_equal; eauto. do 2 eapply f_equal.
      extensionalities. rewrite bind_tau. eauto.
    - eapply rclo9_clo_base. eauto.
  Qed.

  Lemma lbindC_spec: lbindC <10= gupaco9 (_sim_itree) (cpn9 (_sim_itree)).
  Proof.
    intros. eapply wrespect9_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM_ITREE.

Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn9_wcompat: paco.

Require Import Program.

Module MSim.
Section MODSEMR.

  Variable (ms_src ms_tgt: ModSem.t).
  
  Let fl_src := ms_src.(ModSem.fnsems).
  Let fl_tgt := ms_tgt.(ModSem.fnsems).
  Let st_src := ms_src.(ModSem.initial_st).
  Let st_tgt := ms_tgt.(ModSem.initial_st).

  Inductive t: Type := mk {
    world: Type;
    winit: world;
    wf: list world -> nat * Any.t * Any.t -> Prop;
    wle: world -> world -> Prop;
    wle_refl: Reflexive wle;
    wle_trans: Transitive wle;
    wf_mon: forall w n n0 st_src st_tgt (LE: n <= n0) (WF: wf w (n,st_src,st_tgt)), wf w (n0,st_src,st_tgt);
    wf_winit: forall w n st_src st_tgt (WF: wf w (n,st_src,st_tgt)), wf (w++[winit]) (n,st_src,st_tgt);
    sim_initial:
      exists w, wf [w] (1, st_src, st_tgt);
    sim_length:
      List.length fl_src = List.length fl_tgt;
    sim_fnsems:
      forall fn fs (FIND: alist_find fn fl_src = Some fs),
      exists ft, alist_find fn fl_tgt = Some ft /\
        forall my_tid, sim_fsem fl_src fl_tgt winit wf wle my_tid fs ft;
  }.

  Lemma wf_sim_miss (SIM: t)
    (WF: ModSem.wf ms_src)
    :
    forall fn (MISS: alist_find fn fl_src = None),
      alist_find fn fl_tgt = None.
  Proof.
    ii. destruct WF as [NODUP].
    destruct (alist_find fn fl_tgt) eqn: EQ; eauto.
    apply alist_find_fst_some in EQ. apply alist_find_fst_none in MISS.
    exfalso. apply MISS.
    eapply nodup_eqlen_in_rev.
    - instantiate (1:= List.map fst fl_tgt).
      rewrite !map_length, SIM.(sim_length); eauto.
    - eauto.
    - i. destruct (alist_find x fl_src) eqn: AEQ; cycle 1.
      { apply alist_find_fst_none in AEQ. ss. }
      eapply SIM.(sim_fnsems) in AEQ. des.
      apply alist_find_fst_some in AEQ. eauto.
    - eauto.
  Qed.
  
End MODSEMR.

End MSim.

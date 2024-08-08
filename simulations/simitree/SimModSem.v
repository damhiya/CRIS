Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import EventsRed Mod Events.
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

Require Import SimGlobal SimInitial.
Require Import Red IRed.


Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIM.
  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf : world -> W -> Prop.
  Variable le: relation world.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree modE Any.t).



  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | sim_itree_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)

  | sim_itree_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          _sim_itree sim_itree RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          _sim_itree sim_itree RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (IO fn varg rvs) >>= k_src)
                 (st_tgt, trigger (IO fn varg rvs) >>= k_tgt)

  | sim_itree_inline_src
      f_src f_tgt w st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: _sim_itree sim_itree RR true f_tgt w (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_inline_tgt
      f_src f_tgt w st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: _sim_itree sim_itree RR f_src true w (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, i_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: _sim_itree sim_itree RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)

  | sim_itree_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: _sim_itree sim_itree RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)  

  | sim_itree_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_progress
      w0 st_src st_tgt 
      i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR true true w0 (st_src, i_src) (st_tgt, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             st_src st_tgt (ret_src ret_tgt: Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Definition init_rel (w0: world) (st_src st_tgt ret_src ret_tgt: Any.t) :=
    exists w1: world, (<<WLE: le w0 w1>> /\ <<WF: wf w1 (ret_src, ret_tgt)>> ).

  Definition sim_itree o_src o_tgt w0 : relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Definition sim_itree_init w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (init_rel w0) false false w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop) 
        (P: bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
        (RET: forall
            f_src f_tgt w0 st_src st_tgt
            v_src v_tgt
            (RET: RR st_src st_tgt v_src v_tgt),
            P f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt))
        (CALL: forall
            f_src f_tgt w w0 st_src st_tgt
            fn varg k_src k_tgt
            (WF: wf w0 (st_src, st_tgt))
            (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
              (st_tgt, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            f_src f_tgt w0 st_src st_tgt
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret)),
            P f_src f_tgt w0 (st_src, trigger (IO fn varg rvs) >>= k_src)
              (st_tgt, trigger (IO fn varg rvs) >>= k_tgt))
        (INLINESRC: forall
            f_src f_tgt w0 st_src st_tgt
            f fn varg k_src i_tgt
            (FUN: alist_find fn fl_src = Some f)
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt))
        (INLINETGT: forall
            f_src f_tgt w0 st_src st_tgt
            f fn varg i_src k_tgt
            (FUN: alist_find fn fl_tgt = Some f)
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt)),
            P f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt))            
        (TAUSRC: forall
            f_src f_tgt w0 st_src st_tgt
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt))
        (TAUTGT: forall
            f_src f_tgt w0 st_src st_tgt
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt))            
        (CHOOSESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X x k_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
              (st_tgt, i_tgt))
        (CHOOSETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)>> /\ <<IH: P f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)>>),
            P f_src f_tgt w0 (st_src, i_src)
              (st_tgt, trigger (Choose X) >>= k_tgt))
        (TAKESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)>> /\ <<IH: P true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)>>),
            P f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
              (st_tgt, i_tgt))
        (TAKETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X x i_src k_tgt
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)),
            P f_src f_tgt w0 (st_src, i_src)
              (st_tgt, trigger (Take X) >>= k_tgt))
        (SUPDATESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X k_src i_tgt
            (run: Any.t -> Any.t * X )
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt))
        (SUPDATETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X i_src k_tgt
            (run: Any.t -> Any.t * X )
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
            (IH:  P f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt)))),

            P f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt))       
        (PROGRESS: forall
            w0 st_src st_tgt
            i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src, i_src) (st_tgt, i_tgt)),
            P true true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      forall f_src f_tgt w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR f_src f_tgt w0 st_src st_tgt),
        P f_src f_tgt w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM; et.
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | sim_itree_indC_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  | sim_itree_indC_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          sim_itree _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                     (st_tgt, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (IO fn varg rvs) >>= k_src)
                     (st_tgt, trigger (IO fn varg rvs) >>= k_tgt)

  | sim_itree_indC_inline_src
      f_src f_tgt w0 st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_inline_tgt
      f_src f_tgt w0 st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)
 
  | sim_itree_indC_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_indC_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_indC_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src)
                     (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_indC_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src)
                     (st_tgt, trigger (Take X) >>= k_tgt)
  
  | sim_itree_indC_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: sim_itree _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply sim_itree_mon; et. i. eapply rclo8_base. et. }
    { econs 3; eauto. i. eapply sim_itree_mon; et. i. eapply rclo8_base. eauto. }
    { econs 4; et. eapply sim_itree_mon; et. eapply rclo8_base. }
    { econs 5; et. eapply sim_itree_mon; et. eapply rclo8_base. }
    { econs 6; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
    { econs 13; eauto. des. esplits; eauto.  eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | sim_itreeC_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  | sim_itreeC_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          r _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          r _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (IO fn varg rvs) >>= k_src)
                 (st_tgt, trigger (IO fn varg rvs) >>= k_tgt)

  | sim_itreeC_inline_src
      f_src f_tgt w0 st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: r _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_inline_tgt
      f_src f_tgt w0 st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itreeC_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itreeC_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)


  | sim_itreeC_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: r _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)
  | sim_itreeC_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: r _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: r _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
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
    { guclo sim_itree_indC_spec. econs 13; eauto.  gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR w r g st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto. 
  Qed.


  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type)
                           (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM; i; clarify; et.
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto. }
  Qed.


  Definition sim_fsem: relation (Any.t -> itree modE Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree modE Any.t)) := RelProd eq sim_fsem.

  Variant lflagC (r: forall (R_src R_tgt: Type)
    (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1  <8= r2)
    :
      @lflagC r1  <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC  <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM; i; clarify; et.
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 14; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down  R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up  R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. 
    i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify; try (guclo sim_itree_indC_spec; econs; et).
    { i. gstep. econs; et. gfinal. left. et. }
    { i. gstep. econs; et. gfinal. left. et. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { eapply sim_itree_flag_down. gfinal. right. eapply paco8_mon; eauto. ss. }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop):
    forall S_src S_tgt (SS: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> world -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1
      R_src R_tgt RR
      (st_src st_tgt: Any.t)
      (i_src: itree modE R_src) (i_tgt: itree modE R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))

      S_src S_tgt SS
      (k_src: ktree modE R_src S_src) (k_tgt: ktree modE R_tgt S_tgt)
      (SIMK: forall st_src0 st_tgt0 vret_src vret_tgt (SIM: RR st_src0 st_tgt0 vret_src vret_tgt), s _ _ SS false false w1 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src, ITree.bind i_src k_src) (st_tgt, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon 
        r1 r2 s1 s2
        (LEr: r1  <8= r2) (LEs: s1  <8= s2)
    :
      lbindR r1 s1  <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src, i_src). remember(st_tgt, i_tgt).
    revert st_src i_src st_tgt i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM; i; clarify; grind; try (econs; et).
    - exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon with (f_src0 := false) (f_tgt0 := false); ss.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et. 
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et. 
    - eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC  <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.


Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr fl,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 fl fl false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger.
    gstep.
    eapply sim_itree_call; ss. ii. subst. econs; et.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction s.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction c.
    { guclo sim_itree_indC_spec. econs 9. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 10. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.



(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem.t).
  
  Let fl_src := ms_src.(ModSem.fnsems).
  Let fl_tgt := ms_tgt.(ModSem.fnsems).
  Let init_src := ms_src.(ModSem.initial_st).
  Let init_tgt := ms_tgt.(ModSem.initial_st).

  Let W: Type := (Any.t) * (Any.t).
  
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le fl_src fl_tgt) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial: simT (fun x y => exists w, wf w (x, y)) false false init_src init_tgt;
    (* sim_initial: exists w_init,
                 sim_itree_init wf le [] [] w_init (tt↑, resum_itr ms_src.(ModSem.init_st)) (tt↑, resum_itr ms_tgt.(ModSem.init_st)); *)
                  (* init_st will be given as 'itree eventE Any.t', why not directly using sim_global?*)
  }.

End SIMMODSEM.

Lemma self_sim (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms) at 3 4.
    induction a; ii; ss.
    econs; et. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - eapply self_simT. ss.
Qed.

End ModSemPair.


Module ModPair.
Section SIMMOD.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

End ModPair.

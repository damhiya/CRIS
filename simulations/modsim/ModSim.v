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

  Variable world: Type.

  Let W: Type := nat * (Any.t) * (Any.t).
  Variable wf : world -> W -> Prop.
  Variable le: relation world.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree modE Any.t).
  Variable my_tid : nat.

  Hypothesis le_refl: Reflexive le.
  Hypothesis le_trans: Transitive le.

  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=

  | sim_itree_ret
      ps pt w w0 nths st_src st_tgt
      v_src v_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (RET: RR nths st_src st_tgt v_src v_tgt)
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, Ret v_src) (st_tgt, Ret v_tgt)

  | sim_itree_call
      ps pt w w0 nths st_src st_tgt
      fn varg k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 vret nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          _sim_itree sim_itree RR true true w1 nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_io
      ps pt w nths st_src st_tgt
      I O fn (varg: I) k_src k_tgt
      (K: forall (vret: O),
          _sim_itree sim_itree RR true true w nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (IO fn varg) >>= k_src)
                 (st_tgt, trigger (IO fn varg) >>= k_tgt)

  | sim_itree_inline_src
      ps pt w nths st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: _sim_itree sim_itree RR true pt w nths (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_inline_tgt
      ps pt w nths st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: _sim_itree sim_itree RR ps true w nths (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, i_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_tau_src
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR true pt w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_tau_tgt
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR ps true w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_choose_src
      ps pt w nths st_src st_tgt
      X x k_src i_tgt
      (K: _sim_itree sim_itree RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_choose_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_take_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_take_tgt
      ps pt w nths st_src st_tgt
      X x i_src k_tgt
      (K: _sim_itree sim_itree RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)

  | sim_itree_supdate_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: _sim_itree sim_itree RR true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)  

  | sim_itree_supdate_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: _sim_itree sim_itree RR ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_spawn
      ps pt w nths st_src st_tgt
      fn varg k_src k_tgt
      (K: _sim_itree sim_itree RR true true w (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Spawn fn varg) >>= k_src)
                 (st_tgt, trigger (Spawn fn varg) >>= k_tgt)

  | sim_itree_yield
      ps pt w w0 nths st_src st_tgt
      tid k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          _sim_itree sim_itree RR true true w1 nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger (Yield tid) >>= k_src)
                 (st_tgt, trigger (Yield tid) >>= k_tgt)
                 
  | sim_itree_tid
      ps pt w nths st_src st_tgt
      k_src k_tgt
      (K: _sim_itree sim_itree RR true true w nths (st_src, k_src my_tid) (st_tgt, k_tgt my_tid))
    :
      _sim_itree sim_itree RR ps pt w nths (st_src, trigger Tid >>= k_src)
                 (st_tgt, trigger Tid >>= k_tgt)

  | sim_itree_progress
      w w0 nths st_src st_tgt 
      i_src i_tgt
      (WLE: le w w0)
      (SIM: sim_itree _ _ RR false false w0 nths (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR true true w nths (st_src, i_src) (st_tgt, i_tgt)
  .

  Definition final_rel (nths: nat) (st_src st_tgt ret_src ret_tgt: Any.t) :=
    ret_src = ret_tgt.

  Definition sim_itree o_src o_tgt w : nat -> relation _ :=
    paco9 _sim_itree bot9 _ _ final_rel o_src o_tgt w.

  Lemma sim_itree_mon: monotone9 _sim_itree.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

  Lemma sim_itree_wmon (w w0: world) r R_src R_tgt RR ps pt nths src tgt
    (SIM: @_sim_itree r R_src R_tgt RR ps pt w0 nths src tgt)
    (WLE: le w w0)
    :
    _sim_itree r RR ps pt w nths src tgt.
  Proof.
    induction SIM; eauto.
  Qed.

  Lemma sim_itree_ind
        R_src R_tgt (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop) 
        (P: bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
        (RET: forall
            ps pt w w0 nths st_src st_tgt
            v_src v_tgt
            (WLE: le w w0)
            (WF: wf w0 (nths, st_src, st_tgt))
            (RET: RR nths st_src st_tgt v_src v_tgt),
            P ps pt w nths (st_src, Ret v_src) (st_tgt, Ret v_tgt))
        (CALL: forall
            ps pt w w0 nths st_src st_tgt
            fn varg k_src k_tgt
            (WLE: le w w0)
            (WF: wf w0 (nths, st_src, st_tgt))
            (K: forall w1 vret nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
                paco9 _sim_itree bot9 _ _ RR true true w1 nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P ps pt w nths (st_src, trigger (Call fn varg) >>= k_src)
              (st_tgt, trigger (Call fn varg) >>= k_tgt))
        (IO: forall
            ps pt w nths st_src st_tgt
            I O fn (varg: I) k_src k_tgt
            (K: forall (vret: O),
                paco9 _sim_itree bot9 _ _ RR true true w nths (st_src, k_src vret) (st_tgt, k_tgt vret)),
            P ps pt w nths (st_src, trigger (IO fn varg) >>= k_src)
              (st_tgt, trigger (IO fn varg) >>= k_tgt))
        (INLINESRC: forall
            ps pt w nths st_src st_tgt
            f fn varg k_src i_tgt
            (FUN: alist_find fn fl_src = Some f)
            (K: paco9 _sim_itree bot9 _ _ RR true pt w nths (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
            (IH: P true pt w nths (st_src, (f varg) >>= k_src) (st_tgt, i_tgt)),
            P ps pt w nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt))
        (INLINETGT: forall
            ps pt w nths st_src st_tgt
            f fn varg i_src k_tgt
            (FUN: alist_find fn fl_tgt = Some f)
            (K: paco9 _sim_itree bot9 _ _ RR ps true w nths (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
            (IH: P ps true w nths (st_src, i_src) (st_tgt, (f varg) >>= k_tgt)),
            P ps pt w nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt))            
        (TAUSRC: forall
            ps pt w nths st_src st_tgt
            i_src i_tgt
            (K: paco9 _sim_itree bot9 _ _ RR true pt w nths (st_src, i_src) (st_tgt, i_tgt))
            (IH: P true pt w nths (st_src, i_src) (st_tgt, i_tgt)),
            P ps pt w nths (st_src, tau;; i_src) (st_tgt, i_tgt))
        (TAUTGT: forall
            ps pt w nths st_src st_tgt
            i_src i_tgt
            (K: paco9 _sim_itree bot9 _ _ RR ps true w nths (st_src, i_src) (st_tgt, i_tgt))
            (IH: P ps true w nths (st_src, i_src) (st_tgt, i_tgt)),
            P ps pt w nths (st_src, i_src) (st_tgt, tau;; i_tgt))            
        (CHOOSESRC: forall
            ps pt w nths st_src st_tgt
            X x k_src i_tgt
            (K: paco9 _sim_itree bot9 _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
            (IH: P true pt w nths (st_src, k_src x) (st_tgt, i_tgt)),
            P ps pt w nths (st_src, trigger (Choose X) >>= k_src)
              (st_tgt, i_tgt))
        (CHOOSETGT: forall
            ps pt w nths st_src st_tgt
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco9 _sim_itree bot9 _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x)>> /\ <<IH: P ps true w nths (st_src, i_src) (st_tgt, k_tgt x)>>),
            P ps pt w nths (st_src, i_src)
              (st_tgt, trigger (Choose X) >>= k_tgt))
        (TAKESRC: forall
            ps pt w nths st_src st_tgt
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco9 _sim_itree bot9 _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt)>> /\ <<IH: P true pt w nths (st_src, k_src x) (st_tgt, i_tgt)>>),
            P ps pt w nths (st_src, trigger (Take X) >>= k_src)
              (st_tgt, i_tgt))
        (TAKETGT: forall
            ps pt w nths st_src st_tgt
            X x i_src k_tgt
            (K: paco9 _sim_itree bot9 _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
            (IH: P ps true w nths (st_src, i_src) (st_tgt, k_tgt x)),
            P ps pt w nths (st_src, i_src)
              (st_tgt, trigger (Take X) >>= k_tgt))
        (SUPDATESRC: forall
            ps pt w nths st_src st_tgt
            X k_src i_tgt
            (run: Any.t -> Any.t * X )
            (K: paco9 _sim_itree bot9 _ _ RR true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
            (IH: P true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt)),
            P ps pt w nths (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt))
        (SUPDATETGT: forall
            ps pt w nths st_src st_tgt
            X i_src k_tgt
            (run: Any.t -> Any.t * X )
            (K: paco9 _sim_itree bot9 _ _ RR ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
            (IH:  P ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt)))),

            P ps pt w nths (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt))
        (SPAWN: forall
            ps pt w nths st_src st_tgt
            fn varg k_src k_tgt
            (K: paco9 _sim_itree bot9 _ _ RR true true w (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths)),
            P ps pt w nths (st_src, trigger (Spawn fn varg) >>= k_src)
              (st_tgt, trigger (Spawn fn varg) >>= k_tgt))
        (YIELD: forall
            ps pt w w0 nths st_src st_tgt
            tid k_src k_tgt
            (WLE: le w w0)
            (WF: wf w0 (nths, st_src, st_tgt))
            (K: forall w1 nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
                paco9 _sim_itree bot9 _ _ RR true true w1 nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt)),
            P ps pt w nths (st_src, trigger (Yield tid) >>= k_src)
              (st_tgt, trigger (Yield tid) >>= k_tgt))
        (TID: forall
            ps pt w nths st_src st_tgt
            k_src k_tgt
            (K: paco9 _sim_itree bot9 _ _ RR true true w nths (st_src, k_src my_tid) (st_tgt, k_tgt my_tid)),
            P ps pt w nths (st_src, trigger Tid >>= k_src)
              (st_tgt, trigger Tid >>= k_tgt))
        
        (PROGRESS: forall
            w w0 nths st_src st_tgt
            i_src i_tgt
            (WLE: le w w0)
            (SIM: paco9 _sim_itree bot9 _ _ RR false false w0 nths (st_src, i_src) (st_tgt, i_tgt)),
            P true true w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      forall ps pt w nths st_src st_tgt
             (SIM: paco9 _sim_itree bot9 _ _ RR ps pt w nths st_src st_tgt),
        P ps pt w nths st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM; et.
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | sim_itree_indC_ret
      ps pt w w0 nths st_src st_tgt
      v_src v_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (RET: RR nths st_src st_tgt v_src v_tgt)
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, Ret v_src) (st_tgt, Ret v_tgt)

  | sim_itree_indC_call
      ps pt w w0 nths st_src st_tgt
      fn varg k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 vret nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          sim_itree _ _ RR true true w1 nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src)
                     (st_tgt, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_io
      ps pt w nths st_src st_tgt
      I O fn (varg: I) k_src k_tgt
      (K: forall (vret: O),
          sim_itree _ _ RR true true w nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (IO fn varg) >>= k_src)
                     (st_tgt, trigger (IO fn varg) >>= k_tgt)

  | sim_itree_indC_inline_src
      ps pt w nths st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: sim_itree _ _ RR true pt w nths (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_inline_tgt
      ps pt w nths st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: sim_itree _ _ RR ps true w nths (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)
 
  | sim_itree_indC_tau_src
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR true pt w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_indC_tau_tgt
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR ps true w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_indC_choose_src
      ps pt w nths st_src st_tgt
      X x k_src i_tgt
      (K: sim_itree _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Choose X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_choose_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, i_src)
                     (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_indC_take_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Take X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_take_tgt
      ps pt w nths st_src st_tgt
      X x i_src k_tgt
      (K: sim_itree _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, i_src)
                     (st_tgt, trigger (Take X) >>= k_tgt)
  
  | sim_itree_indC_supdate_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: sim_itree _ _ RR true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_supdate_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: sim_itree _ _ RR ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_indC_spawn
      ps pt w nths st_src st_tgt
      fn varg k_src k_tgt
      (K: sim_itree _ _ RR true true w (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Spawn fn varg) >>= k_src)
                     (st_tgt, trigger (Spawn fn varg) >>= k_tgt)

  | sim_itree_indC_yield
      ps pt w w0 nths st_src st_tgt
      tid k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          sim_itree _ _ RR true true w1 nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger (Yield tid) >>= k_src)
                     (st_tgt, trigger (Yield tid) >>= k_tgt)
                     
  | sim_itree_indC_tid
      ps pt w nths st_src st_tgt
      k_src k_tgt
      (K: sim_itree _ _ RR true true w nths (st_src, k_src my_tid) (st_tgt, k_tgt my_tid))
    :
      sim_itree_indC  sim_itree RR ps pt w nths (st_src, trigger Tid >>= k_src)
                     (st_tgt, trigger Tid >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone9 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.
  
  Lemma sim_itree_indC_spec:
    sim_itree_indC <10= gupaco9 (_sim_itree) (cpn9 _sim_itree).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
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
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=

  | sim_itreeC_ret
      ps pt w w0 nths st_src st_tgt
      v_src v_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (RET: RR nths st_src st_tgt v_src v_tgt)
    :
      sim_itreeC r g RR ps pt w nths (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  | sim_itreeC_call
      ps pt w w0 nths st_src st_tgt
      fn varg k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 vret nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          r _ _ RR true true w1 nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

    | sim_itreeC_io
      ps pt w nths st_src st_tgt
      I O fn (varg: I) k_src k_tgt
      (K: forall (vret: O),
          r _ _ RR true true w nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (IO fn varg) >>= k_src)
                 (st_tgt, trigger (IO fn varg) >>= k_tgt)

  | sim_itreeC_inline_src
      ps pt w nths st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: r _ _ RR true pt w nths (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_inline_tgt
      ps pt w nths st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: r _ _ RR ps true w nths (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itreeC_tau_src
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR true pt w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itreeC_tau_tgt
      ps pt w nths st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR ps true w nths (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, i_src) (st_tgt, tau;; i_tgt)


  | sim_itreeC_choose_src
      ps pt w nths st_src st_tgt
      X x k_src i_tgt
      (K: r _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_choose_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR ps pt w nths (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true pt w nths (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_take_tgt
      ps pt w nths st_src st_tgt
      X x i_src k_tgt
      (K: r _ _ RR ps true w nths (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR ps pt w nths (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)
  | sim_itreeC_supdate_src
      ps pt w nths st_src st_tgt
      X k_src i_tgt
      (run: Any.t -> Any.t * X )
      (K: r _ _ RR true pt w nths (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_supdate_tgt
      ps pt w nths st_src st_tgt
      X i_src k_tgt
      (run: Any.t -> Any.t * X )
      (K: r _ _ RR ps true w nths (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itreeC r g RR ps pt w nths (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itreeC_spawn
      ps pt w nths st_src st_tgt
      fn varg k_src k_tgt
      (K: r _ _ RR true true w (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Spawn fn varg) >>= k_src)
                 (st_tgt, trigger (Spawn fn varg) >>= k_tgt)

  | sim_itreeC_yield
      ps pt w w0 nths st_src st_tgt
      tid k_src k_tgt
      (WLE: le w w0)
      (WF: wf w0 (nths, st_src, st_tgt))
      (K: forall w1 nths0 st_src0 st_tgt0 (NTHS: my_tid < nths0) (WLE: le w0 w1) (WF: wf w1 (nths0, st_src0, st_tgt0)),
          r _ _ RR true true w1 nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger (Yield tid) >>= k_src)
                 (st_tgt, trigger (Yield tid) >>= k_tgt)
                 
  | sim_itreeC_tid
      ps pt w nths st_src st_tgt
      k_src k_tgt
      (K: r _ _ RR true true w nths (st_src, k_src my_tid) (st_tgt, k_tgt my_tid))
    :
      sim_itreeC r g RR ps pt w nths (st_src, trigger Tid >>= k_src)
                 (st_tgt, trigger Tid >>= k_tgt)
  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <11= gpaco9 (_sim_itree) (cpn9 _sim_itree).
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
    { guclo sim_itree_indC_spec. econs 13; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 14; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 15; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 16; eauto. gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g:
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
    gstep. destruct st_src, st_tgt. econs; eauto. 
  Qed.


  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type)
                           (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
        R_src R_tgt (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
        ps0 pt0 ps1 pt1 w nths st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR ps0 pt0 w nths st_src st_tgt)
        (SRC: ps0 = true -> ps1 = true)
        (TGT: pt0 = true -> pt1 = true)
    :
      @_sim_itree sim_itree _ _ RR ps1 pt1 w nths st_src st_tgt.
  Proof.
    revert ps1 pt1 SRC TGT.
    induction SIM; i; clarify; et.
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto. }
  Qed.

  Definition sim_fsem: relation (Any.t -> itree modE Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w nths mrs_src mrs_tgt (NTHS: my_tid < nths) (SIMMRS: wf w (nths, mrs_src, mrs_tgt)),
                 sim_itree false false w nths (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  (* Definition sim_fnsem: relation (string * (Any.t -> itree modE Any.t)) := RelProd eq sim_fsem. *)

  Variant lflagC (r: forall (R_src R_tgt: Type)
    (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: nat -> Any.t -> Any.t -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> nat -> Any.t * itree modE R_src -> Any.t * itree modE R_tgt -> Prop :=
  | lflagC_intro
      ps0 ps1 pt0 pt1 w nths st_src st_tgt
      (SIM: r _ _ RR ps0 pt0 w nths st_src st_tgt)
      (SRC: ps0 = true -> ps1 = true)
      (TGT: pt0 = true -> pt1 = true)
    :
      lflagC r RR ps1 pt1 w nths st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1  <9= r2)
    :
      @lflagC r1  <9= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <10= gupaco9 (_sim_itree) (cpn9 _sim_itree).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM; i; clarify; et.
    exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto.
    eapply rclo9_base; auto.
  Qed.

  Lemma sim_itree_flag_down  R0 R1 RR r g w nths st_src st_tgt ps pt
        (SIM: gpaco9 _sim_itree (cpn9 _sim_itree) r g R0 R1 RR false false w nths st_src st_tgt)
    :
      gpaco9 _sim_itree (cpn9 _sim_itree) r g R0 R1 RR ps pt w nths st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up  R0 R1 RR w nths st_src st_tgt ps pt
        (SIM: paco9 _sim_itree bot9 R0 R1 RR true true w nths st_src st_tgt)
    :
      paco9 _sim_itree bot9 R0 R1 RR ps pt w nths st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w nths st_src st_tgt ps pt b b0 SIM.
    gcofix CIH. 
    i. revert ps pt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, nths, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w nths st_src st_tgt => set P
    end.
    revert b b0 w nths st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify; try (guclo sim_itree_indC_spec; econs; et).
    { i. gstep. econs; et. gfinal. left. et. }
    { i. gstep. econs; et. gfinal. left. et. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { i. gstep. econs; et. gfinal. left. et. }
    { i. gstep. econs; et. gfinal. left. et. }
    { i. gstep. econs; et. gfinal. left. et. }
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco9_mon.
      - punfold SIM. pstep. eapply sim_itree_wmon; eauto.
      - ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop):
    forall S_src S_tgt (SS: nat -> Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> world -> nat -> Any.t * itree modE S_src -> Any.t * itree modE S_tgt -> Prop :=

  | lbindR_intro
      ps pt w
      R_src R_tgt RR
      nths (st_src st_tgt: Any.t)
      (i_src: itree modE R_src) (i_tgt: itree modE R_tgt)
      (NTHS: my_tid < nths)
      (SIM: r _ _ RR ps pt w nths (st_src, i_src) (st_tgt, i_tgt))

      S_src S_tgt SS
      (k_src: ktree modE R_src S_src) (k_tgt: ktree modE R_tgt S_tgt)
      (SIMK: forall w0 nths0 st_src0 st_tgt0 vret_src vret_tgt (NTHS: my_tid < nths0) (WLE: le w w0) (SIM: RR nths0 st_src0 st_tgt0 vret_src vret_tgt), s _ _ SS false false w0 nths0 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt))
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
    induction SIM; i; clarify; grind; try by (econs; eauto).
    - exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon with (ps0 := false) (pt0 := false); ss.
      eapply sim_itree_mon; [eapply sim_itree_wmon|]; eauto.
      i. eapply rclo9_base. auto.
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et. 
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et.
    - econs; eauto. eapply rclo9_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC  <10= gupaco9 (_sim_itree) (cpn9 (_sim_itree)).
  Proof.
    intros. eapply wrespect9_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM_ITREE.

Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn9_wcompat: paco.

(*
Section SIM_ITREE_PROP.

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

End SIM_ITREE_PROP.
*)

(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)

Require Import Program.

Module ModSemR.
Section MODSEMR.

  Variable (ms_src ms_tgt: ModSem.t).
  
  Let fl_src := ms_src.(ModSem.fnsems).
  Let fl_tgt := ms_tgt.(ModSem.fnsems).
  Let st_src := ms_src.(ModSem.initial_st).
  Let st_tgt := ms_tgt.(ModSem.initial_st).

  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> nat * Any.t * Any.t -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_initial:
      exists (w: world), wf w (1, st_src, st_tgt);
    sim_length:
      List.length fl_src = List.length fl_tgt;
    (* sim_miss: *)
    (*   forall fn (MISS: alist_find fn fl_src = None), *)
    (*   alist_find fn fl_tgt = None; *)
    sim_fnsems:
      forall fn fs (FIND: alist_find fn fl_src = Some fs),
      exists ft, alist_find fn fl_tgt = Some ft /\
        forall my_tid, @sim_fsem world wf le fl_src fl_tgt my_tid fs ft;
  }.

  Lemma wf_sim_miss
    world wf le
    (WF: ModSem.wf ms_src) 
    (sim_length: List.length fl_src = List.length fl_tgt)
    (sim_fnsems:
      forall fn fs (FIND: alist_find fn fl_src = Some fs),
      exists ft, alist_find fn fl_tgt = Some ft /\
        forall my_tid, @sim_fsem world wf le fl_src fl_tgt my_tid fs ft)
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
      rewrite !map_length, sim_length. eauto.
    - eauto.
    - i. destruct (alist_find x fl_src) eqn: AEQ; cycle 1.
      { apply alist_find_fst_none in AEQ. ss. }
      eapply sim_fnsems in AEQ. des.
      apply alist_find_fst_some in AEQ. eauto.
    - eauto.
  Qed.
  
End MODSEMR.

(* Lemma self_sim (ms: ModSem.t): *)
(*   sim ms ms. *)
(* Proof. *)
(*   econs; et. *)
(*   { instantiate (1:= top2). ss. } *)
(*   { instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). *)
(*     i. exists tt. esplits; eauto. } *)
(*   { ii. esplits; eauto. *)
(*     ii. subst. destruct w. apply self_sim_itree. } *)
(* Qed. *)

End ModSemR.

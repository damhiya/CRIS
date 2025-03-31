Require Import sflib Basics Program.

Definition level := nat.

(****

 Library for Polynomial Functors

 ****)

(* Stratified Algebraic Theory *)

Module SAT.

  Class t : Type := {
    ops : Type;
    arity : ops -> forall (term_prev: Type), Type;
  }.

End SAT.

(* Global Algebraic Theory *)
Module GAT.

  Class t : Type := __GATOM : nat -> SAT.t.

  Class inG (F : SAT.t) (GF : t) : Type := {
    inG_id : nat;
    inG_prf : F = GF inG_id;
  }.

End GAT.

(****

 Library for SAT

 ****)

(* Term *)
Module GTerm. Section GTerm.
  Context `{α: GAT.t}.

  Inductive term {term_prev: Type} : Type :=
  | _lift (p: term_prev) : term
  | _cur i (op: (α i).(SAT.ops)) (args: (α i).(SAT.arity) op term_prev -> term)
  .

  Fixpoint _t (n : level) : Type :=
    match n with
    | O => Empty_set
    | S m => term (term_prev:=_t m) 
    end.

  Definition t_prev (n : level) : Type := _t n.

  Definition t (n : level) : Type := t_prev (S n).

  Definition lift {n} (p : t n) : t (S n) := _lift p.

  Fixpoint liftn k {n} (p : t n) : t (k+n) :=
    match k return t (k+n) with
    | 0 => p
    | S k' => lift (liftn k' p)
    end.
End GTerm. End GTerm.

(* Semantic Domain *)
Module SemDom.

  Class t : Type := {
      dom: Type;
    }.

End SemDom.

(* Interpretation for the constructors in a group *)
Module SATIntp.

  Section SEM.

  Context `{Δ: SemDom.t}.
  Context `{α: GAT.t}.
  Context `{A: SAT.t}.

  Class t : Type := 
    sem:
      forall n (op: A.(SAT.ops))
             (args: A.(SAT.arity) op (@GTerm.t_prev α n) -> GTerm.t n)
             (Args: A.(SAT.arity) op (@GTerm.t_prev α n) -> SemDom.dom),
        SemDom.dom
  .

  End SEM.

End SATIntp.

(* Interpretation for the constructors in all groups *)
Module GATIntp.

  Section GSEM.

  Context `{Δ : SemDom.t}.

  Class t `{α: GAT.t}: Type :=
    gsem : forall i, @SATIntp.t Δ α (α i).

  Class inG (A: SAT.t) (α: GAT.t) (B: @SATIntp.t Δ α A) (β: t) :=
    {
      inG_id: nat;
      inG_prf: existT _ A B = existT _ (α inG_id) (β inG_id);
    }.
  
  End GSEM.

End GATIntp.

(* Semantics for the syntax *)
Module GTermSem.

  Section SEM.

  Context `{Δ: SemDom.t}.
  Context `{α: GAT.t}.
  Context `{β: @GATIntp.t Δ α}.

  Fixpoint _t n : GTerm.t_prev n -> SemDom.dom :=
    match n with
    | O => fun x => match x with end
    | S m =>
      fix _t_aux (syn : GTerm.t_prev (S m)) : SemDom.dom :=
        match syn with
        | GTerm._lift p => _t m p
        | GTerm._cur i op args => β i m op args (compose _t_aux args)
        end
    end.

  Definition t_prev n : GTerm.t_prev n -> SemDom.dom := _t n.
  
  Definition t n : GTerm.t n -> SemDom.dom := t_prev (S n).

  Program Definition cur
    `{A: SAT.t} `{B: @SATIntp.t Δ α A} `{IN: @GATIntp.inG Δ A α B β} {n}
    (op: A.(SAT.ops)) (args: A.(SAT.arity) op (GTerm.t_prev n) -> GTerm.t n) : GTerm.t n.
    destruct IN. inversion inG_prf. subst.
    exact (GTerm._cur inG_id op args).
  Defined.
  
  End SEM.
  
End GTermSem.

Module SATRed.
  
  Section RED.

  Context `{Δ: SemDom.t}.
  Context `{α: GAT.t}.
  Context `{β: @GATIntp.t Δ α}.

  Lemma cur `{A: SAT.t} `{B: @SATIntp.t Δ α A} `{IN: @GATIntp.inG Δ A α B β} n op args:
    GTermSem.t n (GTermSem.cur op args) = B n op args (compose (GTermSem.t n) args).
  Proof using.
    destruct IN eqn : EQ. subst. dependent destruction inG_prf. reflexivity.
  Qed.

  Lemma lift_0 t d:
    GTermSem.t_prev 1 (GTerm._lift t) = d.
  Proof using. destruct t. Qed.

  Lemma lift n (t : GTerm.t n) :
    GTermSem.t (S n) (GTerm.lift t) = GTermSem.t n t.
  Proof using. reflexivity. Qed.

  End RED.

End SATRed.

Global Opaque GTermSem.cur.
Global Opaque GTermSem.t.

(** Notations *)

Declare Scope SAT_scope.
Delimit Scope SAT_scope with SAT.
Bind Scope SAT_scope with GTerm.t.

Local Open Scope SAT_scope.

Notation "'⟦' F ',' n '⟧'" := (GTermSem.t n F).
Notation "'⟦' F '⟧'" := (GTermSem.t _ F).
Notation "'⟨' op ',' args '⟩'" := (GTermSem.cur op args) : SAT_scope.
Notation "⤉ P" := (GTerm.lift P) (at level 20) : SAT_scope.

(* Simple reduction tactics. *)

Global Opaque GTerm.t_prev.
Global Opaque GTerm.t.

(* TODO : improve these tactics *)
From stdpp Require Import ssreflect.
Ltac SAT_red :=
  (hrepeat do 1
    tryany (do 1 rewrite !@SATRed.cur)
    tryany (do 1 rewrite !@SATRed.lift)
           (try (change (GTerm.t_prev (S ?n)) with (); fail 1);
            change (GTerm.t_prev (S ?n)) with (GTerm.t n)));
  simpl.

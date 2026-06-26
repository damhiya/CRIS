
(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a weaker, coinductive notion of equivalence,
    [eqit], which can be intuitively thought of as a form of extensional
    equality. We shall rely extensively on setoid rewriting.
 *)

(* begin hide *)
From Stdlib Require Import
     Structures.Orders (* Hint Unfold is_true *)
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITreeS Require Import
     Basics
     ITreeDefinition.

From CRIS Require Import sflib.

Local Open Scope itree_scope.


(** ** Coinductive reasoning with Paco *)

(** Similarly to the way we deal with cofixpoints explained in
    [Core.ITreeDefinition], coinductive properties are defined in two steps,
    as greatest fixed points of monotone relation transformers.

    - a _relation transformer_, a.k.a. _generating function_,
      is a function mapping relations to relations
      [gf : (i -> i -> Prop) -> (i -> i -> Prop)];
    - _monotonicity_ is with respect to relations ordered by set inclusion
      (a.k.a. implication, when viewed as predicates)
      [(r1 <2= r2) -> (gf r1 <2= gf r2)];
    - the Paco library provides a combinator [paco2] defining the greatest
      fixed point [paco2 gf] when [gf] is indeed monotone.

    By thus avoiding [CoInductive] to define coinductive properties,
    Paco spares us from thinking about guardedness of proof terms,
    instead encoding a form of productivity visibly in types.
 *)

(* Local Coercion is_true : bool >-> Sortclass. *)

Section eqit.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : iEvent} {R1 R2: Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Inductive eqitF (sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF sim (TauF m1) (TauF m2)
  | EqVis {u: Type} (e : E u) k1 k2
        (REL: forall v, sim (k1 v) (k2 v) : Prop):
      eqitF sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eqitF : itree.

  Definition eqit_ sim :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF sim (observe t1) (observe t2).
  Hint Unfold eqit_ : itree.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono x0 x1 sim sim'
        (IN: eqitF sim x0 x1)
        (LE: sim <2= sim'):
    eqitF sim' x0 x1.
  Proof.
    intros. induction IN; eauto with itree.
  Qed.

  Lemma eqit__mono : monotone2 (eqit_).
  Proof. do 2 red. intros. eapply eqitF_mono; eauto. Qed.

  Hint Resolve eqit__mono : paco.

  Definition eqit : itree E R1 -> itree E R2 -> Prop :=
    paco2 eqit_ bot2.

  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)

  Lemma id_wcompat:
    wcompatible2 eqit_ id.
  Proof.
    econstructor; eauto.
    intros. red in PR. eapply eqitF_mono; eauto.
    intros. gfinal. eauto.
  Qed.
  
End eqit.

(* begin hide *)
#[global] Hint Constructors eqitF : itree.
#[global] Hint Unfold eqit_ : itree.
#[global] Hint Resolve eqit__mono : paco.
#[global] Hint Resolve id_wcompat : paco.
#[global] Hint Unfold eqit : itree.

(** A notation of [eqit]. You can write [≅] using [[\cong]] in
    tex-mode *)

Infix "≅" := (eqit eq) (at level 70) : type_scope.

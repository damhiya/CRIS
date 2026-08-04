(** * General-purpose definitions *)

(** Not specific to itrees. *)

(* begin hide *)
From Stdlib Require
     Ensembles.

From Stdlib Require Import
     RelationClasses.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Data.Monads.StateMonad
     Data.Monads.ReaderMonad
     Data.Monads.OptionMonad
     Data.Monads.EitherMonad.

Import
  FunctorNotation
  MonadNotation.
Local Open Scope monad.
(* end hide *)

(** ** Parametric functions *)

(** A notation for a certain class of parametric functions.
    Some common names of things that can be represented by such a type:

    - Natural transformations (functor morphisms)
    - Monad morphisms
    - Event morphisms (if [E] and [F] are simply
      indexed types with no particular structure)
    - Event handlers (if [F] is a monad)
 *)

(** ** Common monads and transformers. *)

Module Monads.

Definition identity (a : Type) : Type := a.

Definition stateT (S : Type) (M: Type -> Type) (A : Type) : Type :=
  S -> M (S * A)%type.

#[global] Instance Functor_stateT {M: Type -> Type} {S: Type} {Fm : Functor M} : Functor (stateT S M)
  := {|
    fmap _ _ f := fun run s => fmap (fun sa => (fst sa, f (snd sa))) (run s)
    |}.

#[global] Instance Monad_stateT {M: Type -> Type} {S: Type} {Fm : Monad M} : Monad (stateT S M)
  := {|
    ret _ a := fun s => ret (s, a)
  ; bind _ _ t k := fun s =>
      sa <- t s ;;
      k (snd sa) (fst sa)
    |}.

End Monads.

(** ** Loop operator *)

(** [iter]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R].
 *)
Class MonadIter (M : Type -> Type) :=
  iter : forall {I R: Type}, (I -> M (I + R)%type) -> I -> M R.

#[global] Hint Mode MonadIter ! : typeclass_instances.

(** *** Transformer instances *)

(** And the standard transformers can lift [iter].

    Quite easily in fact, no [Monad] assumption needed.
 *)

#[global] Instance MonadIter_stateT {M: Type -> Type} {S: Type} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (Monads.stateT S M)
  :=
  fun _ _ step i s =>
    iter (fun si =>
      let s := fst si in
      let i := snd si in
      si' <- step i s;;
      ret match snd si' with
          | inl i' => inl (fst si', i')
          | inr r => inr (fst si', r)
          end) (s, i).

Notation iEvent := (Type -> Type) (only parsing).

Notation "E ~> F" := (forall T, E T -> F T)
  (at level 99, right associativity, only parsing) : type_scope.
(* The same level as [->]. *)
(* This might actually not be such a good idea. *)

(** Identity morphism. *)
Definition idM {E : iEvent} : E ~> E := fun _ e => e.

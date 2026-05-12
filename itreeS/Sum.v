(** * Sums of indexed types *)

(** In the context of interaction trees, events can be combined
    using this sum type. *)

(* begin hide *)

From ITreeS Require Import Basics.

Set Implicit Arguments.
Set Contextual Implicit.

(* end hide *)

(** Sum of type constructors [Type -> Type].

    [sum1 : (Type -> Type) -> (Type -> Type) -> (Type -> Type)]. *)
Variant sum1 (E1 E2 : iEvent) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).
Arguments inr1 {E1 E2} [X].
Arguments inl1 {E1 E2} [X].

(** An infix notation for convenience. *)
Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 59, right associativity) : type_scope.

(** The coproduct is case analysis on sums. *)
Definition case_sum1 {A B C : iEvent} (f : A ~> C) (g : B ~> C)
  : A +' B ~> C
  := fun _ ab =>
       match ab with
       | inl1 a => f _ a
       | inr1 b => g _ b
       end.

(** The empty indexed type. *)
Variant void1 : Type -> Type := .

(* Eliminate [void1]. *)
Definition elim_void1 {E: iEvent}
  : forall T : Type, void1 T -> E T :=
  fun T (v : void1 T) => match v with end.

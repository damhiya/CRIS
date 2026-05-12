(** * Category operations *)

(** Interfaces for programming with categories. *)

(** A category is represented by a type of objects [obj], and a type
    of morphisms [C : obj -> obj -> Type].

    The interface gives the signatures for the following operations
    (which may be defined independently).
    For any [a], [b], [c]):

    - [eq2 : C a b -> C a b -> Prop], equivalence of morphisms;

    - [id_ a : C a a], the identity morphism;
    - [cat : C a b -> C b c -> C a c], composition of morphisms;

    - [empty : C i a], the initial morphism (where [i] is the initial
      object);

    - [bimap : C a b -> C c d -> C (bif a b) (bif c d)], "vertical
      composition" of morphisms, where [bif] is a bifunctor
      (in our case it is the coproduct bifunctor);
    - [assoc_l], [assoc_r], [unit_l], [unit_l'], [unit_r], [unit_r']:
      natural isomorphisms of a tensor product [bif], making [C] a
      monoidal category;

    - [case_ : C a c -> C b c -> C (bif a b) c], "case analysis"
      of a coproduct [bif];
    - [inl_ : C a (bif a b)], left injection in a coproduct [bif];
    - [inr_ : C b (bif a b)], right injection;

    - [iter : C a (bif a b) -> C a b], loop operator.
 *)

(** We use typeclasses to give such "canonical names" to these
    operations, allowing us to define common notations and equations
    once and for all. This is the approach described in
    "Type Classes for Mathematics in Type Theory",
    by Bas Spitters and Eelis van der Weegen
    (https://arxiv.org/abs/1102.1323).

    The properties of these operations are given in
    [Basics.CategoryTheory].
 *)

(** Notations [>>>] and [⩯] are in the module [CatNotations], under the scope
    [cat]. The common way to use them is:
[[
  Import CatNotations.
  Local Open Scope cat.
]]
 *)

(** ** Low-level infrastructure *)

(** Categories are parameterized by a type of objects [obj]. *)

Module Import Carrier.

(** A category will be designated by the type of its morphisms (Hom-sets),
    which is indexed by two objects. *)
(* Notation Hom obj := (obj -> obj -> Type) (only parsing). *)

(** Examples found in this library:

    - The category of functions: [obj := Type], [Fun a b := a -> b].
    - The category of indexed functions: [obj := Type -> Type], [IFun E F := E ~> F]
      (where [~>] is defined in [Basics.Basics]).
    - The category of [itree] continuations (one category for every [E : Type -> Type]):
      [obj := Type], [ktree E a b := a -> itree E a b].
    - The category of [itree] handlers: [obj := Type -> Type],
      [Handler E F := E ~> itree F].

    The latter two are Kleisli categories of the former two respectively.
*)

(** Bifunctors from a category to itself are designated by their object maps.
    They are associated to morphism maps via the [Bimap] class. *)
Notation binop obj := (obj -> obj -> obj) (only parsing).

End Carrier.

(** Scope for category notations. *)
Declare Scope cat_scope.
Delimit Scope cat_scope with cat.

(** ** Categories *)

(* [/ᐠ｡‸｡ᐟ\] *)
Section CatOps.

  Context {obj : Type} (C : obj -> obj -> Type).

(** The identity morphism for the object [a : obj] is written [id_ a]. *)
Class Id_ : Type :=
  id_ : forall a: obj, C a a.
(* We add an underscore [id_] to avoid clashing with the standard
   library [id]. *)

(** Given two morphisms [f] and [g] with a common endpoint, their
    composition (or con(cat)enation) is written [cat f g] or [f >>> g]. *)
Class Cat : Type : Type :=
  cat : forall a b c, C a b -> C b c -> C a c.

(** If there is an initial object [i], its initial morphisms are written
    [empty : C i a]. *)
Class Initial (i : obj) :=
  empty : forall a, C i a.

End CatOps.

Arguments id_ {obj C Id_}.
Arguments cat {obj C Cat a b c}.
Arguments empty {obj C i Initial a}.

(** ** Bifunctors *)

Section CocartesianOps.

Context {obj : Type} (C : obj -> obj -> Type) (bif : binop obj).

(** *** Coproducts *)

(** Coproducts are a generalization of sum types and case analysis. *)

(** Case analysis on a sum. *)
Class Case :=
  case_ : forall a b c, C a c -> C b c -> C (bif a b) c.

(** Injection into the left component. *)
Class Inl :=
  inl_ : forall a b, C a (bif a b).

(** Injection into the right component. *)
Class Inr :=
  inr_ : forall a b, C b (bif a b).

(* Like [id_], the underscores avoid confusion with the names
   from the stdlib ([inl] and [inr] are constructors of [sum],
   and [case] is a tactic.) *)

End CocartesianOps.

Arguments case_ {obj C bif Case a b c}.
Arguments inl_ {obj C bif Inl a b}.
Arguments inr_ {obj C bif Inr a b}.

(** ** Core notations *)
Module Import CatNotations.

Infix ">>>" := cat (at level 50, left associativity) : cat_scope.

End CatNotations.

Local Open Scope cat.

(** ** Automatic solver of reassociating sums *)

Section RESUM.

Context {obj : Type} (C : obj -> obj -> Type) (bif : binop obj).
Context `{Id_ _ C} `{Cat _ C}.
Context `{Case _ C bif} `{Inl _ C bif} `{Inr _ C bif}.

Class ReSum (a b : obj) :=
  resum : C a b.

(** The instance weights on [ReSum_inl] (8) and [ReSum_inr] (9) are so that,
    if you have a list [E +' E +' F] (associated to the right:
    [E +' (E +' F)]), then the first one will be picked for the inclusion
    [E -< E +' E +' F]. *)

#[global]
Instance ReSum_id a : ReSum a a := { resum := id_ a }.
#[global]
Instance ReSum_sum a b c
         `{ReSum a c} `{ReSum b c} : ReSum (bif a b) c :=
  { resum := case_ resum resum }.
#[global]
Instance ReSum_inl a b c `{ReSum a b} : ReSum a (bif b c) | 8 :=
  { resum := resum >>> inl_ }.
#[global]
Instance ReSum_inr a b c `{ReSum a b} : ReSum a (bif c b) | 9 :=
  { resum := resum >>> inr_ }.
#[global]
Instance ReSum_empty {i : obj} `{Initial _ _ i} a : ReSum i a :=
  { resum := empty }.

(* Usage template:

[[
Opaque cat.
Opaque id.
Opaque case_.
Opaque inl_.
Opaque inr_.

    (* where the category is (->)  vv *)
Definition f {X Y Z} : complex_sum -> another_complex_sum :=
  Eval compute in resum.

Transparent cat.
Transparent id.
Transparent case_.
Transparent inl_.
Transparent inr_.
]]
*)

End RESUM.

#[global] Hint Mode ReSum ! ! ! ! : typeclass_instances.

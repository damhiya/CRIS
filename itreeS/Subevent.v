(** * Extensible effects *)

(** Notations to handle large sums and classes for extensible effects. *)

(* begin hide *)
From ITreeS Require Import
     CategoryOps
     Basics
     Sum
     ITreeDefinition.

(* end hide *)

(** Automatic application of commutativity and associativity for
    sums types constructed with [sum1].

    N.B. This is prone to infinite instance resolution loops.
    Put the following option at the top of your [.v] files to
    bound the instance search depth:

[[
  Typeclasses eauto := 5.
]]

    Higher numbers allow bigger instances but grow the search
    space exponentially.
 *)


(** The name of the category. *)
Definition IFun (E F : iEvent) : Type := E ~> F.

(** The identity function. *)
#[global] Instance Id_IFun : Id_ IFun := fun E _ e => e.

(** Function composition. *)
#[global] Instance Cat_IFun : Cat IFun :=
  fun E F G f1 f2 R e => f2 _ (f1 _ e).

(** [void1] is the initial object. *)
#[global] Instance Initial_void1 : Initial IFun void1 := @elim_void1.

#[global] Instance Case_sum1 : Case IFun sum1 := @case_sum1.
#[global] Instance Inl_sum1 : Inl IFun sum1 := @inl1.
#[global] Instance Inr_sum1 : Inr IFun sum1 := @inr1.



Notation Subevent E F := (@ReSum _ IFun E F)
  (only parsing).
Notation "E -< F" := (Subevent E F)
  (at level 92, left associativity) : type_scope.

Definition subevent {E F : iEvent} `{E -< F} : E ~> F :=
  resum IFun.

#[global]
Instance Subevent_refl E : @ReSum _ IFun E E.
Proof. repeat red; eauto. Defined.

(** Notations to construct and pattern-match on nested sums. *)
Module Import SumNotations.

Declare Scope sum_scope.
Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inr1 x) : sum_scope.
Notation "( x |)" := (inl1 x) : sum_scope.
Notation "(| x |)" := (inr1 (inl1 x)) : sum_scope.
Notation "(|| x )" := (inr1 (inr1 x)) : sum_scope.
Notation "(|| x |)" := (inr1 (inr1 (inl1 x))) : sum_scope.
Notation "(||| x )" := (inr1 (inr1 (inr1 x))) : sum_scope.
Notation "(||| x |)" := (inr1 (inr1 (inr1 (inl1 x)))) : sum_scope.
Notation "(|||| x )" := (inr1 (inr1 (inr1 (inr1 x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inl1 x))))) : sum_scope.
Notation "(||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x))))))) : sum_scope.

End SumNotations.

Local Open Scope sum_scope.

(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
Notation trigger e := (ITree.trigger (subevent _ e)).

(* Some rewriting lemmas sometimes expose [resum]. The following lemmas help reshape the goal properly *)
Lemma resum_to_subevent : forall (E F : iEvent) H T e,
    @resum _ IFun E F H T e = subevent _ e.
Proof.
  intros; reflexivity.
Qed.

Lemma subevent_subevent' : forall {E F} `{E -< F} {X} (e : E X),
    @subevent F F _ X (@subevent E F _ X e) = subevent X e.
Proof.
  reflexivity.
Qed.

Lemma subevent_subevent : forall {E F G} (SEF: E -< F) (SFG: F -< G) T (e : E T),
    @subevent F G SFG T (@subevent E F SEF T e) =
    @subevent E G (fun x f => SFG _ (SEF _ f)) T e.
Proof.
  reflexivity.
Qed.

#[global] Instance subevent_void1 E: @ReSum _ IFun void1 E :=
  fun T e => match e with end.

Lemma subevent_left {E F: iEvent} {R: Type} (e: E R):
  @subevent E (E +' F) (ReSum_inl _ _ _ _ _) R e = inl1 e.
Proof.
  reflexivity.
Qed.

Lemma subevent_right {E F: iEvent} {R: Type} (e: F R):
  @subevent F (E +' F) (ReSum_inr _ _ _ _ _) R e = inr1 e.
Proof.
  reflexivity.
Qed.

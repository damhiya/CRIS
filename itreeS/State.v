(** * State *)

(** Events to read and update global state. *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITreeS Require Import
     Basics
     CategoryOps
     ITreeDefinition
     Subevent
     Interp
     Sum.

Local Open Scope itree_scope.

Import Monads.

(* end hide *)

(* Stateful handlers [E ~> Monads.stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> Monads.stateT S (itree F)]. *)

Definition interp_state {E: iEvent} {M: Type -> Type} {S: Type} 
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> Monads.stateT S M) :
  itree E ~> Monads.stateT S M
  :=
  interp h.

Arguments interp_state {E M S FM MM IM} h [T].

(* list of ucmras. Exists to avoid universal inconsistency of Iris and list with relations.  *)
From iris.algebra Require Import cmra.

Inductive cmra_list : Type :=
 | nil : cmra_list
 | cons (a : cmra) (l : cmra_list) `{CmraDiscrete a} : cmra_list.

Declare Scope ulist_scope.
Delimit Scope ulist_scope with cmra_list.
Bind Scope ulist_scope with cmra_list.

Infix "::" := cons (at level 60, right associativity) : ulist_scope.

Local Open Scope ulist_scope.

Module UList.
  Definition length : cmra_list → nat :=
    fix length l :=
      match l with
      | nil => O
      | _ :: l' => S (length l')
      end.

  (** Concatenation of two lists *)

  Definition app : cmra_list -> cmra_list -> cmra_list :=
    fix app l m :=
    match l with
    | nil => m
    | a :: l1 => a :: app l1 m
    end.

  Infix "++" := app (right associativity, at level 60) : ulist_scope.

  #[local] Open Scope bool_scope.
  Open Scope ulist_scope.

  (** Standard notations for lists.
  In a special module to avoid conflicts. *)
  Module UListNotations.
    Notation "[ ]" := nil (format "[ ]") : ulist_scope.
    Notation "[ x ]" := (cons x nil) : ulist_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : ulist_scope.
  End UListNotations.

  Import UListNotations.

  Section Elts.
    (*****************************)
    (** ** Nth element of a list *)
    (*****************************)
    Fixpoint nth (n:nat) (l:cmra_list) (default:cmra) {struct l} : cmra :=
      match n, l with
        | O, x :: l' => x
        | O, [] => default
        | S m, [] => default
        | S m, x :: t => nth m t default
      end.

    Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
    Proof.
      intro l; induction l as [|? ? IHl DISC]; intro n; destruct n;
      simpl; intros d H; auto.
      - inversion H.
      - apply IHl. now apply Nat.succ_le_mono.
    Qed.
End Elts. End UList.

Export UList.UListNotations.
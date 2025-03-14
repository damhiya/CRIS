(* list of ucmras. Exists to avoid universal inconsistency of Iris and list with relations.  *)
(* From iris.algebra Require Import cmra.
Require Import iprop sflib.

Declare Scope clist_scope.
Delimit Scope clist_scope with clist.

Module CmraList.
  Definition elem : Type := {R : cmra & option R}.

  Inductive t : Type :=
  | nil : t
  | cons (a : elem) (l : t) `{CmraDiscrete (projT1 a)} : t.
  Bind Scope clist_scope with t.

  Local Open Scope clist_scope.

  Definition length : t → nat :=
    fix length l :=
      match l with
      | nil => O
      | cons _ l' => S (length l')
      end.

  Definition app : t → t → t :=
    fix app l m :=
      match l with
      | nil => m
      | cons a l1 => cons a (app l1 m)
      end.

  Fixpoint In (a : elem) (l : t) : Prop :=
    match l with
    | nil => False
    | cons hd tl => a = hd ∨ In a tl
    end.

  Definition incl (l1 l2 : t) : Prop := ∀ a, In a l1 → In a l2.

  Lemma incl_tl (a : elem) (l1 l2 : t) `{CmraDiscrete (projT1 a)} :
    incl l1 l2 → incl l1 (cons a l2).
  Proof. intros INCL i IN1; ss; right; apply INCL; eauto. Qed.

  Lemma incl_cons (a : elem) (l1 l2 : t) `{CmraDiscrete (projT1 a)} :
    In a l2 → incl l1 l2 → incl (cons a l1) l2.
  Proof. intros IN INCL; intros i [IN1 | IN1]; subst; eauto. Qed.

  Lemma incl_cons_inv (a : elem) (l1 l2 : t) `{CmraDiscrete (projT1 a)} :
    incl (cons a l1) l2 → In a l2 ∧ incl l1 l2.
  Proof. intros INCL; split; [eapply INCL; ss; eauto|intros i IN; eapply INCL; right; eauto]. Qed.

  Definition to_GRA (l : t) : GRA.
  Proof.
    induction l as [|[R hd] tl].
    { refine (GRA_mk 0 _). intros a; inv a. }
    { refine (GRA_mk (1 + GRA_len) _). intros i; inv_fin i.
      { apply (DRA_mk R). }
      { apply IHtl. }
    }
  Defined.

  (* Lemma app_to_GRA (l1 l2 : t) : to_GRA (app l1 l2) = GRAs.app (to_GRA l1) (to_GRA l2).
  Proof.
    induction l1.
    { ss. destruct (to_GRA l2); ss. }
  Admitted.

  Class sub (l : t) (Σ : GRA) := sub_in i : In i l → { j | projT1 i = @GRA_lookup Σ j }.
  Global Instance sub_refl l : sub l (to_GRA l).
  Proof. Admitted.

  Global Instance sub_app_l l l1 l2 : sub l (to_GRA l1) → sub l (to_GRA (app l1 l2)).
  Proof. Admitted.

  Global Instance sub_app_r l l1 l2 : sub l (to_GRA l2) → sub l (to_GRA (app l1 l2)).
  Proof. Admitted. *)

  Fixpoint In_cmra (a : cmra) (l : t) : Prop :=
    match l with
    | nil => False
    | cons hd tl => a = projT1 hd ∨ In_cmra a tl
    end.

  Class InCL (A : cmra) (l : t) := InCL_in : In_cmra A l.
  Global Instance InCL_cons A a l `{CmraDiscrete A} : InCL A (cons (existT A a) l).
  Proof. ss; eauto. Qed.

  Global Instance InCL_tl A B l `{CmraDiscrete (projT1 B)} : InCL A l → InCL A (cons B l).
  Proof. ss; eauto. Qed.

  (* Global Instance InCL_sub_inG a l Σ : InCL a l → sub l Σ → inG a Σ.
  Proof. Admitted. *)
End CmraList.
Global Coercion CmraList.to_GRA : CmraList.t >-> GRA.
Infix "::" := CmraList.cons (at level 60, right associativity) : clist_scope.
Infix "++" := CmraList.app (right associativity, at level 60) : clist_scope.

Module GRAL.
  Inductive t : Type :=
  | nil
  | cons (l : CmraList.t) (tl : t).

  Fixpoint to_GRA (l : t) :=
    match l with
    | nil => GRAs.nil
    | cons l tl => GRAs.app l (to_GRA tl)
    end.

  Fixpoint In (e : CmraList.t) (l : t) :=
    match l with
    | nil => False
    | cons hd tl => e = hd ∨ In e tl
    end.

  Class sub (e : CmraList.t) (l : t) := sub_in : In e l.

  Global Instance sub_cons a l : sub a (cons a l).
  Proof. ss; eauto. Qed.

  Global Instance sub_tl a b l : sub a l → sub a (cons b l).
  Proof. ss; eauto. Qed.

  Global Instance InCL_sub_inG a e l : CmraList.InCL a e → sub e l → inG a (to_GRA l).
  Proof.
    revert a e; induction l.
    { intros ??? []. }
  Admitted.

  Section test.
    Context (a b c : CmraList.t).
    Let l := cons a (cons b (cons c nil)).
    Goal sub c l. apply _. Qed.
  End test.

  Section test.
    Context (a b c d e f g h i : cmra) `{∀ c, CmraDiscrete c}.
    Local Open Scope clist_scope.
    Import SigTNotations.
    Let A := (a; None) :: (b; None) :: (c; None) :: CmraList.nil.
    Let B := (d; None) :: (e; None) :: (f; None) :: CmraList.nil.
    Let C := (e; None) :: (f; None) :: (g; None) :: CmraList.nil.
    Local Instance Σ : GRA := GRAL.to_GRA (GRAL.cons A (GRAL.cons B (GRAL.cons C GRAL.nil))).
    Goal inG g Σ. apply _. Qed.
  End test.

  Section test.
    Context (a b c : cmra) `{∀ c, CmraDiscrete c}.
    Local Open Scope clist_scope.
    Import SigTNotations.
    Let A := (a; None) :: (b; None) :: (c; None) :: CmraList.nil.
    Context `{GRAL.sub A Γ}.
    Goal inG a (to_GRA Γ). apply _. Qed.
  End test.

  Definition init_res (l : t) : GRAUR (to_GRA l).
  Proof.
    induction l as [|hd tl].
    { exact ε. }
    { simpl. admit. }

End GRAL.
(** Standard notations for lists.
In a special module to avoid conflicts. *)
Notation "#[ ]" := CmraList.nil (format "#[ ]") : clist_scope.
Notation "#[ x ; .. ; z ]" := 
  (CmraList.cons x .. (CmraList.cons z CmraList.nil) ..)
    (format "#[ '[' x ;  '/' .. ;  '/' z ']' ]") : clist_scope.

Section test.
  Context `{!CmraDiscrete A, !CmraDiscrete B, !CmraDiscrete C, c : C}.
  Import SigTNotations.
  Local Open Scope clist_scope.
  Local Definition b : CmraList.t := #[(A; None); (B; None); (C; Some c)].
  Goal CmraList.InCL A b. apply _. Qed.

  Local Instance Σ : GRA := CmraList.nil ++ CmraList.nil ++ b.
  Goal inG A Σ. apply _. Qed.
End test.

Require Import own.
Definition to_res (l : CmraList.t) : l.
Proof.
  induction l as [|[R [r|]] tl].
  { exact ε. }
  { refine (own.iRes_singleton base_γ r ⋅ _).
    { Set Printing All. refine (inG_mk R _ 0%fin). } }

Local Open Scope clist_scope.
Global Instance incl_subG (l1 l2 : CmraList.t) : CmraList.incl l1 l2 → subG l1 l2.
Proof.
  induction l1.
  { intros _ i; inv i. }
  { intros [IN INCL]%CmraList.incl_cons_inv. i. destruct a. simpl in i. inv_fin i.
    { hexploit (INCL (existT x o)); first ss; eauto. admit. }
    {  } }
  intros H i; destruct (H i) as [j Hprf].
  eexists. Set Printing All.  rewrite CmraList.to_GRA_len_app. rewrite Hprf. rewrite /CmraList.to_GRA /CmraList.t_rect. Set Printing All. reflexivity. *)


(* Debug #1 *)
(* From iris Require Import excl auth numbers.

Class AGΣ (Σ : GRA) := {
  #[local] A_inG :: inG (exclR unitO) Σ;
}.
Definition AΣ : GRA := #[DRA_mk (exclR unitO) None].
Global Instance subG_AGΣ {Σ : GRA} : subG AΣ Σ → AGΣ Σ.
Proof. solve_inG. Qed.

Section a.
  Context `{!AGΣ Σ}.
  Definition a : inG (exclR unitO) Σ. Proof. apply _. Defined.
End a.

Class BGΣ (Σ : GRA) := {
  #[local] B_inG :: inG (authUR (optionUR (exclR unitO))) Σ;
}.
Definition BΣ : GRA := #[DRA_mk (authUR (optionUR (exclR unitO))) (Some (● (Excl' ())))].
Global Instance subG_BGΣ {Σ : GRA} : subG BΣ Σ → BGΣ Σ.
Proof. solve_inG. Qed.

Section b.
  Context `{!BGΣ Σ}.
  Definition b : inG (authUR (optionUR (exclR unitO))) Σ. Proof. apply _. Defined.
End b.

Class CGΣ (Σ : GRA) := {
  #[local] C_inG :: inG (ZR) Σ;
}.
Definition CΣ : GRA := #[DRA_mk (ZR) (Some 1%Z)].
Global Instance subG_CGΣ {Σ : GRA} : subG CΣ Σ → CGΣ Σ.
Proof. solve_inG. Qed. *)


(* Inductive cmra_list : Type :=
 | nil : cmra_list
 | cons (a : cmra) (l : cmra_list) `{CmraDiscrete a} : cmra_list.

Declare Scope ulist_scope.
Delimit Scope ulist_scope with cmra_list.
Bind Scope ulist_scope with cmra_list.

Infix "::" := cons (at level 60, right associativity) : ulist_scope.

Local Open Scope ulist_scope. *)

(* Module UList.
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

Export UList.UListNotations. *)
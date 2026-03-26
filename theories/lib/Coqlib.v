Require Import String.

Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

Require Export sflib.
From Paco Require Export paco.
Notation "f ∘ g" := (fun x => (f (g x))).
Require Export Basics.

Require Import Relations.
Require Export RelationClasses.
Require Import Wellfounded.
Require Export Classical_Prop.
Require Export Lia.
Require Export Axioms.
Require Import Relation_Operators.
Require Export List.
Require Export ClassicalDescription.
Require Export Program.
Require Export Morphisms.
Require Import Sorting.Permutation.

Set Implicit Arguments.



Global Generalizable All Variables.
(* Global Unset Transparent Obligations. *)
Add Search Blacklist "_obligation_".

(* TODO : if it is mature enough, move it to sflib & remove this file *)

Definition update_fst {A B C : Type} (f : A -> C) (ab : A * B) : C * B := (f (fst ab), (snd ab)).

Definition update_snd {A B C : Type} (f : B -> C) (ab : A * B) : A * C := ((fst ab), f (snd ab)).

Lemma dep_split_right
      (A B : Prop) (PA : A)
      (PB : <<LEFT : A>> -> B):
    <<SPLIT : A /\ B>>.
Proof. split; eauto. Qed.

Lemma dep_split_left
      (A B : Prop)
      (PA : <<RIGHT : B>> -> A)
      (PB : B):
    A /\ B.
Proof. split; eauto. Qed.

Lemma Forall_app A P (l0 l1 : list A)
      (FORALL0 : Forall P l0)
      (FORALL1 : Forall P l1):
    Forall P (l0 ++ l1).
Proof. ginduction l0; i; ss. inv FORALL0. econs; eauto. Qed.

Global Program Instance incl_PreOrder {A} : PreOrder (@incl A).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

(* is_Some & is_None? a bit harder to type *)
Definition is_some {X} (x : option X) : bool :=
  match x with
  | Some _ => true
  | _ => false
  end.

Definition is_none {X} := negb ∘ (@is_some X).

Hint Unfold is_some is_none : core.

Notation top1 := (fun _ => True).
Notation top2 := (fun _ _ => True).
Notation top3 := (fun _ _ _ => True).
Notation top4 := (fun _ _ _ _ => True).
Notation top5 := (fun _ _ _ _ _ => True).
Notation top6 := (fun _ _ _ _ _ _ => True).

Hint Unfold Basics.compose : core.


(* Note : not clos_refl_trans. That is not well-founded.. *)
Lemma well_founded_clos_trans
      index
      (order : index -> index -> Prop)
      (WF : well_founded order):
    <<WF : well_founded (clos_trans index order)>>.
Proof. hnf in WF. hnf. i. eapply Acc_clos_trans. eauto. Qed.

Lemma Forall2_impl
      X Y
      (xs : list X) (ys : list Y)
      (P Q : X -> Y -> Prop)
      (* (IMPL : all3 (P <3= Q)) *)
      (IMPL : (P <2= Q))
      (FORALL : Forall2 P xs ys):
    <<FORALL : Forall2 Q xs ys>>.
Proof. induction FORALL; econs; eauto. Qed.

Inductive Forall3 X Y Z (R : X -> Y -> Z -> Prop) : list X -> list Y -> list Z -> Prop :=
| Forall3_nil : Forall3 R [] [] []
| Forall3_cons
    x y z xs ys zs
    (RSAT : R x y z)
    (TAIL : Forall3 R xs ys zs):
    Forall3 R (x :: xs) (y :: ys) (z :: zs).

Lemma Forall3_impl
      X Y Z
      (xs : list X) (ys : list Y) (zs : list Z)
      (P Q : X -> Y -> Z -> Prop)
      (* (IMPL : all3 (P <3= Q)) *)
      (IMPL : (P <3= Q))
      (FORALL : Forall3 P xs ys zs):
    <<FORALL : Forall3 Q xs ys zs>>.
Proof. induction FORALL; econs; eauto. Qed.


Definition o_map A B (oa : option A) (f : A -> B) : option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end.

Definition o_join A (a : option (option A)) : option A :=
  match a with
  | Some a => a
  | None => None
  end.

Definition o_bind A B (oa : option A) (f : A -> option B) : option B := o_join (o_map oa f).
Hint Unfold o_map o_join o_bind : core.

Definition curry2 A B C (f : A -> B -> C) : (A * B) -> C := fun ab => f (fst ab) (snd ab).

Definition o_bind2 A B C (oab : option (A * B)) (f : A -> B -> option C) : option C :=
o_join (o_map oab (curry2 f)).

(* Notation "o >>= f" := (o_bind o f) (at level 50, no associativity) : option_monad_scope. *)

(* Copied from Errors.v *)

Declare Scope o_monad_scope.

Notation "'do' X <- A ; B" := (o_bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200)
 : o_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (o_bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : o_monad_scope.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Notation "'assertion' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200, only parsing)
  : o_monad_scope.

Open Scope o_monad_scope.

(* Lemma o_bind_ignore
      X Y
      (x : option X) (y : option Y):
    (do _ <- x ; y) = assertion(x) ; y.
Proof. des_ifs. Qed. *)

Hint Unfold flip : core.

Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Local Tactic Notation "u" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Local Tactic Notation "u" := repeat (autounfold with *; cbn).
Local Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in *).

Definition sumbool_to_bool {P Q : Prop} (a : {P} + {Q}) : bool := if a then true else false.

Coercion sumbool_to_bool : sumbool >-> bool.

Ltac is_prop H :=
  let ty := type of H in
  match type of ty with
  | Prop => idtac
  | _ => fail 1
  end.

Ltac clear_until id :=
  on_last_hyp ltac:(fun id' => match id' with
                               | id => idtac
                               | _ => clear id'; clear_until id
                               end).

Definition aof_true : Type := True.
Global Opaque aof_true.

Ltac sp H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match eval hnf in ty with
  | forall (a : ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0 : A, a1 : A, a2 : A, a3 : A, a4 : A, a5 : A |- _] => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
    | [a0 : A, a1 : A, a2 : A, a3 : A, a4 : A |- _] => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
    | [a0 : A, a1 : A, a2 : A, a3 : A |- _] => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
    | [a0 : A, a1 : A, a2 : A |- _] => fail 2 "3 candidates!" a0 "," a1 "," a2
    | [a0 : A, a1 : A |- _] => fail 2 "2 candidates!" a0 "," a1
    | [a0 : A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name : A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

(*
Goal let my_nat := nat in
     let my_f := my_nat -> Prop in
     forall (f : my_f) (g : nat -> Prop) (x : nat) (y : my_nat), False.
  i. sp f. sp g.
Abort.
*)

Lemma map_ext_strong
      X Y (f g : X -> Y) xs
      (EXT : forall x (IN : In x xs), f x = g x):
    map f xs = map g xs.
Proof.
  ginduction xs; ii; ss. exploit EXT; eauto. i; des.
  f_equal; ss. eapply IHxs; eauto.
Qed.

(* copied from : https://robbertkrebbers.nl/research/ch2o/tactics.html *)
Hint Extern 998 (_ = _) => f_equal : f_equal.
Hint Extern 999 => congruence : congruence.
Hint Extern 1000 => lia : lia.

Lemma find_map
      X Y (f : Y -> bool) (x2y : X -> Y) xs:
    find f (map x2y xs) = o_map (find (f ∘ x2y) xs) x2y.
Proof. u. ginduction xs; ii; ss. des_ifs; ss. Qed.

(* copied from promising/lib/Basic.v *)

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.

Lemma Forall2_length
      X Y (P : X -> Y -> Prop) xs ys
      (FORALL2 : Forall2 P xs ys):
    length xs = length ys.
Proof. ginduction FORALL2; ii; ss. lia. Qed.

(*
(* 0 goal *)
Goal forall (mytt : unit) (H : unit -> False), False.
  i. hexpl H.
Qed.

(* 1 goal *)
Goal forall (H : nat -> False), False.
  i. hexpl H.
Abort.

Goal forall (H : nat -> nat -> False), False.
  i. Fail hexpl H.
Abort.

(* name *)
Goal forall (mytt : unit) (HH : unit -> (True -> True /\ True)), False.
  i. hexpl HH ABC. hexpl HH.
Abort.
 *)

Hint Extern 997 => lia : lia.

Ltac rp := first [erewrite f_equal8|
                  erewrite f_equal7|
                  erewrite f_equal6|
                  erewrite f_equal5|
                  erewrite f_equal4|
                  erewrite f_equal3|
                  erewrite f_equal2|
                  erewrite f_equal|
                  fail].

Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Definition range (lo hi : Z) : Z -> Prop := fun x => lo <= x < hi. (* TODO : Use Notation instead *)
Hint Unfold range : core.

Ltac sym := symmetry.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.

Lemma rev_nil
      X (xs : list X)
      (NIL : rev xs = []):
    xs = [].
Proof.
  generalize (f_equal (@length _) NIL). i. ss. destruct xs; ss. rewrite length_app in *. ss. lia.
Qed.

Fixpoint last_opt X (xs : list X) : option X :=
  match xs with
  | [] => None
  | [hd] => Some hd
  | hd :: tl => last_opt tl
  end.

Lemma last_none
      X (xs : list X)
      (NONE : last_opt xs = None):
    xs = [].
Proof. ginduction xs; ii; ss. des_ifs. sp IHxs. ss. Qed.

Lemma last_some
      X (xs : list X) x
      (SOME : last_opt xs = Some x):
    exists hds, xs = hds ++ [x].
Proof.
  ginduction xs; ii; ss. des_ifs.
  { exists nil. ss. }
  exploit IHxs; eauto. i; des. rewrite x2. exists (a :: hds). ss.
Qed.

Fixpoint zip X Y Z (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
  match xs, ys with
  | xhd :: xtl, yhd :: ytl => f xhd yhd :: zip f xtl ytl
  | _, _ => []
  end.

Lemma zip_length
      X Y Z (f : X -> Y -> Z) xs ys:
    length (zip f xs ys) = min (length xs) (length ys).
Proof. ginduction xs; ii; ss. des_ifs. ss. rewrite IHxs. lia. Qed.

Lemma in_zip_iff
      X Y Z (f : X -> Y -> Z) xs ys z:
    (<<ZIP : In z (zip f xs ys)>>)
    <-> (exists x y, <<F : f x y = z>> /\ exists n, <<X : nth_error xs n = Some x>> /\ <<Y : nth_error ys n = Some y>>).
Proof.
  split; ii.
  - ginduction xs; ii; ss. des_ifs. ss. des; ss.
    + esplits; eauto; try instantiate (1 := 0%nat); ss.
    + exploit IHxs; eauto. i; des. esplits; eauto; try instantiate (1:= (1+n)%nat); ss.
  - des. ginduction n; ii; ss.
    { des_ifs. ss. left; ss. }
    des_ifs. ss. exploit (@IHn _ _ _ f); eauto.
Qed.

Global Opaque Z.mul.

Lemma unit_ord_wf : well_founded (bot2 : unit -> unit -> Prop).
Proof. ii. induction a; ii; ss. Qed.

Ltac et:= eauto.

Require Import Program.

Lemma f_equal_h
      X1 X2 Y1 Y2 (f1 : X1 -> Y1) (f2 : X2 -> Y2) x1 x2
      (TYPX : X1 = X2)
      (FUNC : JMeq f1 f2)
      (ARG : JMeq x1 x2)
      (TYPY : Y1 = Y2) : (* Do we need this? *)
    JMeq (f1 x1) (f2 x2).
Proof. subst. eapply JMeq_eq in FUNC. subst. ss. Qed.

Lemma f_equal_hr
      X1 X2 Y (f1 : X1 -> Y) (f2 : X2 -> Y) x1 x2
      (FUNC : JMeq f1 f2)
      (TYP : X1 = X2)
      (ARG : JMeq x1 x2):
    f1 x1 = f2 x2.
Proof. eapply JMeq_eq. eapply f_equal_h; eauto. Qed.

Lemma f_equal_rh
      X Y1 Y2 (f1 : X -> Y1) (f2 : X -> Y2) x
      (FUNC : JMeq f1 f2)
      (TYP : Y1 = Y2):
    JMeq (f1 x) (f2 x).
Proof. eapply f_equal_h; eauto. Qed.

Lemma cons_app
      X xhd (xtl : list X):
    xhd :: xtl = [xhd] ++ xtl.
Proof. ss. Qed.

Lemma list_map_injective A B (f : A -> B)
      (INJECTIVE : forall a0 a1 (EQ : f a0 = f a1), a0 = a1)
      l0 l1
      (LEQ : map f l0 = map f l1):
    l0 = l1.
Proof.
  revert l1 LEQ. induction l0; i; ss; destruct l1; ss. inv LEQ. f_equal; eauto.
Qed.

Lemma Forall_in_map A B al (R : B -> Prop) (f : A -> B)
      (RMAP : forall a (IN : In a al), R (f a)):
    Forall R (map f al).
Proof. induction al; econs; ss; eauto. Qed.

Lemma Forall_map A B la (R : B -> Prop) (f : A -> B)
      (RMAP : forall a, R (f a)):
    Forall R (map f la).
Proof. induction la; econs; ss. Qed.

Lemma f_hequal A (B : A -> Type) (f : forall a, B a)
      a1 a2 (EQ : a1 = a2):
    JMeq (f a1) (f a2).
Proof. destruct EQ. econs. Qed.

Ltac uo := unfold o_bind, o_bind2, o_map, o_join in *.

Lemma some_injective
      X (x0 x1 : X)
      (EQ : Some x0 = Some x1):
    x0 = x1.
Proof. injection EQ. auto. Qed.

Fixpoint list_diff X (dec : (forall x0 x1, {x0 = x1} + {x0 <> x1})) (xs0 xs1 : list X) : list X :=
  match xs0 with
  | [] => []
  | hd :: tl =>
    if in_dec dec hd xs1
    then list_diff dec tl xs1
    else hd :: list_diff dec tl xs1
  end.

Lemma list_diff_spec
      X dec (xs0 xs1 xs2 : list X)
      (DIFF : list_diff dec xs0 xs1 = xs2):
    <<SPEC : forall x0, In x0 xs2 <-> (In x0 xs0 /\ ~ In x0 xs1)>>.
Proof.
  subst. split; i.
  - ginduction xs0; ii; des; ss. des_ifs.
    { exploit IHxs0; et. i; des. esplits; et. }
    ss. des; clarify.
    { tauto. }
    exploit IHxs0; et. i; des. esplits; et.
  - ginduction xs0; ii; des; ss. des; clarify; des_ifs; ss; try tauto; exploit IHxs0; et.
Qed.

Fixpoint last_option X (xs : list X) : option X :=
  match xs with
  | [] => None
  | hd :: nil => Some hd
  | hd :: tl => last_option tl
  end.
Lemma not_ex_all_not
      U (P : U -> Prop)
      (NEX : ~ (exists n : U, P n)):
    <<NALL : forall n : U, ~ P n>>.
Proof. eauto. Qed.

(* Remark : if econs/econsr gives different goal, at least 2 econs is possible *)
Ltac econsr :=
  first
    [ econstructor 30
     |econstructor 29
     |econstructor 28
     |econstructor 27
     |econstructor 26
     |econstructor 25
     |econstructor 24
     |econstructor 23
     |econstructor 22
     |econstructor 21
     |econstructor 20
     |econstructor 19
     |econstructor 18
     |econstructor 17
     |econstructor 16
     |econstructor 15
     |econstructor 14
     |econstructor 13
     |econstructor 12
     |econstructor 11
     |econstructor 10
     |econstructor  9
     |econstructor  8
     |econstructor  7
     |econstructor  6
     |econstructor  5
     |econstructor  4
     |econstructor  3
     |econstructor  2
     |econstructor  1].

Global Program Instance top2_PreOrder X : PreOrder (top2 : X -> X -> Prop).

Lemma app_eq_inv
      A (x0 x1 y0 y1 : list A)
      (EQ : x0 ++ x1 = y0 ++ y1)
      (LEN : (length x0) = (length y0)):
    x0 = y0 /\ x1 = y1.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify. exploit IHx0; eauto. i; des. clarify.
Qed.

Lemma pos_elim_succ : forall p,
    <<ONE : p = 1%positive>> \/
    <<SUCC : exists q, (Pos.succ q) = p>>.
Proof. i. hexploit (Pos.succ_pred_or p); eauto. i; des; ss; eauto. Qed.

Section FLIPS.

Definition flip2 A B C D : (A -> B -> C -> D) -> A -> C -> B -> D. intros; eauto. Defined.
Definition flip3 A B C D E : (A -> B -> C -> D -> E) -> A -> B -> D -> C -> E. intros; eauto. Defined.
Definition flip4 A B C D E F : (A -> B -> C -> D -> E -> F) -> A -> B -> C -> E -> D -> F. intros; eauto. Defined.

Variable A B C D : Type.
Variable f : A -> B -> C -> D.

Let put_dummy_arg_without_filp A DUMMY B : (A -> B) -> (A -> DUMMY -> B) := fun f => (fun a _ => f a).
Let put_dummy_arg1 A DUMMY B : (A -> B) -> (A -> DUMMY -> B) := fun f => (flip (fun _ => f)).
Let put_dummy_arg21 A DUMMY B C : (A -> B -> C) -> (A -> DUMMY -> B -> C) := fun f => (flip (fun _ => f)).
Let put_dummy_arg22 A B DUMMY C : (A -> B -> C) -> (A -> B -> DUMMY -> C) :=
  fun f => (flip2 (flip (fun _ => f))).

End FLIPS.
Hint Unfold flip2 flip3 flip4 : core.

Lemma firstn_S
      (A : Type) (l : list A) n:
      (le (Datatypes.length l) n /\ firstn (n + 1) l = firstn n l)
    \/ (lt n (Datatypes.length l) /\ exists x, firstn (n + 1) l = (firstn n l) ++ [x]).
Proof.
  ginduction l; i; try sfby (left; do 2 rewrite firstn_nil; split; ss; lia). destruct n.
  { right. ss. split; try lia. eauto. }
  specialize (IHl n). ss. des.
  - left. split; try lia. rewrite IHl0. ss.
  - right. split; try lia. rewrite IHl0. eauto.
Qed.

Lemma map_firstn
      (A B : Type) (l : list A) (f : A -> B) n:
    map f (firstn n l) = firstn n (map f l).
Proof.
  ginduction l; ss; i.
  { ss. do 2 rewrite firstn_nil. ss. }
  destruct n; ss. rewrite IHl. ss.
Qed.

Lemma Forall2_apply_Forall2 A B C D (f : A -> C) (g : B -> D)
      (P : A -> B -> Prop) (Q : C -> D -> Prop)
      la lb
      (FORALL : Forall2 P la lb)
      (IMPLY : forall a b (INA : In a la) (INB : In b lb),
          P a b -> Q (f a) (g b)):
    Forall2 Q (map f la) (map g lb).
Proof.
  ginduction la; ss; i; inv FORALL; ss. econs; eauto.
Qed.

Definition mapi_aux A B (f : nat -> A -> B) :=
  let fix rec (cur : nat) (la : list A) {struct la} : list B :=
      match la with
      | [] => []
      | hd :: tl => f cur hd :: rec (S cur) tl
      end
  in rec.

Definition mapi A B (f : nat -> A -> B) (la : list A) : list B :=
  mapi_aux f (0%nat) la.

Lemma in_mapi_aux_iff
      A B (f : nat -> A -> B) la b
  :
    forall m,
      In b (mapi_aux f m la) <->
      (exists idx a, f (m + idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  ginduction la; split; ii; ss; des; firstorder (subst; auto).
  - destruct idx; ss.
  - exists 0%nat. rewrite Nat.add_0_r. esplits; eauto.
  - exploit IHla; eauto. intros [T _]. exploit T; eauto. i; des. esplits; eauto.
    { rp; eauto. f_equal. instantiate (1:= (S idx%nat)). lia. }
    ss.
  - destruct idx; ss; clarify.
    { left. f_equal. lia. }
    right. eapply IHla; eauto. esplits; eauto.
    { rp; eauto. f_equal. lia. }
Qed.

(* NOTE : If you give name << >>, rewrite tactic does not work... *)
(* TODO : FIX IT *)
Lemma in_mapi_iff
      A B (f : nat -> A -> B) la b
  :
    (* (<<IN : In b (mapi f la)>>) <-> *)
    (* (<<NTH : (exists idx a, f idx a = b /\ nth_error la idx = Some a)>>) *)
    In b (mapi f la) <->
    (exists idx a, f (idx) a = b /\ nth_error la idx = Some a)
.
Proof.
  eapply in_mapi_aux_iff.
Qed.

Lemma nth_error_mapi_aux_iff
      A B (f : nat -> A -> B) la b
  :
    forall idx m,
      nth_error (mapi_aux f m la) idx = Some b <->
      (exists a, f (m + idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  ginduction la; split; ii; ss; des; firstorder (subst; auto).
  - destruct idx; ss.
  - destruct idx; ss.
  - destruct idx; ss; clarify.
    + esplits; eauto. f_equal; lia.
    + exploit IHla; eauto. intros [T _]. eapply T in H. des. clarify.
      esplits; eauto. ss. f_equal; lia.
  - destruct idx; ss; clarify.
    { repeat f_equal; lia. }
    exploit IHla; eauto. intros [_ T]. exploit T; eauto. intro Q; des.
    replace (m + S idx)%nat with (S m + idx)%nat by lia.
    rewrite Q. ss.
Qed.

Lemma nth_error_mapi_iff
      A B (f : nat -> A -> B) la b
  :
    forall idx,
      nth_error (mapi f la) idx = Some b <->
      (exists a, f (idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  split; ii; des.
  - eapply nth_error_mapi_aux_iff in H; eauto.
  - eapply nth_error_mapi_aux_iff; eauto.
Qed.

Lemma mapi_aux_length
      A B (f : nat -> A -> B) m la
  :
    <<LEN : length (mapi_aux f m la) = length la>>
.
Proof.
  ginduction la; ii; ss.
  erewrite IHla; eauto.
Qed.

Lemma nth_error_mapi_none_aux_iff
      A B  (f : nat -> A -> B) la idx m
  :
    <<NTH : nth_error (mapi_aux f m la) idx = None>> <->
           <<LEN : (length la <= idx)%nat>>
.
Proof.
  split; i.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss. r. lia.
    + destruct idx; ii; ss. r. exploit IHla; eauto. i; des. lia.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss.
    + destruct idx; ii; ss. { lia. } eapply IHla; eauto. r. lia.
Qed.

Definition option_dec X (dec : forall x0 x1 : X, {x0 = x1} + {x0 <> x1})
           (x0 x1 : option X) : {x0 = x1} + {x0 <> x1}
.
  decide equality.
Defined.

Fixpoint filter_map A B (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | hd :: tl =>
    match (f hd) with
    | Some b => b :: (filter_map f tl)
    | _ => filter_map f tl
    end
  end
.

Lemma in_filter_map_iff
      X Y (f : X -> option Y) xs y
  :
    <<IN : In y (filter_map f xs)>> <-> (exists x, <<F : f x = Some y>> /\ <<IN : In x xs>>)
.
Proof.
  split; ii.
  - ginduction xs; ii; ss. des_ifs; ss; des; clarify; eauto.
    + exploit IHxs; eauto. i; des. eauto.
    + exploit IHxs; eauto. i; des. eauto.
  - des. ginduction xs; ii; ss. des_ifs; ss; des; clarify; eauto.
    exploit (IHxs _ f y x); eauto.
Qed.

Lemma nodup_length
      X (xs : list X) x_dec
  :
    <<LEN : (length (nodup x_dec xs) <= length (xs))%nat>>
.
Proof.
  r.
  ginduction xs; ii; ss. exploit IHxs; et. i; des. des_ifs; ss; try rewrite x0; try lia.
Qed.

Fixpoint snoc X (xs : list X) (x : X) : list X :=
  match xs with
  | [] => [x]
  | hd :: tl => hd :: snoc tl x
  end
.

Lemma elim_snoc
      X (xs : list X)
  :
    <<NIL : xs = []>> \/ exists lt dh, <<SNOC : xs = snoc lt dh>>
.
Proof.
  ginduction xs; ii; ss; et.
  des; clarify; et.
  - right. exists nil, a. ss.
  - right. exists (a :: lt), dh. ss.
Qed.

Lemma rev_snoc
      X (x : X) lt
  :
    <<EQ : rev (snoc lt x) = x :: rev lt>>
.
Proof.
  ginduction lt; ii; ss.
  erewrite IHlt; et.
Qed.

Lemma func_app
      X Y (f : X -> Y)
      x0 x1
      (EQ : x0 = x1)
  :
    <<EQ : f x0 = f x1>>
.
Proof. clarify. Qed.
Arguments func_app [_] [_].

Lemma snoc_length
      X (x : X) lt
  :
    <<LEN : (length (snoc lt x) = length lt + 1)%nat>>
.
Proof.
  ginduction lt; ii; ss. erewrite IHlt; et.
Qed.

Lemma rev_cons
      X (xs : list X) x tl
      (REV : rev xs = x :: tl)
  :
    (<<NTH : nth_error xs (Datatypes.length xs - 1) = Some x>>)
.
Proof.
  ginduction xs; ii; ss.
  { generalize (elim_snoc xs); intro T.
    des; clarify.
    - ss. clarify.
    - rewrite rev_snoc in *; ss. clarify.
      exploit IHxs; et. i; des.
      rewrite snoc_length in *. destruct lt; ss. rewrite Nat.sub_0_r in *; ss.
  }
Qed.

(* TODO : Coqlib? *)
Lemma nodup_app_l A (l0 l1 : list A)
      (ND : NoDup (l0 ++ l1))
  :
    NoDup l0.
Proof.
  induction l0.
  { econs. }
  ss. inv ND. econs; et.
  ii. eapply H1. eapply List.in_or_app. auto.
Qed.

Lemma nodup_app_r A (l0 l1 : list A)
      (ND : NoDup (l0 ++ l1))
  :
    NoDup l1.
Proof.
  induction l0; ss. inv ND. auto.
Qed.

Lemma nodup_comm A (l0 l1 : list A)
      (NODUP : NoDup (l0 ++ l1))
  :
    NoDup (l1 ++ l0).
Proof.
  eapply Permutation_NoDup; [|et].
  eapply Permutation_app_comm.
Qed.

Lemma NoDup_snoc
      X (x : X) xs
      (NIN : ~In x xs)
      (NDUP : NoDup xs)
  :
    <<NDUP : NoDup (xs ++ [x])>>
.
Proof.
  ginduction xs; ii; ss.
  - econs; et.
  - apply not_or_and in NIN. des.
    eapply NoDup_cons_iff in NDUP; des; ss.
    econs; et.
    + rewrite in_app_iff. apply and_not_or. esplits; et.
      * ss. ii; des; clarify.
    + eapply IHxs; et.
Qed.

Lemma NoDup_rev
      X (xs : list X)
      (UNIQ : NoDup xs)
  :
    <<UNIQ : NoDup (rev xs)>>
.
Proof.
  ginduction xs; ii; ss.
  inv UNIQ. eapply IHxs in H2.
  eapply NoDup_snoc; et. rewrite <- in_rev. ss.
Qed.

Lemma NoDup_app_disjoint A (l0 l1 : list A) (NODUP : NoDup (l0 ++ l1))
  :
    forall a (IN0 : List.In a l0) (IN1 : List.In a l1), False.
Proof.
  revert NODUP. induction l0; et. i. ss. des; ss.
  { subst. inv NODUP. eapply H1. eapply in_or_app. auto. }
  { eapply IHl0; et. inv NODUP. ss. }
Qed.

Lemma map_ext
      A B
      (f g : A -> B)
      l
      (EQ : forall a (IN : In a l), <<EQ : f a = g a>>)
  :
    map f l = map g l
.
Proof.
  ginduction l; ii; ss.
  exploit EQ; et. i; des. erewrite IHl; et. congruence.
Qed.

Lemma filter_map_none
      X Y (f : X -> option Y) xs
      (NONE : forall x (IN : In x xs), f x = None)
  :
    <<NIL : filter_map f xs = []>>
.
Proof.
  clear - xs NONE. ginduction xs; ii; ss. exploit IHxs; et. intro T. rewrite T. des_ifs.
  exploit NONE; et. i; clarify.
Qed.

Lemma filter_map_app
      X Y xs0 xs1 (f : X -> option Y)
  :
    <<EQ : (filter_map f (xs0 ++ xs1)) = (filter_map f xs0) ++ (filter_map f xs1)>>
.
Proof.
  ginduction xs0; ii; ss.
  des_ifs. rewrite IHxs0. ss.
Qed.

Lemma filter_map_rev
      X Y xs (f : X -> option Y)
  :
    <<EQ : rev (filter_map f xs) = filter_map f (rev xs)>>
.
Proof.
  ginduction xs; ii; ss. des_ifs.
  - ss. rewrite IHxs; et. rewrite filter_map_app; ss. des_ifs.
  - ss. rewrite IHxs; et. rewrite filter_map_app; ss. des_ifs. rewrite app_nil_r. ss.
Qed.

Lemma nth_error_nth
      X
      (xs : list X) n x
      (NTH : nth_error xs n = Some x)
  :
    forall d, nth n xs d = x
.
Proof.
  ginduction xs; ii; ss; des_ifs; ss; clarify.
  exploit IHxs; eauto.
Qed.

Lemma prop_ext_rev
      A B
      (EQ : A = B)
  :
    A <-> B
.
Proof. clarify. Qed.

Lemma func_ext_rev
      A B
      (a : A)
      (f g : A -> B)
      (EQ : f = g)
  :
    f a = g a
.
Proof.
  clarify.
Qed.

(*** TODO : move to CoqlibC ***)
Lemma NoDup_inj_aux
      X Y (f : X -> Y) xs
      (NODUP : NoDup (map f xs))
      x0 x1
      (NEQ : x0 <> x1)
      (IN0 : In x0 xs)
      (IN1 : In x1 xs)
  :
    f x0 <> f x1
.
Proof.
  ginduction xs; i; ss.
  inv NODUP. des; clarify; et.
  - intro T. rewrite <- T in *. eapply H1. erewrite in_map_iff. eauto.
  - intro T. rewrite T in *. eapply H1. erewrite in_map_iff. eauto.
Qed.

Require Import Classical_Pred_Type.

Lemma not_and_or_strong
      P Q
      (H : (~ (P /\ Q)))
  :
    ((Q /\ ~ P) \/  ~Q)
.
Proof.
  apply not_and_or in H.
  destruct (classic Q); et.
  des; clarify; et.
Qed.

Lemma NNPP_rev
      (P : Prop)
      (p : P)
  :
    ~ ~ P
.
Proof. ii. eauto. Qed.

Ltac Psimpl_ :=
  match goal with
  | [ H : ~ ~ ?P |- _ ] => apply NNPP in H
  | [ H : ~ (NW (fun _ => ~ ?P)) |- _ ] => apply NNPP in H
  | [ |- ~ ~ ?P ] => apply NNPP_rev
  | [ H : (~?P -> ?P) |- _ ] => apply Peirce in H
  | [ H : ~ (?P -> ?Q) |- _ ] => apply imply_to_and in H
  | [ |- ~?P \/ ~?Q ] => apply imply_to_or
  (* Parameter or_to_imply : forall P Q : Prop, ~ P \/ Q -> P -> Q. *)
  | [ H : ~(?P /\ ?Q) |- _ ] => apply not_and_or_strong in H
  | [ |- ~(?P /\ ?Q) ] => apply or_not_and
  | [ H : ~(?P \/ ?Q) |- _ ] => apply not_or_and in H
  | [ |- ~(?P \/ ?Q) ] => apply and_not_or
  | [ H : ~(forall n, ~?P n) |- _ ] => apply not_all_not_ex in H
  | [ H : ~(forall n, ?P) |- _ ] => apply not_all_ex_not in H; destruct H as [n H]
  | [ H : ~(exists n, ?P) |- _ ] => apply Coqlib.not_ex_all_not in H; unfold NW in H
  | [ H : ~(exists n, ~?P n) |- _ ] => apply not_ex_not_all in H
  | [ |- ~(forall n, ?P n) ] => apply ex_not_not_all
  | [ |- ~(exists n, ?P n) ] => apply all_not_not_ex
  end
.

Ltac Psimpl := hrepeat do 1 Psimpl_.

Goal (~ forall (mm : nat), mm = 0%nat) -> exists n, n <> 0%nat.
  ii. Psimpl. exists mm. assumption.
Qed.

Goal (~ exists (mm : nat), mm = 0%nat) -> forall mm, mm <> 0%nat.
  intro H. Psimpl. assumption.
Qed.

Lemma iff_eta
      (P Q : Prop)
      (EQ : P = Q)
  :
    <<EQ : P <-> Q>>
.
Proof. clarify. Qed.

Lemma and_eta
      (P0 P1 Q0 Q1 : Prop)
      (EQ0 : P0 = P1)
      (EQ1 : Q0 = Q1)
  :
    <<EQ : (P0 /\ Q0) = (P1 /\ Q1)>>
.
Proof. clarify. Qed.

Tactic Notation "ii" "as" ident(a) := hrepeat do 1 (let name := fresh a in intro name).

Require Import String.
Module Type SEAL.
  Parameter sealing : string -> forall X : Type, X -> X.
  Parameter sealing_eq : forall key X (x : X), sealing key x = x.
End SEAL.
Module Seal : SEAL.
  Definition sealing (_ : string) X (x : X) := x.
  Lemma sealing_eq key X (x : X) : sealing key x = x.
  Proof. refl. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_default_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => (hrepeat do 1 rewrite (@Seal.sealing_eq x)); try clear x
  | _ => (hrepeat do 1 rewrite (@Seal.sealing_eq _ _ x));
         hrepeat do 1 match goal with
                | [ H : string |- _ ] => clear H
                end
  end
.

Notation "☃ y" := (Seal.sealing _ y) (at level 60, only printing).
Goal forall x, 5 + 5 = x. i. seal 5. seal x. Fail progress cbn. unseal key0. unseal 5. progress cbn. Abort.
Goal forall x y z, x + y = z. i. seal x. seal y. unseal y. unseal key. Abort.
Goal forall x y z, x + y = z. i. seal_with "a" x. seal_with "b" y. unseal "a". unseal "b". Abort.

Notation "f ∘ g" := (fun x => (f (g x))).

Definition map_fst A B C (f : A -> C) : A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f : B -> C) : A * B -> A * C := fun '(a, b) => (a, f b).

Lemma fst_map_snd {A B C} f:
  (fst ∘ @map_snd A B C f) = fst.
Proof.
  extensionalities. destruct H. s. eauto.
Qed.

(* Definition is_zero (v : Z) : bool := (dec v 0%Z)%Z. *)

Notation "(∘)" := (fun g f => g ∘ f) (at level 0, left associativity).

Lemma map_dist {A B C} (f: A -> B) (g: B -> C) (l: list A) :
  map (g ∘ f) l = map g (map f l).
Proof. induction l; simpl; eauto. rewrite IHl. reflexivity. Qed.

Variant option_rel A B (P : A -> B -> Prop) : option A -> option B -> Prop :=
| option_rel_some
    a b (IN : P a b)
  :
    option_rel P (Some a) (Some b)
| option_rel_none
  :
    option_rel P None None
.
Hint Constructors option_rel : core.

Definition map_or_else X Y (ox : option X) (f : X -> Y) (d : Y) :=
  match ox with | Some x => f x | None => d end.

Lemma map_or_else_same : forall X Y (ox : option X) (d : Y), map_or_else ox (fun _ => d) d = d.
  i. destruct ox; ss.
Qed.

Definition or_else X (ox : option X) (d : X) := match ox with | Some x => x | None => d end.

Lemma map_or_else_id : forall X ox (d : X), map_or_else ox id d = or_else ox d. refl. Qed.

Lemma flat_map_map A B C (f : A -> B) (g : B -> list C) (l : list A)
  :
    flat_map g (map f l) = flat_map (g ∘ f) l.
Proof.
  induction l; ss. f_equal; auto.
Qed.

Lemma fold_right_app_flat_map A B (f : A -> list B) l
  :
    flat_map f l
    =
    fold_right (@app _) [] (List.map f l).
Proof.
  induction l; ss. f_equal. auto.
Qed.

Lemma map_flat_map A B C (f : A -> list B) (g : B -> C) (l : list A)
  :
    List.map g (flat_map f l)
    =
    flat_map (List.map g) (List.map f l).
Proof.
  induction l; ss. rewrite List.map_app. f_equal; auto.
Qed.

Lemma flat_map_single A B (f : A -> B) (l : list A)
  :
    flat_map (fun a => [f a]) l
    =
    List.map f l.
Proof.
  induction l; ss.
Qed.

Lemma Forall2_In_l A B R (l0 : list A) (l1 : list B) a
      (FORALL2 : Forall2 R l0 l1)
      (IN : In a l0)
  :
    exists b, In b l1 /\ R a b.
Proof.
  revert IN. induction FORALL2; ss. i. des.
  { subst. et. }
  { eapply IHFORALL2 in IN; et. i. des. esplits; et. }
Qed.

Lemma Forall2_In_r A B R (l0 : list A) (l1 : list B) b
      (FORALL2 : Forall2 R l0 l1)
      (IN : In b l1)
  :
    exists a, In a l0 /\ R a b.
Proof.
  revert IN. induction FORALL2; ss. i. des.
  { subst. et. }
  { eapply IHFORALL2 in IN; et. i. des. esplits; et. }
Qed.

Lemma Forall2_eq
      A
      (xs0 xs1 : list A)
      (EQ : Forall2 eq xs0 xs1)
  :
    <<EQ : xs0 = xs1>>
.
Proof. induction EQ; ss. des; subst. refl. Qed.

Global Open Scope nat_scope.

(* Lemmas about string *)

Lemma string_length_app (s1 s2: string):
  String.length (String.append s1 s2) = String.length s1 + String.length s2.
Proof.
  revert s2. induction s1; i; ss.
  fold append. rewrite IHs1. et.
Qed.
  
Definition strings_maxlen (l: list string) : nat :=
  list_max (List.map String.length l).

Fixpoint string_repeat (s: string) (n: nat) : string :=
  match n with
  | 0 => ""
  | S n' => String.append s (string_repeat s n')
  end.

Lemma string_repeat_length s n:
  String.length (string_repeat s n) = n * String.length s.
Proof.
  induction n; ss.
  rewrite string_length_app. rewrite IHn. et.
Qed.

Lemma strings_maxlen_app l1 l2:
  strings_maxlen (l1++l2) = max (strings_maxlen l1) (strings_maxlen l2).
Proof.
  revert l2. induction l1; et.
  i. s. unfold strings_maxlen in *. ss.
  rewrite IHl1. nia.
Qed.

Lemma strings_maxlen_notin s l
  (LONG: String.length s > strings_maxlen l)
  :
  ~ existsb (String.eqb s) l.
Proof.
  ii. eapply existsb_exists in H. des. eapply String.eqb_eq in H0; subst.
  revert_until l. induction l; i; ss.
  des; subst.
  - unfold strings_maxlen in LONG. ss. nia.
  - eapply IHl; et. unfold strings_maxlen in *. ss. nia.
Qed.

Lemma string_ex_not_in (l: list string):
  exists s, ~ In s l.
Proof.
  exists (string_repeat "H" (1 + strings_maxlen l)).
  ii. eapply strings_maxlen_notin; cycle 1.
  - eapply existsb_exists. esplits; [apply H|apply String.eqb_refl].
  - rewrite string_repeat_length. s. nia.
Qed.

From stdpp Require Import base list.

(* Lemmas about names *)
Definition maxlen (s : list string) : nat :=
  list_max (String.length <$> s).

Fixpoint mname_long (n : nat) : string :=
  match n with
  | 0 => ""
  | S n' => String.append "." (mname_long n')
  end.

Lemma mname_long_length n : String.length (mname_long n) = n.
Proof. induction n; ss. rewrite IHn. et. Qed.

Lemma elem_of_maxlen (fn : string) (s : list string) :
  fn ∈ s → String.length fn ≤ maxlen s.
Proof. i; eapply max_list_elem_of_le, elem_of_list_fmap; esplits; eauto. Qed.

Lemma maxlen_app s1 s2 : maxlen (s1 ++ s2) = maxlen s1 `max` maxlen s2.
Proof. unfold maxlen. rewrite fmap_app, list_max_app. et. Qed.

Lemma list_max_in k ns
  (IN: In k ns)
  :
  k <= list_max ns.
Proof.
  induction ns; ss; des; subst; try nia.
  apply IHns in IN. nia.
Qed.  

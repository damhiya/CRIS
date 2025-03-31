Require Import sflib List.
Import ListNotations.
Require Import Permutation.

Ltac Lauto_normalize :=
  (hrepeat do 1 (match goal with
      [|-context[?x::?l]] =>
        match l with
        | [] => fail 1
        | _ => change (x::l) with ([x]++l)
        end
    end));
  try rewrite <-!app_assoc.

Ltac Lauto_prepare :=
  match goal with
  | [|- ?l = _] =>
      rewrite <-(app_nil_r l);
      change (l ++ []) with ([]++(l ++ []))
  end;
  Lauto_normalize.

Ltac Lauto_find x :=
  hrepeat do 1 match goal with
    | [|- context[?l1 ++ ?l2 ++ [x]]] => pattern (l1 ++ l2 ++ [x]); rewrite (app_assoc l1 l2 _)
    | [|- context[?l1 ++ ?l2 ++ [x] ++ ?l3]] => pattern (l1 ++ l2 ++ [x] ++ l3); rewrite (app_assoc l1 l2 _)
    end.

Ltac Lauto_finish :=
  try rewrite !app_nil_r; Lauto_normalize; simpl List.app.

Section TEST.
  Variable P : list nat -> Prop.
  Variable old new : nat.
  Hypothesis P_change : forall l l', P(l ++ [new] ++ l') -> P(l ++ [old] ++ l').

  Lemma test0 (x1 x2 x3 x4 x5:nat) (l1 l2 l3 l4 : list nat)
    (SAT : P ([x1]++(x2::l1)++([x3;new]++l3)++[x4]++l4++[x5]))
    :
    P ([x1]++(x2::l1)++([x3;old]++l3)++[x4]++l4++[x5]).
  Proof.
    Lauto_normalize; simpl List.app.

    eapply eq_ind; cycle 1.
    { symmetry.
      Lauto_prepare.
      Lauto_find old.
      reflexivity.
    }
    apply P_change.
    Lauto_finish.
    apply SAT.
  Qed.  

End TEST.

(*
Lemma perm_normalize_elmt {T} (x : T) l:
  Permutation (l++[x]) (x::l).
Proof using.
  induction l; eauto.
  simpl. rewrite IHl. eauto using Permutation.
Qed.

Lemma perm_rotate {T} (x : T) l:
  Permutation (x::l) (l ++ [x]).
Proof.
  induction l; eauto.
  simpl. rewrite <-IHl. eauto using Permutation.
Qed.

Ltac perm_to_singleton :=
  hrepeat do 1 match goal with
      [|-context[?x::?l]] =>
        match l with
        | [] => fail 1
        | _ => change (x::l) with ([x]++l)
        end
    end.

Ltac _perm_normalize :=
  perm_to_singleton;
  rewrite !app_assoc;
  rewrite !perm_normalize_elmt.
  
Ltac perm_normalize :=
  do 2 _perm_normalize; simpl.
  
Ltac perm_check_at_head x :=
  match goal with
    [|-context[Permutation (?x' :: _) _]] =>
      match x' with
      | x => idtac
      end
  end.

Ltac perm_rotate :=
  rewrite perm_rotate.

Ltac perm_rotate_rev :=
  perm_to_singleton;
  rewrite !app_assoc, <-perm_rotate.

Lemma _perm_counter_intro : forall n:nat, n = n.
Proof. eauto. Qed.

Lemma _perm_counter_dec : forall n, S n = S n -> n = n.
Proof. eauto. Qed.

Ltac perm_move_start := let counter := fresh "_COUNTER" in
  eassert(counter := _perm_counter_intro _).
  
Ltac perm_move_forward x :=
  first
    [perm_check_at_head x;
     match goal with [H:_|-_] => instantiate (1:= 0) in H end
    |perm_rotate; simpl;
     match goal with [H:_|-_] => instantiate (1:= S _) in H end;
     perm_move_forward x].

Ltac perm_move_back :=
  first
    [match goal with [H:_|-_] => apply _perm_counter_dec in H end;
     perm_rotate_rev;
     perm_move_back
    |simpl].

Ltac perm_move_finish :=
  match goal with [H:_|-_] => clear H end.


Section TEST.
  Variable P : list nat -> Prop.
  Hypothesis P_perm : forall l1 l2, Permutation l2 l1 -> P l1 -> P l2.
  
  Variable old new : nat.
  Hypothesis P_change : forall l, P(new :: l) -> P(old :: l).

  Lemma test (x1 x2 x3 x4 x5:nat) (l1 l2 l3 l4 : list nat)
    (SAT : P ([x1]++(x2::l1)++([x3;new]++l3)++[x4]++l4++[x5]))
    :
    P ([x1]++(x2::l1)++([x3;old]++l3)++[x4]++l4++[x5]).
  Proof.
    eapply P_perm.
    { perm_normalize. reflexivity. }
    
    perm_move_start.
    eapply P_perm.
    { perm_normalize.
      perm_move_forward old.
      reflexivity.
    }
    
    apply P_change.
    
    eapply P_perm.
    { perm_move_back.
      reflexivity.
    }
    perm_move_finish.

    eapply P_perm, SAT.
    { perm_normalize.
      reflexivity.
    }
  Qed.
  
End TEST.
*)

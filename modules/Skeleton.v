Require Import Coqlib.
Require Export ZArith.
Require Import String.
Require Import PCM.
Require Import Events.
Require Export AList.
Require Import IPM.

Set Implicit Arguments.

Local Open Scope nat_scope.

Notation gname := string (only parsing). (*** convention : not capitalized ***)

Require Import Orders.
Require Import Any.

Module Sk.
  (* Class ld : Type := mk { *)
  (*   t:> Type; *)
  (*   unit : t; *)
  (*   add : t -> t -> t; *)
  (*   canon : t -> t; *)
  (*   wf : t -> Prop; *)
  (*   add_comm : forall a b (WF : wf (add a b)), *)
  (*       canon (add a b) = canon (add b a); *)
  (*   add_assoc : forall a b c, add a (add b c) = add (add a b) c; *)
  (*   add_unit_l : forall a, add unit a = a; *)
  (*   add_unit_r : forall a, add a unit = a; *)
  (*   wf_comm : forall a b, wf (add a b) -> wf (add b a); *)
  (*   unit_wf : wf unit; *)
  (*   wf_mon : forall a b, wf (canon (add a b)) -> wf (canon a); *)

  (*   extends := fun a b => exists ctx, canon (add a ctx) = b; *)
  (* } *)
  (* . *)


  (* Imp Instance *)
  (* Inductive gdef : Type := Gfun | Gvar (gv : Z). *)

  (* Module GDef <: Typ. Definition t := gdef. End GDef. *)
  (* Module GDef <: Typ. Definition t := Any.t. End GDef. *)

  (* Module SkSort := AListSort GDef. *)

  (* Definition sort : alist gname gdef -> alist gname gdef := SkSort.sort. *)
  (* Definition sort : alist gname Any.t -> alist gname Any.t := SkSort.sort. *)

  Definition t := alist gname Any.t.

  Definition wf (sk : t) := List.NoDup (List.map fst sk).

  Definition unit : t := [].

  Definition add (sk1 sk2 : t) : t := sk1 ++ sk2.

  Definition equiv (sk1 sk2 : t) : Prop := sk1 ≡ₚ sk2.

  Lemma equiv_wf (sk1 sk2 : t)
    (EQV : equiv sk1 sk2)
    (WF : wf sk1)
    :
    wf sk2.
  Proof.
    eapply Permutation_NoDup, WF. eapply Permutation_map. eauto.
  Qed.

  Lemma equiv_incl (sk1 sk2 : t)
    (EQV : equiv sk1 sk2)
    :
    List.incl sk1 sk2.
  Proof.
    ii. eapply Permutation_in, H. apply EQV.
  Qed.
  
  (* Program Definition gdefs : ld := *)
  (*   @mk (alist gname Any.t) nil (@List.app _) sort (fun sk => @List.NoDup _ (List.map fst sk)) _ _ _ _ _ _ _. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   eapply SkSort.sort_add_comm. auto. *)
  (*   (* eapply Permutation.Permutation_NoDup; [|et]. *) *)
  (*   (* eapply Permutation.Permutation_map. *) *)
  (*   (* symmetry. eapply SkSort.sort_permutation. *) *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   eapply List.app_assoc. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   rewrite List.app_nil_r. auto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   i. eapply Permutation.Permutation_NoDup; [|et]. *)
  (*   eapply Permutation.Permutation_map. *)
  (*   apply Permutation.Permutation_app_comm. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   econs. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   cut (List.NoDup (List.map fst a)). *)
  (*   { i. eapply Permutation.Permutation_NoDup; [|et]. *)
  (*     eapply Permutation.Permutation_map. *)
  (*     eapply SkSort.sort_permutation. } *)
  (*   cut (List.NoDup (List.map fst (a ++ b))). *)
  (*   { i. rewrite map_app in H0. *)
  (*     eapply nodup_app_l. et. } *)
  (*   i. eapply Permutation.Permutation_NoDup; [|et]. *)
  (*   eapply Permutation.Permutation_map. *)
  (*   symmetry. eapply SkSort.sort_permutation. *)
  (* Qed. *)

  (* Local Existing Instance gdefs. *)


  (*** TODO : It might be nice if Sk.t also constitutes a resource algebra ***)
  (*** At the moment, List.app is not assoc/commutative. We need to equip RA with custom equiv. ***)

  (* Definition incl (sk0 sk1 : Sk.t) : Prop := List.incl sk0 sk1. *)
  (*   forall gn gd (IN : List.In (gn, gd) sk0), *)
  (*     List.In (gn, gd) sk1. *)

  (* Program Instance incl_PreOrder : PreOrder incl. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. ss. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. eapply H0. eapply H. ss. *)
  (* Qed. *)

End Sk.

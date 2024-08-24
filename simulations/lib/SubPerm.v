Require Import Coqlib sflib.
Require Import IPM.

Definition sub_perm {A} (l1 l2: list A) : Prop :=
  exists l0, (l0 ++ l1) ≡ₚ l2.

Lemma sub_perm_incl {A} (l1 l2: list A)
  (SP: sub_perm l1 l2)
  :
  incl l1 l2.
Proof.
  r in SP. des.
  ii. eapply Permutation_in; eauto.
  apply in_or_app. eauto.
Qed.

Lemma sub_perm_nodup {A} (l1 l2: list A)
  (SP: sub_perm l1 l2)
  (ND: List.NoDup l2)
  :
  List.NoDup l1.
Proof.
  r in SP. des.
  eapply Permutation_NoDup in ND; cycle 1.
  - symmetry. eauto.
  - eapply nodup_app_r. eauto.
Qed.

Lemma sub_perm_cancel {A} (l0 l1 l1' l2 l2': list A)
  (SP: sub_perm (l1 ++ l2) (l1' ++ l2'))
  :
  sub_perm (l1 ++ l0 ++ l2) (l1' ++ l0 ++ l2').
Proof.
  r in SP. des. exists l3.
  do 2 rewrite Permutation_app_rot.
  rewrite <-!app_assoc. symmetry.
  rewrite Permutation_app_rot.
  apply Permutation_app_head.
  rewrite Permutation_app_comm. symmetry.
  rewrite Permutation_app_rot. eauto.
Qed.

Lemma sub_perm_cancel_head {A} (l0 l l': list A)
  (SP: sub_perm l l')
  :
  sub_perm (l0 ++ l) (l0 ++ l').
Proof.
  apply (sub_perm_cancel l0 [] []). eauto.
Qed.

Lemma sub_perm_cancel_tail {A} (l0 l l': list A)
  (SP: sub_perm l l')
  :
  sub_perm (l ++ l0) (l' ++ l0).
Proof.
  assert (X:=sub_perm_cancel l0 l l' [] []).
  rewrite !app_nil_r in *. eauto.
Qed.

Lemma sub_perm_remove {A} (l0 l1 l2: list A):
  sub_perm (l1 ++ l2) (l1 ++ l0 ++ l2).
Proof.
  exists l0.
  rewrite/__ !List.app_assoc [l0 ++ _]Permutation_app_comm.
  eauto.
Qed.

Lemma sub_perm_remove_head {A} (l0 l: list A):
  sub_perm l (l0 ++ l).
Proof.
  apply (sub_perm_remove l0 []).
Qed.

Lemma sub_perm_remove_tail {A} (l0 l: list A):
  sub_perm l (l ++ l0).
Proof.
  assert (X := sub_perm_remove l0 l []).
  rewrite !app_nil_r in *. eauto.
Qed.

Lemma sub_perm_refl {A} (l: list A):
  sub_perm l l.
Proof.
  apply (sub_perm_remove_head []).
Qed.

Lemma sub_perm_trans {A} (l1 l2 l3: list A):
  sub_perm l1 l2 -> sub_perm l2 l3 -> sub_perm l1 l3.
Proof.
  unfold sub_perm. i; des.
  eexists. rewrite/__ -H0 -H.
  rewrite app_assoc. eauto.
Qed.

Lemma sub_perm_nil {A} (l: list A):
  sub_perm [] l.
Proof.
  apply (sub_perm_remove_tail l []).
Qed.

Program Instance incl_PreOrder {A}: PreOrder (@sub_perm A).
Next Obligation.
  ii. apply sub_perm_refl.
Qed.
Next Obligation.
  ii. eapply sub_perm_trans; eauto.
Qed.

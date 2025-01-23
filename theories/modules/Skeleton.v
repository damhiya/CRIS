Require Import Common.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module Sk.
  Definition t := alist string Any.t.
  Definition wf (sk : t) := List.NoDup (List.map fst sk).
  Definition unit : t := [].
  Definition add (sk1 sk2 : t) : t := sk1 ++ sk2.
  Definition equiv (sk1 sk2 : t) : Prop := sk1 ≡ₚ sk2.

  Lemma equiv_wf (sk1 sk2 : t) (EQV : equiv sk1 sk2) (WF : wf sk1) :
    wf sk2.
  Proof. eapply Permutation_NoDup, WF. eapply Permutation_map. eauto. Qed.

  Lemma equiv_incl (sk1 sk2 : t) (EQV : equiv sk1 sk2) :
    List.incl sk1 sk2.
  Proof. ii. eapply Permutation_in, H. apply EQV. Qed.
End Sk.

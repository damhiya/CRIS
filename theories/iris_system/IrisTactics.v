Require Import Common syn_invariants.
From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.

(* Cmra *)
Ltac simple_rewrite_id :=
  hrepeat do 1 (
    match goal with
    | [H: context[(ε ⋅ ?x)] |- _] => rewrite left_id in H 
    | [|- context[(ε ⋅ ?x)]] => rewrite left_id
    | [H: context[(?x ⋅ ε)] |- _] => rewrite right_id in H 
    | [|- context[(?x ⋅ ε)]] => rewrite right_id
    | [H: context[(None ⋅ ?x)] |- _] => rewrite left_id in H 
    | [|- context[(None ⋅ ?x)]] => rewrite left_id
    | [H: context[ (?x ⋅ None)] |- _] => rewrite right_id in H
    | [|- context[( ?x ⋅ None )]] => rewrite right_id
    end 
  )
.

Ltac substitute_setoid_rewrite :=
  hrepeat do 1 (
    match goal with
    | [H1: context[?x], H2: ?x ≡ ?y |- _] => setoid_rewrite H2 in H1
    | [H: context[?x ≡ ?y] |- context [?x]] => setoid_rewrite H
    end 
  )
.

Ltac pair_des := 
  match goal with
    | [H: context[(?x ⋅ ?y)] |- _] => setoid_rewrite <- pair_op in H
    | [|- context[(?x ⋅ ?y)]] => setoid_rewrite <- pair_op
    | [H: context[✓ (?x , ?y)] |- _] => setoid_rewrite pair_valid in H; destruct H
    | [|- context[✓ (?x , ?y)]] => setoid_rewrite pair_valid; split
    | [H: context[ (?a, ?b) ≼ (?a', ?b') ] |- _] => setoid_rewrite pair_included in H 
    | [|- context[ (?a, ?b) ≼ (?a', ?b') ]] => setoid_rewrite pair_included
    | [H: context[ core (?a, ?b) ] |- _] => setoid_rewrite pair_core in H
    | [|- context[ core (?a, ?b) ]] => setoid_rewrite pair_core
  end
.

Ltac option_des_hypothsis := 
  match goal with
    | [H: context[ (✓ (Some ?a))] |- _] => rewrite Some_valid in H 
    | [|- context[ (✓ (Some ?a))]] => rewrite Some_valid
    | [H: context[ (Some (?a ⋅ ?b)) ] |- _] => rewrite Some_op in H
    | [|- context[ (Some (?a ⋅ ?b)) ]] => rewrite Some_op 
    | [H: context[ (Some (?a ⋅? ?ma))] |- _] => rewrite <- Some_op_opM in H
    | [|- context[ (Some (?a ⋅? ?ma))]] => rewrite <- Some_op_opM
    | [H: context[ (?ma ⋅ ?mb = None)] |- _] => rewrite op_None in H; destruct H 
    | [|- context[ (?ma ⋅ ?mb = None)]] => rewrite op_None; split
  end
.

Ltac some_included :=
  match goal with
  | [H1: context[ (Some (Excl ?a) ≼ Some ?b)], H2: context[(✓ ?b)] |- _] 
    => assert((Excl a) ≡ b) by (apply Some_included_exclusive; ss) 
  | [H: context[ (Some (?a) ≼ Some (?b))] |- _]
    => first [ assert(a ≼ b) by (apply Some_included_total; ss) 
             | apply Some_included]
  end
. 

Ltac option_pair_des := 
  match goal with
  | [H: context[ Some (?a1, ?b1) ≼ Some (?a2, ?b2) ] |- _] => apply Some_pair_included in H; destruct H
  end 
.

Ltac discrete_fun_tac := 
  match goal with
  | [H: context[ (?f ⋅ ?g) ?x] |- _] => rewrite discrete_fun_lookup_op in H
  | [|- context[ (?f ⋅ ?g) ?x]] => rewrite discrete_fun_lookup_op
  | [H: context[ (core ?f) ?x] |- _] => rewrite discrete_fun_lookup_core in H
  | [|- context[ (core ?f) ?x]] => rewrite discrete_fun_lookup_core 
  end 
.

Ltac cmra_tac := ( 
                      try simple_rewrite_id;
                      try substitute_setoid_rewrite;
                      try pair_des;
                      try option_des_hypothsis;
                      try some_included;
                      try option_pair_des;
                      try discrete_fun_tac
                    ); ss
.

(* excl *)
Ltac excl_inv :=
  match goal with 
  | [H: context[Excl ?a ≡ Excl ?b] |- _] => inv H
  end
.

Ltac excl_valid := 
  match goal with
  | [H: context[✓ (Excl' ?a ⋅ ?mx)] |- _] => apply excl_validN_inv_l in H
  | [H: context[✓ (?mx ⋅ Excl' ?a)] |- _] => apply excl_validN_inv_r in H
  end 
.

Ltac excl_included :=
  match goal with
  | [H: context[(Excl' ?a ≼ Excl' ?b)] |- _] => rewrite Excl_included in H
  | [|- context[?ea ≼ ExclInvalid]] => apply ExclInvalid_included
  end 
.

Ltac excl_tac := 
  (
    try excl_inv;
    try excl_valid;
    try excl_included
  )
.

(* auth *)
Ltac auth_des := 
  match goal with 
  | [H: context[◯ (?a ⋅ ?b)] |- _] => rewrite auth_frag_op in H 
  | [|- context[◯ (?a ⋅ ?b)]] => rewrite auth_frag_op
  | [|- context[◯ ?a ≼ ◯ ?b]] => apply auth_frag_mono
  | [H: context[✓ (● ?a)] |- _] => rewrite auth_auth_valid in H 
  | [H: context[✓ (◯ ?b)] |- _] => rewrite auth_frag_valid in H
  | [|- context[✓ (◯ ?b)]] => rewrite auth_frag_valid 
  | [H: context[✓ (◯ ?b1 ⋅ ◯ ?b2)] |- _] => rewrite auth_frag_op_valid in H
  | [|- context[✓ (◯ ?b1 ⋅ ◯ ?b2)]] => rewrite auth_frag_op_valid
  | [H: context[✓ (●{?dq} ?a)] |- _] => rewrite auth_auth_dfrac_valid in H; destruct H
  | [|- context[✓ (●{?dq} ?a)]] => rewrite auth_auth_dfrac_valid; split
  | [H: context[✓ (●{?dq1} ?a1 ⋅ ●{?dq2} ?a2)] |- _] => rewrite auth_auth_dfrac_op_valid in H; destruct H
  | [|- context[✓ (●{?dq1} ?a1 ⋅ ●{?dq2} ?a2)]] => rewrite auth_auth_dfrac_op_valid; split
  | [H: context[✓ (● ?a1 ⋅ ● ?a2) ] |- _] => rewrite auth_auth_op_valid in H; discriminate H
  | [H: context[✓ (●{?dq} ?a ⋅ ◯ ?b)] |- _] => rewrite auth_both_dfrac_valid_discrete in H; destruct H 
  | [|- context[✓ (●{?dq} ?a ⋅ ◯ ?b)]] => rewrite auth_both_dfrac_valid_discrete; split
  | [H: context[✓ (● ?a ⋅ ◯ ?b)] |- _] => rewrite auth_both_valid_discrete in H; destruct H 
  | [|- context[✓ (● ?a ⋅ ◯ ?b)]] => rewrite auth_both_valid_discrete; split
  end 
.

Ltac auth_included :=
  match goal with 
  | [H: context[● ?a1 ≼ ● ?a2 ⋅ ◯ ?b] |- _] => rewrite auth_auth_included in H
  | [|- context[● ?a1 ≼ ● ?a2 ⋅ ◯ ?b]] => rewrite auth_auth_included
  | [H: context[●{?dq1} ?a1 ≼ ●{?dq2} ?a2 ⋅ ◯ ?b] |- _] => rewrite auth_auth_dfrac_included in H; destruct H
  | [|- context[●{?dq1} ?a1 ≼ ●{?dq2} ?a2 ⋅ ◯ ?b]] => rewrite auth_auth_dfrac_included
  | [H: context[●{?dq1} ?a1 ⋅ ◯ ?b1 ≼ ●{?dq2} ?a2 ⋅ ◯ ?b2] |- _] 
    => rewrite auth_both_dfrac_included in H; destruct H 
  | [|- context[●{?dq1} ?a1 ⋅ ◯ ?b1 ≼ ●{?dq2} ?a2 ⋅ ◯ ?b2]]
    => rewrite auth_both_dfrac_included; split
  | [H: context[● ?a1 ⋅ ◯ ?b1 ≼ ● ?a2 ⋅ ◯ ?b2] |- _]
    => rewrite auth_both_included in H; destruct H 
  | [|- context[● ?a1 ⋅ ◯ ?b1 ≼ ● ?a2 ⋅ ◯ ?b2]]
    => rewrite auth_both_included; split
  end
.

Ltac auth_tac := 
  (
    try auth_des;
    try auth_included
  ) 
.

(* frac *)

Ltac frac_des :=
  match goal with 
  | [H: context[✓ ?p] |- _] => rewrite frac_valid in H 
  | [|- context[✓ ?p]] => rewrite frac_valid 
  | [H: context[?p ⋅ ?q] |- _] => rewrite frac_op in H 
  | [|- context[?p ⋅ ?q]] => rewrite frac_op
  | [H: context[?p ≼ ?q] |- _] => rewrite frac_included in H 
  | [|- context[?p ≼ ?q]] => rewrite frac_included  
  end 
.  

Section example_excl.

Context {A : ofe}.
Implicit Types a b : A.
Implicit Types x y : excl A.

Lemma excl_eq a b c :
  (Excl b ≡ Excl c) →
  (Excl a ≡ Excl b) →
  Excl a ≡ Excl c
.
Proof using. ii. excl_tac. cmra_tac. Qed. 


End example_excl.

Section example_auth.

Context {A : ucmra}.
Implicit Types a b : A.
Implicit Types x y : auth A.
Implicit Types q : frac.
Implicit Types dq : dfrac.

Lemma tmp a1 a2: 
✓ (● a1 ⋅ ● a2) -> False .
Proof using.
 ii. auth_tac. ss.  
Qed.

End example_auth.

Ltac iris_tac :=
  repeat (
      ss;
      try cmra_tac;
      try excl_tac;
      try auth_tac;
      try frac_des).

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
  | [|- context[?ea ≼ ExclBot]] => apply ExclBot_included
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
Proof. ii. excl_tac. cmra_tac. Qed. 


End example_excl.

Section example_auth.

Context {A : ucmra}.
Implicit Types a b : A.
Implicit Types x y : auth A.
Implicit Types q : frac.
Implicit Types dq : dfrac.

Lemma tmp a1 a2: 
✓ (● a1 ⋅ ● a2) -> False .
Proof.
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

(* Tactics for discrete_fun_singleton *)

Fixpoint discrete_fun_list `{EqDecision A} {B : A → ucmra} (l: list (sigT B)) :=
  match l with
  | [] => ε%I
  | (existT a b) :: tl => (discrete_fun_singleton a b) ⋅ discrete_fun_list tl
  end.

Fixpoint discrete_fun_not_in `{EqDecision A} {B : A → ucmra} (a: A) (l: list (sigT B)) :=
  match l with
  | [] => True
  | (existT a' _) :: tl => a <> a' ∧ discrete_fun_not_in a tl
  end.

Lemma discrete_fun_singleton_valid `{EqDecision A} (B : A → ucmra) (a1 a2 : A)
  (b1 : B a1) (b2 : B a2) : 
  a1 <> a2 → ✓ b1 → ✓ b2 →
  ✓ (discrete_fun_singleton a1 b1 ⋅ discrete_fun_singleton a2 b2).
Proof. 
  ii; rewrite discrete_fun_lookup_op.
  unfold discrete_fun_singleton, discrete_fun_insert; des_ifs; ss;
    rewrite ?right_id ?left_id //=.
  apply ucmra_unit_valid.
Qed.

Lemma discrete_fun_list_valid `{EqDecision A} (B : A → ucmra) (l: list (sigT B))
  (NODUP: List.NoDup (map projT1 l))
  (VALID: ∀ i r, In (existT i r) l -> ✓ r)
  :
  ✓ (discrete_fun_list l).
Proof.
Admitted.

Ltac dfs_unfold :=
  match goal with
  | [|-✓ ?tm] => rewrite /tm
  end;
  (hrepeat do 1 match goal with
  | [|-context[?tm ⋅ _]] =>
      try match tm with
      | ε => fail 2
      | (_ ⋅ _)%I => fail 2
      | discrete_fun_singleton _ _ => fail 2
      end;
      rewrite /tm
  | [|-context[_ ⋅ ?tm]] =>
      try match tm with
      | ε => fail 2
      | (_ ⋅ _)%I => fail 2
      | discrete_fun_singleton _ _ => fail 2
      end;
      rewrite /tm
  end);
  (hrepeat do 1 match goal with
  | |-context[?r ⋅ ε] => rewrite (right_id _ _ r)
  | |-context[ε ⋅ ?r] => rewrite (left_id _ _ r)
  end).

Ltac dfs_normalize_assoc :=
  (hrepeat do 1 match goal with [|-context[@op (ucmra_car (GRAUR _)) _ ?x (?y ⋅ ?z)]] =>
    rewrite (assoc _ x y z)
  end).

Ltac dfs_normalize_assoc_rev :=
  (hrepeat do 1 match goal with [|-context[@op (ucmra_car (GRAUR _)) _ (?x ⋅ ?y) ?z]] =>
    rewrite -(assoc _ x y z)
  end).

Lemma res_move_up `{Σ: GRA} (r1 r2 r3: Σ):
  r1 ⋅ r2 ⋅ r3 ≡ r1 ⋅ r3 ⋅ r2.
Proof.
  rewrite -assoc (comm _ r2 r3) assoc. eauto.
Qed.

Ltac dfs_merge :=
  (hrepeat do 1 let RES := fresh "RES" in
    dfs_normalize_assoc;
    match goal with [|-context[discrete_fun_singleton ?key _]] =>
      (hrepeat do 1 match goal with [|-context[_ ⋅ discrete_fun_singleton ?key' _ ⋅ discrete_fun_singleton key _]] =>
        try match key' with key => fail 2 end;
        rewrite (res_move_up _ (discrete_fun_singleton key' _) (discrete_fun_singleton key _));
        try rewrite !(discrete_fun_singleton_op key)
      end);
      try rewrite !(discrete_fun_singleton_op key)
    end;
    eset (RES := discrete_fun_singleton _ _);
    dfs_normalize_assoc_rev;
    try match goal with |-✓(?x ⋅ ?y) => rewrite (comm _ x y) end);
  (hrepeat do 1 match goal with [H:= _|-_] => unfold H; clear H end).

Ltac dfs_to_list_instantiate tm :=
  match tm with
  | ε => instantiate (1 := []); instantiate (1:= [])
  | (discrete_fun_singleton ?a ?b) ⋅ ?tm' =>
      instantiate (1 := a :: _); instantiate (2:= existT a b :: _);
      dfs_to_list_instantiate tm'
  end.

Ltac dfs_to_list :=
  let NL := fresh "NL" in
  let X := fresh "TMP" in
  match goal with
  | |-✓ ε => idtac
  | |-✓ ?r => rewrite -(right_id _ _ r)
  end;
  dfs_normalize_assoc_rev;
  match goal with
  | |- ✓ ?tm =>
     epose (X := _ : list {i : _ & allocs.allocsUR (GRA_lookup i)});
     epose (NL := _ : list (fin GRA_len)); revert X NL;
     dfs_to_list_instantiate tm; intros X NL;
     change tm with (discrete_fun_list X); unfold X; clear X; revert NL
  end.
  
Ltac dfs_resolve :=
  let NL := fresh "NL" in
  intros NL;
  eapply discrete_fun_list_valid; [
    match goal with [|-List.NoDup ?tm] => change tm with NL end; unfold NL;
    inv_instances.solve_in_subG_goal;
    rewrite ?/eq_rec_r ?/eq_rec; try rewrite -!eq_rect_eq; s; eauto;
    (hrepeat do 1 econstructor; ii; ss; des; eauto; try depdes H)
  |]; clear NL.

Ltac dfs_split :=
  intros ? ?; let H := fresh "IN" in intros H;
  try contradiction;
  (hrepeat do 1 destruct H as [H | H]; try contradiction; try depdes H).

Ltac dfs_simplify :=
  try rewrite !allocs.allocs_frag_op; try rewrite -!cmra_transport_op;
  try rewrite !allocs.allocs_frag_valid; try rewrite !cmra_transport_valid.

Ltac dfs_solve :=
  dfs_unfold;
  dfs_merge;
  dfs_to_list;
  dfs_resolve;
  dfs_split;
  dfs_simplify.

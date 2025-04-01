Require Export String.
From ExtLib Require Export
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Coqlib.

Set Implicit Arguments.
(* Global Opaque string_dec. *)

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)

Class Dec (A : Type) := dec : forall (a0 a1 : A), { a0 = a1 } + { a0 <> a1 }.

Global Program Instance positive_Dec : Dec positive. Next Obligation. decide equality. Defined.
Global Program Instance string_Dec : Dec String.string. Next Obligation. apply String.string_dec. Defined.
Global Program Instance nat_Dec : Dec nat. Next Obligation. apply Nat.eq_dec. Defined.
Global Program Instance Z_Dec : Dec Z. Next Obligation. apply Z.eq_dec. Defined.
Global Program Instance option_Dec A `{Dec A} : Dec (option A).
Next Obligation.
Proof using.
  i. destruct a0, a1.
  - destruct (H a a0).
    + left. f_equal. apply e.
    + right. ii. inversion H0. et.
  - right. ss.
  - right. ss.
  - left. refl.
Defined.

Definition update K `{Dec K} V (f : K -> V) (k : K) (v : V) : K -> V :=
  fun _k => if dec k _k then v else f _k.

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)


Global Instance function_Map `{Dec K} V : (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end).


Global Instance Dec_RelDec K `{Dec K} : @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K} : RelDec_Correct Dec_RelDec.
Proof using.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.

Fixpoint alist_pop (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : K) (m : alist K V) : option (V * alist K V) :=
  match m with
  | [] => None
  | (k', v) :: ms =>
    if k ?[R] k'
    then Some (v, ms)
    else match @alist_pop K R RD_K V k ms with
         | Some (v', ms') => Some (v', (k', v) :: ms')
         | None => None
         end
  end.

Fixpoint alist_pops (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : list K) (m : alist K V) : alist K V * alist K V :=
  match k with
  | [] => ([], m)
  | khd::ktl =>
    let (l, m0) := alist_pops RD_K ktl m in
    match alist_pop RD_K khd m0 with
    | Some (v, m1) => ((khd, v)::l, m1)
    | None => (l, m0)
    end
  end.

Fixpoint alist_replace (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : K) (v : V) (m : alist K V) : alist K V :=
  match m with
  | [] => []
  | (k', v') :: ms =>
    if k ?[R] k'
    then (k, v) :: ms
    else (k', v') :: alist_replace _ k v ms
  end.

Definition alist_filter K `{Dec K} V (f : K -> bool) (l : alist K V) :=
  List.filter (f ∘ fst) l.

Fixpoint _alist_upd [K] [R : K -> K -> Prop] {RD_K : RelDec R} [V]
  (k : K) (v : V) (l : alist K V) : alist K V
  :=
  match l with
  | [] => []
  | x :: l' =>
      if k ?[ R ] (fst x)
      then (k,v) :: l'
      else x :: _alist_upd k v l'
  end.

Definition alist_upd [K] [R : K -> K -> Prop] {RD_K : RelDec R} [V] :=
  @_alist_upd K R RD_K V.

Arguments alist_replace [K R] {RD_K} [V].
Arguments alist_find [K R] {RD_K} [V].
Arguments alist_add [K R] {RD_K} [V].
Arguments alist_pop [K R] {RD_K} [V].
Arguments alist_pops [K R] {RD_K} [V].
Arguments alist_remove [K R] {RD_K} [V].

Lemma eq_rel_dec_correct T `{DEC : Dec T}
      x0 x1
  :
    x0 ?[eq] x1 = if (DEC x0 x1) then true else false.
Proof using.
  des_ifs.
Qed.

Require Import List Setoid Permutation.

Section ALIST.
  Lemma alist_find_some K `{Dec K} V (k : K) (l : alist K V) (v : V)
        (FIND : alist_find k l = Some v)
  :
    In (k, v) l.
  Proof using.
    revert FIND. induction l; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
  Qed.

  Lemma alist_find_some_iff K `{Dec K} V (k : K) (l : alist K V) (v : V)
        (ND : List.NoDup (List.map fst l))
        (IN : In (k, v) l)
  :
    alist_find k l = Some v.
  Proof using.
    revert ND IN. induction l; ss.
    i. destruct a. ss. inv ND. des.
    { clarify. rewrite eq_rel_dec_correct in *. des_ifs. }
    { rewrite eq_rel_dec_correct in *. des_ifs; et.
      exfalso. eapply (List.in_map fst) in IN. et. }
  Qed.

  Lemma alist_find_none K `{Dec K} V (k : K) (l : alist K V)
        (FIND : alist_find k l = None)
        v
    :
      ~ In (k, v) l.
  Proof using.
    revert FIND. induction l; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
    ii. des; clarify. eapply IHl; et.
  Qed.

  Lemma alist_find_app K `{Dec K} V (k : K) (l0 l1 : alist K V) (v : V)
        (FIND : alist_find k l0 = Some v)
    :
      alist_find k (l0 ++ l1) = Some v.
  Proof using.
    revert FIND. induction l0; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
  Qed.

  Lemma alist_find_map K `{Dec K} V0 V1 (f : V0 -> V1) (k : K) (l : alist K V0)
    :
      alist_find k (List.map (fun '(k, v) => (k, f v)) l) = o_map (alist_find k l) f.
  Proof using.
    induction l; ss. uo. destruct a. rewrite eq_rel_dec_correct in *.
    des_ifs.
  Qed.

  Lemma alist_find_find_some K `{Dec K} V (k : K) (l : alist K V) v
    :
      alist_find k l = Some v <-> find (fun '(k2, _) => rel_dec k k2) l = Some (k, v).
  Proof using.
    induction l; ss. destruct a. rewrite eq_rel_dec_correct in *. des_ifs.
    split; i; clarify.
  Qed.

  Lemma alist_find_find_none K `{Dec K} V (k : K) (l : alist K V)
    :
      alist_find k l = None <-> find (fun '(k2, _) => rel_dec k k2) l = None.
  Proof using.
    induction l; ss. destruct a. rewrite eq_rel_dec_correct in *. des_ifs.
  Qed.

  Lemma alist_add_find_eq K `{Dec K} V (k : K) (l : alist K V) (v : V)
    :
      alist_find k (alist_add k v l) = Some v.
  Proof using.
    ss. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_remove_find_eq K `{Dec K} V (k : K) (l : alist K V)
    :
      alist_find k (alist_remove k l) = None.
  Proof using.
    induction l; ss. rewrite eq_rel_dec_correct. des_ifs.
    ss. destruct a. ss. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_remove_find_neq K `{Dec K} V (k0 k1 : K) (l : alist K V)
        (NEQ : k0 <> k1)
    :
      alist_find k0 (alist_remove k1 l) = alist_find k0 l.
  Proof using.
    induction l; ss.
    destruct a. ss. rewrite ! eq_rel_dec_correct. des_ifs.
    { ss. rewrite eq_rel_dec_correct. des_ifs. }
    { ss. rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma alist_add_find_neq K `{Dec K} V (k0 k1 : K) (l : alist K V) (v : V)
        (NEQ : k0 <> k1)
    :
      alist_find k0 (alist_add k1 v l) = alist_find k0 l.
  Proof using.
    ss. rewrite eq_rel_dec_correct. des_ifs.
    eapply alist_remove_find_neq; auto.
  Qed.

  Lemma alist_find_filter K `{Dec K} V (l : alist K V) (k : K) (v : V) (f : K -> bool)
        (FIND : alist_find k (alist_filter f l) = Some v)
        (ND : List.NoDup (List.map fst l))
    :
      alist_find k l = Some v.
  Proof using.
    revert FIND ND. induction l; ss. i.
    destruct a. erewrite eq_rel_dec_correct. ss. inv ND. des_ifs.
    - ss. rewrite eq_rel_dec_correct in *. des_ifs.
    - exfalso. hexploit IHl; et. i. eapply H2.
      eapply alist_find_some in H0. eapply (in_map fst) in H0. ss.
    - ss. rewrite eq_rel_dec_correct in *. des_ifs.
      eapply IHl; et.
    - eapply IHl; et.
  Qed.

  Lemma alist_add_nodup K `{Dec K} V (l : alist K V) k v
        (ND : List.NoDup (List.map fst l))
    :
      List.NoDup (List.map fst (alist_add k v l)).
  Proof using.
    revert ND. induction l; ss.
    { i. econs; et. }
    i. inv ND. sp IHl. destruct a. ss.
    rewrite eq_rel_dec_correct in *. des_ifs.
    inv IHl. ss. econs; et.
    { ii. ss. des; clarify. }
    { econs; et. ii. eapply H2.
      eapply in_map_iff in H0. eapply in_map_iff.
      des. subst. esplits; et.
      unfold alist_remove in H1.
      eapply filter_In in H1. des; auto. }
  Qed.

  Lemma alist_remove_filter K `{Dec K} V (l : alist K V) k f
    :
      alist_filter f (alist_remove k l) =
      alist_remove k (alist_filter f l).
  Proof using.
    induction l; ss. destruct a. ss.
    rewrite eq_rel_dec_correct. des_ifs; ss.
    { rewrite Heq0. rewrite eq_rel_dec_correct. des_ifs. f_equal; et. }
    { rewrite Heq0. et. }
    { rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma alist_add_filter K `{Dec K} V (l : alist K V) k v f
        (IN : f k = true)
    :
      alist_filter f (alist_add k v l) =
      alist_add k v (alist_filter f l).
  Proof using.
    unfold alist_add in *. ss. des_ifs.
    f_equal. eapply alist_remove_filter.
  Qed.

  Lemma alist_add_other_filter K `{Dec K} V f (l : alist K V) k v
        (NIN : f k = false)
    :
      alist_filter f (alist_add k v l) =
      alist_filter f l.
  Proof using.
    induction l; ss.
    { i. rewrite NIN. ss. }
    { i. destruct a. ss. rewrite NIN in *.
      rewrite eq_rel_dec_correct. des_ifs; ss.
      { rewrite Heq0. f_equal. auto. }
      { rewrite Heq0. auto. }
    }
  Qed.

  Lemma alist_permutation_find K `{Dec K} V (l0 l1 : alist K V)
        (ND : List.NoDup (List.map fst l0))
        (PERM : Permutation l0 l1)
        k
    :
      alist_find k l0 = alist_find k l1.
  Proof using.
    revert ND k. induction PERM; ss.
    { i. inv ND. destruct x. rewrite eq_rel_dec_correct. des_ifs. et. }
    { i. inv ND. inv H3. destruct x, y. rewrite eq_rel_dec_correct. des_ifs.
      rewrite eq_rel_dec_correct in *. des_ifs. f_equal. exfalso. eapply H2. ss. auto. }
    { i. rewrite IHPERM1; auto. rewrite IHPERM2; auto.
      eapply Permutation_NoDup; [|apply ND].
      eapply Permutation_map. auto.
    }
  Qed.

  Lemma alist_find_app_o K `{Dec K} V k (l0 l1 : alist K V)
    :
      alist_find k (l0 ++ l1) =
      match (alist_find k l0) with
      | Some v => Some v
      | _ => alist_find k l1
      end.
  Proof using.
    induction l0; ss. destruct a. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_find_map_snd K R `{RD_K : @RelDec K R} A B (f : A -> B) (l : alist K A) k
    :
      alist_find k (map (map_snd f) l)
      =
      o_map (alist_find k l) f.
  Proof using.
    induction l; ss. destruct a. ss. uo. des_ifs.
  Qed.
End ALIST.

Arguments alist_upd [K R] {RD_K} [V] : simpl never.

Tactic Notation "asimpl" "in" ident(H) :=
  (try unfold alist_remove, alist_add in H); simpl in H.

Tactic Notation "asimpl" "in" "*" :=
  (try unfold alist_remove, alist_add in *); simpl in *.

Tactic Notation "asimpl" :=
  (try unfold alist_remove, alist_add); simpl.

Notation "f ∘ g" := (fun x => (f (g x))). (*** It is already in Coqlib but Coq seems to have a bug; it gets overriden by the one in program_scope in the files that import this file ***)

Section ALIST.

  Lemma alist_find_fst_some:
    forall [K : Type] {H : Dec K} [V : Type] (k : K) (l : alist K V) [v : V],
    alist_find k l = Some v -> In k (List.map fst l).
  Proof using.
    i. apply alist_find_some in H0. eapply (in_map fst) in H0. eauto.
  Qed.

  Lemma alist_find_fst_none:
    forall [K : Type] {H : Dec K} [V : Type] (k : K) (l : alist K V),
    alist_find k l = None -> ~ In k (List.map fst l).
  Proof using.
    ii. apply (in_map_iff fst) in H1. des; subst. destruct x. ss.
    eapply alist_find_none in H0. apply H0. eauto.
  Qed.

  Lemma alist_find_fst_notin:
    forall [K : Type] {H : Dec K} [V : Type] (k : K) (l : alist K V),
    ~ In k (List.map fst l) -> alist_find k l = None.
  Proof using.
    ii. destruct (alist_find k l) eqn : EQ; eauto.
    apply alist_find_fst_some in EQ. ss.
  Qed.

  Lemma alist_find_fst_in:
    forall [K : Type] {H : Dec K} [V : Type] (k : K) (l : alist K V),
    In k (List.map fst l) -> exists v, alist_find k l = Some v.
  Proof using.
    ii. destruct (alist_find k l) eqn : EQ; eauto.
    apply alist_find_fst_none in EQ. ss.
  Qed.

  Lemma nodup_eqlen_in_rev
    X (l1 l2 : list X)
    (LEN : List.length l1 = List.length l2)
    (NODUP : List.NoDup l1)
    (MEM : forall x (IN : In x l1), In x l2)
    :
    forall x (IN : In x l2), In x l1.
  Proof using.
    revert_until l1. induction l1; i.
    { destruct l2; ss. }

    apply NoDup_cons_iff in NODUP.
    hexploit (MEM a); s; eauto.
    i. apply in_split in H. des; subst.
    eapply in_elt_inv in IN. des; subst; eauto.
    eapply IHl1 in IN; eauto.
    { rewrite length_app in *. ss. nia. }
    i. hexploit (MEM x0); s; eauto.
    i. apply in_elt_inv in H. des; subst; eauto. ss.
  Qed.

  Lemma in_eqlen_nodup_rev
    X (l1 l2 : list X)
    (LEN : List.length l1 = List.length l2)
    (NODUP : List.NoDup l1)    
    (MEM : forall x (IN : In x l1), In x l2)
    :
    NoDup l2.
  Proof using.
    revert_until l1. induction l1; i.
    { destruct l2; ss. }

    apply NoDup_cons_iff in NODUP.
    hexploit (MEM a); s; eauto.
    i. apply in_split in H. des; subst.
    assert (MEM' : forall x, In x l1 -> In x (l0 ++ l3)).
    { i. hexploit (MEM x); ss; eauto.
      i. apply in_elt_inv in H0. des; subst; eauto. ss.
    }
    clear MEM.
    
    hexploit (IHl1 (l0++l3)); eauto.
    { rewrite length_app in *. ss. nia. }
    i. eapply Permutation.Permutation_NoDup.
    { apply Permutation.Permutation_middle. }
    eapply NoDup_cons_iff; split; eauto.
    ii. apply NODUP.
    eapply nodup_eqlen_in_rev, H0; eauto.
    rewrite length_app in *. ss. nia.
  Qed.

  Lemma alist_add_incl {K V} `{DEC : Dec K} (k : K) (v:V) db:
    incl (List.map fst db) (List.map fst (alist_add k v db)).
  Proof using.
    induction db; ss.
    destruct a. ss.
    ii. unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec.
    destruct H; subst.
    { des_ifs; ss; eauto. }
    apply IHdb in H.
    des_ifs; ss; eauto.
    destruct H; eauto.
  Qed.

  Lemma alist_find_with_nodup {K} `{Dec K} {V} (l1 l2 : alist K V) (k : K) (v : V)
    (NODUP : List.NoDup (List.map fst (l1 ++ [(k,v)] ++ l2)))
    :
    alist_find k (l1 ++ [(k,v)] ++ l2) = Some v.
  Proof using.
    induction l1; ss.
    { rewrite eq_rel_dec_correct. des_ifs. }
    destruct a. rewrite eq_rel_dec_correct. inv NODUP. des_ifs; s.
    { exfalso. apply H2. rewrite map_app; s. apply in_or_app. s; eauto. }
    rewrite IHl1; eauto.
  Qed.
  
  Lemma alist_upd_in_or {K V} `{DEC : Dec K} k (v : V) l kv
    (IN : In kv (alist_upd k v l))
    :
    kv = (k, v) \/ In kv l.
  Proof using.
    unfold alist_upd in *.
    revert kv IN. induction l; ss; i; des; eauto.
    rewrite eq_rel_dec_correct in IN.
    des_ifs; ss; des; eauto.
    apply IHl in IN. des; eauto.
  Qed.
        
  Lemma alist_upd_nodup {K V} `{DEC : Dec K} k v (l : alist K V)
    (ND : List.NoDup (List.map fst l))
    :
    List.NoDup (List.map fst (alist_upd k v l)).
  Proof using.
    unfold alist_upd in *.
    revert ND. induction l; ss; i; eauto using NoDup.
    i. inv ND. sp IHl. destruct a.
    rewrite eq_rel_dec_correct in *.
    des_ifs; ss; eauto using NoDup.
    econs; eauto.
    ii. apply in_map_iff in H. des. subst.
    apply alist_upd_in_or in H0.
    des; subst; eauto.
    apply H1. eapply in_map. eauto.
  Qed.
  
  Lemma List_filter_none {A} (f : A -> bool) (l : list A)
    (NOTIN : forall a, In a l -> f a = true):
    List.filter f l = l.
  Proof using.
    induction l; eauto.
    s. des_ifs; cycle 1.
    { rewrite NOTIN in Heq; ss. eauto. }
    f_equal. eapply IHl. i. eapply NOTIN. s. eauto.
  Qed.
  
  Lemma alist_upd_with_nodup {K} `{Dec K} {V} (l1 l2 : alist K V) (k : K) (v v' : V)
    (NODUP : List.NoDup (List.map fst (l1 ++ [(k,v)] ++ l2)))
    :
    alist_upd k v' (l1 ++ [(k,v)] ++ l2) = l1 ++ [(k,v')] ++ l2.
  Proof using.
    unfold alist_upd in *.
    induction l1; ss.
    { rewrite eq_rel_dec_correct. des_ifs. }
    rewrite eq_rel_dec_correct. inv NODUP. des_ifs; s.
    { exfalso. apply H2. rewrite map_app; s. apply in_or_app. s; eauto. }
    rewrite IHl1; eauto.
  Qed.

  Lemma alist_upd_head {K} `{Dec K} {V} (l1 l2 : alist K V) (k : K) (v : V)
    (NODUP : In k (List.map fst l1))
    :
    alist_upd k v (l1 ++ l2) = alist_upd k v l1 ++ l2.
  Proof using.
    unfold alist_upd.
    induction l1; ss.
    destruct a. ss. rewrite eq_rel_dec_correct. des_ifs; s.
    rewrite IHl1; eauto.
    des; eauto. exfalso. eauto.
  Qed.
  
  Lemma alist_upd_tail {K} `{Dec K} {V} (l1 l2 : alist K V) (k : K) (v : V)
    (NODUP : ~ In k (List.map fst l1))
    :
    alist_upd k v (l1 ++ l2) = l1 ++ alist_upd k v l2.
  Proof using.
    unfold alist_upd.
    induction l1; eauto.
    destruct a. s. rewrite eq_rel_dec_correct. des_ifs; s.
    - exfalso. apply NODUP. s. eauto.
    - rewrite IHl1; eauto.
      ii. apply NODUP. s. eauto.
  Qed.
  
  Lemma alist_upd_keys {K} `{Dec K} {V} (k : K) (v : V) (l : alist K V):
    List.map fst (alist_upd k v l) = List.map fst l.
  Proof using.
    i. induction l; ss.
    unfold alist_upd, _alist_upd. des_ifs.
    { rewrite eq_rel_dec_correct in Heq. des_ifs. }
    s. f_equal. eauto.
  Qed.

  Lemma alist_upd_not_tail {K} `{Dec K} {V} (l1 l2 : alist K V) (k : K) (v : V)
    (NODUP : ~ In k (List.map fst l2))
    :
    alist_upd k v (l1 ++ l2) = alist_upd k v l1 ++ l2.
  Proof using.
    unfold alist_upd.
    induction l1; ss; cycle 1.
    {
      destruct a. ss. rewrite eq_rel_dec_correct. des_ifs; s.
      rewrite IHl1; eauto.
    }
    induction l2; ss.
    destruct a. ss. rewrite eq_rel_dec_correct. des_ifs; s.
    { exfalso. eapply not_or_and in NODUP. des. ss. }
    rewrite IHl2; eauto.
  Qed.

  Lemma alist_upd_not_in {K V} `{Dec K} (k : K) (v : V) l
        (NOTIN : ~ In k (map fst l))
      :
        alist_upd k v l = l.
  Proof using.
    induction l; ss. eapply not_or_and in NOTIN. des.
    unfold alist_upd. ss. des_ifs.
    { rewrite eq_rel_dec_correct in Heq. des_ifs. }
    f_equal. eauto.
  Qed.
  
End ALIST.

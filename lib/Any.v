Require Import Coqlib.

Set Implicit Arguments.

Module Type ANY.

  Parameter t: Type.
  Parameter upcast: forall {T: Type}, T -> t.
  Parameter downcast: forall {T: Type}, t -> option T.

  Parameter upcast_downcast: forall T (v: T), downcast (upcast v) = Some v.
  Parameter downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Parameter upcast_inj: forall A B (a: A) (b: B) (EQ: upcast a = upcast b),
      <<EQ: A = B>> /\ <<EQ: a ~= b>>.

  Parameter upf: forall {T: Type}, (T -> t) -> t.
  Parameter downf: forall {T: Type}, t -> option (T -> t).
  Parameter upf_downf: forall T (f: T -> t), downf (upf f) = Some f.
  Parameter downf_upf: forall T a (f: T -> t), downf a = Some f -> a = upf f.

  Parameter pair: t -> t -> t.
  Parameter split: t -> option (t * t).
  Parameter pair_split: forall (a0 a1: t), split (pair a0 a1) = Some (a0, a1).
  Parameter split_pair: forall (a a0 a1: t), split a = Some (a0, a1) -> <<PAIR: a = pair a0 a1>>.

  Parameter upcast_split: forall T (v: T), split (upcast v) = None.
  Parameter pair_downcast: forall a0 a1 T, @downcast T (pair a0 a1) = None.

End ANY.

Module Any: ANY.

  Record box := box_intro { ty: Type; val: ty }.

  Inductive _t: Type :=
  | _upcast (b: box)
  | _upfun {T: Type} (f: T -> _t)
  .

  Definition t := _t.

  Definition upcast {T} val := _upcast (@box_intro T val).
  
  Definition upf {T} := @_upfun T.

  Definition pair a0 a1 :=
    upf (fun b => match b with true => a0 | false => a1 end).

  Definition _downcast {T: Type} (b: box): option T :=
    match (excluded_middle_informative (b.(ty) = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X) y0) with
            | eq_refl => b.(val)
            end)
    | right _ => None
    end.

  Definition downcast {T: Type} (a: t): option T :=
    match a with
    | _upcast b => _downcast b
    | _ => None
    end.

  Definition _downf {T: Type} T' (f: T' -> t) : option (T -> t) :=
    match (excluded_middle_informative (T' = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X -> t) y0) with
            | eq_refl => f
            end)
    | right _ => None
    end.

  Definition downf {T: Type} (a: t) : option (T -> t) :=
    match a with
    | _upfun f => _downf f
    | _ => None
    end.

  Definition split (a: t): option (t * t) :=
    option_map (fun f => (f true, f false)) (@downf bool a).
    
  Lemma upcast_downcast
        T (a: T)
    :
      downcast (upcast a) = Some a
  .
  Proof.
    ss. unfold _downcast. ss.
    replace (excluded_middle_informative (T = T))
      with (@left _ (T <> T) (@eq_refl _ T)); ss.
    destruct (excluded_middle_informative (T = T)); ss.
    f_equal. eapply proof_irrelevance.
  Qed.

  Lemma downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Proof.
    i. unfold upcast, downcast, _downcast in *. des_ifs. destruct b. ss.
  Qed.

  Lemma upcast_inj
        A B (a: A) (b: B)
        (EQ: upcast a = upcast b)
    :
      <<EQ: A = B>> /\ <<EQ: a ~= b>>
  .
  Proof. unfold upcast in *. simpl_depind. ss. Qed.

  Lemma upf_downf: forall T (f: T -> t), downf (upf f) = Some f.
  Proof.
    ss. unfold _downf. i.
    replace (excluded_middle_informative (T = T))
      with (@left _ (T <> T) (@eq_refl _ T)); ss.
    destruct (excluded_middle_informative (T = T)); ss.
    rewrite (UIP _ _ _ e eq_refl). ss.
  Qed.
    
  Lemma downf_upf: forall T a (f: T -> t), downf a = Some f -> a = upf f.
  Proof.
    i. destruct a; ss. unfold _downf in *. des_ifs.
  Qed.

  Lemma pair_split (a0 a1: t)
    :
      split (pair a0 a1) = Some (a0, a1).
  Proof. unfold pair, split. rewrite upf_downf. eauto. Qed.

  Lemma split_pair (a a0 a1: t) (SPLIT: split a = Some (a0, a1))
    :
      <<PAIR: a = pair a0 a1>>.
  Proof.
    unfold pair, split, option_map in *.
    eapply downf_upf. des_ifs.
    f_equal. extensionalities. des_ifs.
  Qed.

  Lemma upcast_split T (v: T)
    :
      split (upcast v) = None.
  Proof. ss. Qed.

  Lemma pair_downcast a0 a1 T
    :
      @downcast T (pair a0 a1) = None.
  Proof. ss. Qed.

  Lemma pair_inj: forall a b c d, pair a b = pair c d -> <<EQ: a = c /\ b = d>>.
  Proof.
    i. destruct (split (pair a b)) eqn:T.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
  Qed.
  
End Any.

Module Type SANY.

  Parameter t: Type.
  Parameter upcast: forall {T: Type}, T -> t.
  Parameter downcast: forall {T: Type}, t -> option T.

  Parameter upcast_downcast: forall T (v: T), downcast (upcast v) = Some v.
  Parameter downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Parameter upcast_inj: forall A B (a: A) (b: B) (EQ: upcast a = upcast b),
      <<EQ: A = B>> /\ <<EQ: a ~= b>>.

  Parameter upf: forall {T: Type}, (T -> t) -> t.
  Parameter downf: forall {T: Type}, t -> option (T -> t).
  Parameter upf_downf: forall T (f: T -> t), downf (upf f) = Some f.
  Parameter downf_upf: forall T a (f: T -> t), downf a = Some f -> a = upf f.

  Parameter pair: t -> t -> t.
  Parameter split: t -> option (t * t).
  Parameter pair_split: forall (a0 a1: t), split (pair a0 a1) = Some (a0, a1).
  Parameter split_pair: forall (a a0 a1: t), split a = Some (a0, a1) -> <<PAIR: a = pair a0 a1>>.

  Parameter upcast_split: forall T (v: T), split (upcast v) = None.
  Parameter pair_downcast: forall a0 a1 T, @downcast T (pair a0 a1) = None.

End SANY.

Module SAny : SANY.

  Record box := box_intro { ty: Type; val: ty }.

  Inductive _t: Type :=
  | _upcast (b: box)
  | _upfun {T: Type} (f: T -> _t)
  .

  Definition t := _t.
  
  Definition upcast {T} val := _upcast (@box_intro T val).

  Definition upf {T} := @_upfun T.

  Definition pair a0 a1 :=
    upf (fun b => match b with true => a0 | false => a1 end).

  Definition _downcast {T: Type} (b: box): option T :=
    match (excluded_middle_informative (b.(ty) = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X) y0) with
            | eq_refl => b.(val)
            end)
    | right _ => None
    end.

  Definition downcast {T: Type} (a: t): option T :=
    match a with
    | _upcast b => _downcast b
    | _ => None
    end.

  Definition _downf {T: Type} T' (f: T' -> t) : option (T -> t) :=
    match (excluded_middle_informative (T' = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X -> t) y0) with
            | eq_refl => f
            end)
    | right _ => None
    end.

  Definition downf {T: Type} (a: t) : option (T -> t) :=
    match a with
    | _upfun f => _downf f
    | _ => None
    end.

  Definition split (a: t): option (t * t) :=
    option_map (fun f => (f true, f false)) (@downf bool a).
    
  Lemma upcast_downcast
        T (a: T)
    :
      downcast (upcast a) = Some a
  .
  Proof.
    ss. unfold _downcast. ss.
    replace (excluded_middle_informative (T = T))
      with (@left _ (T <> T) (@eq_refl _ T)); ss.
    destruct (excluded_middle_informative (T = T)); ss.
    f_equal. eapply proof_irrelevance.
  Qed.

  Lemma downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Proof.
    i. unfold upcast, downcast, _downcast in *. des_ifs. destruct b. ss.
  Qed.

  Lemma upcast_inj
        A B (a: A) (b: B)
        (EQ: upcast a = upcast b)
    :
      <<EQ: A = B>> /\ <<EQ: a ~= b>>
  .
  Proof. unfold upcast in *. simpl_depind. ss. Qed.

  Lemma upf_downf: forall T (f: T -> t), downf (upf f) = Some f.
  Proof.
    ss. unfold _downf. i.
    replace (excluded_middle_informative (T = T))
      with (@left _ (T <> T) (@eq_refl _ T)); ss.
    destruct (excluded_middle_informative (T = T)); ss.
    rewrite (UIP _ _ _ e eq_refl). ss.
  Qed.
    
  Lemma downf_upf: forall T a (f: T -> t), downf a = Some f -> a = upf f.
  Proof.
    i. destruct a; ss. unfold _downf in *. des_ifs.
  Qed.

  Lemma pair_split (a0 a1: t)
    :
      split (pair a0 a1) = Some (a0, a1).
  Proof. unfold pair, split. rewrite upf_downf. eauto. Qed.

  Lemma split_pair (a a0 a1: t) (SPLIT: split a = Some (a0, a1))
    :
      <<PAIR: a = pair a0 a1>>.
  Proof.
    unfold pair, split, option_map in *.
    eapply downf_upf. des_ifs.
    f_equal. extensionalities. des_ifs.
  Qed.

  Lemma upcast_split T (v: T)
    :
      split (upcast v) = None.
  Proof. ss. Qed.

  Lemma pair_downcast a0 a1 T
    :
      @downcast T (pair a0 a1) = None.
  Proof. ss. Qed.

  Lemma pair_inj: forall a b c d, pair a b = pair c d -> <<EQ: a = c /\ b = d>>.
  Proof.
    i. destruct (split (pair a b)) eqn:T.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
  Qed.
  
End SAny.

Notation "a ↑" := (Any.upcast a) (at level 9).
Notation "a ↓" := (Any.downcast a) (at level 9).

Notation "a ↑↑" := (SAny.upcast a) (at level 9).
Notation "a ↓↓" := (SAny.downcast a) (at level 9).

Goal (tt↑↓) = Some tt. rewrite Any.upcast_downcast. ss. Qed.
Check (Any.pair tt↑ tt↑).
Goal (tt ↑↑ ↓↓) = Some tt. rewrite SAny.upcast_downcast. ss. Qed.
Check (SAny.pair tt↑↑ tt↑↑).
Check (tt ↑↑ ↑ : Any.t).

(* SAT for Separation logic (bi) *)
Require Export sflib.
From stdpp Require Import gmap.
From iris.bi Require Import notation bi.
Require Export SAT.

(* Note that the types in a group has the type SAT.t *)
(* The types in all groups *)
Section sl_red_base.
  Context {PROP : bi}.
  Context `{@GATIntp.t PROP α}.

  (* Reduce SL formula into [PROP]. *)
  Class SLRed n (f : GTerm.t n) (P : PROP) :=
    sl_red : ⟦ f ⟧ ⊣⊢@{PROP} P.
  Global Arguments sl_red {_} f%_SAT P%_I.

  (* High-cost fallback trivial instance. *)
  Global Instance sl_red_base n f :
    SLRed n f ⟦ f ⟧ | 200.
  Proof. rewrite /SLRed. reflexivity. Qed.

  (* Increase weight so that this is not tried first. *)
  Global Instance lift_red n p P :
    SLRed n p P →
    SLRed (S n) (⤉ p) P | 2.
  Proof. intros. rewrite /SLRed SATRed.lift sl_red. reflexivity. Qed.

  Lemma lift_red_base n p :
    ⟦ ⤉ p, S n ⟧ ⊣⊢ ⟦ p ⟧.
  Proof. apply: sl_red. Qed.
End sl_red_base.

(* Hint to progress on a match search *)
Global Hint Extern 100 (SLRed _ (match ?x with _ => _ end) _) =>
  destruct x : typeclass_instances.
Global Hint Extern 100 (SLRed _ _ (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Ltac solve_base_sl_red :=
  intros; rewrite /SLRed ?SATRed.cur /= ?sl_red //=.

(* Note that the types in a group has the type SAT.t *)
(* The types in all groups *)
Module TypG.
  Class t: Type := __TYP : GAT.t.
End TypG.

(** Types for Separation Logic **)
Module ST. Section ST.
  Inductive type : Type :=
  | baseT (t : Type) : type
  | sPropT : type
  | funT : type → type → type
  | prodT : type → type → type
  | sumT : type → type → type
  | listT : type → type
  | gmapT : type → type (* TODO: From Rocq 9.0.0, can use generic keytype. *)
  | metaT : type
  .

  Fixpoint interp (ty : type) (sProp : Type) : Type :=
    match ty with
    | baseT b => b
    | sPropT => sProp
    | funT ty1 ty2 => (interp ty1 sProp → interp ty2 sProp)
    | prodT ty1 ty2 => prod (interp ty1 sProp) (interp ty2 sProp)
    | sumT ty1 ty2 => sum (interp ty1 sProp) (interp ty2 sProp)
    | listT ty1 => list (interp ty1 sProp)
    | gmapT ty1 => gmap positive (interp ty1 sProp)
    | metaT => Type
    end.

  Global Instance t : SAT.t := {
      ops := type;
      arity := interp;
    }.
End ST. End ST.

Module STτ.
  Class t (τ : TypG.t) := { #[global] inG :: @GAT.inG ST.t τ }.
End STτ.

(** Notations and Coercions. *)
Coercion ST.baseT : Sortclass >-> ST.type.

(* Notation scope *)
Local Open Scope SAT_scope.

(* TODO: level too high? *)
Notation "⇣ T" := (ST.baseT T) (at level 90) : SAT_scope.
Notation "'Φ'" := (ST.sPropT) : SAT_scope.
Infix "->" := (ST.funT) : SAT_scope.
Infix "*" := (ST.prodT) : SAT_scope.
Infix "+" := (ST.sumT) : SAT_scope.

(* TODO: Does this really need to be SAT_scope? annoying as lot of explicit scoping is needed. *)
Notation "'τ{' t ',' n '}'" := (@SAT.arity ST.t t (GTerm.t_prev n)) : SAT_scope.
Notation "'τ{' t '}'" := (@SAT.arity ST.t t (GTerm.t_prev _)) : SAT_scope.

(* Separation Logic *)

Module SPropBi.
  Section syntax.
    Context {τ : TypG.t}.

    Variant ops : Type :=
    | _emp
    | _pure (P : Prop)
    | _and
    | _or
    | _impl
    | _forall i (ty : (τ i).(SAT.ops))
    | _exist i (ty : (τ i).(SAT.ops))
    | _sep
    | _wand
    | _persistently
    .

    Definition arity (s : ops) (Prev : Type) : Type :=
      match s with
      | _emp => fin 0
      | _pure P => fin 0
      | _and => fin 2
      | _or => fin 2
      | _impl => fin 2
      | _forall i ty => (τ i).(SAT.arity) ty Prev
      | _exist i ty => (τ i).(SAT.arity) ty Prev
      | _sep => fin 2
      | _wand => fin 2
      | _persistently => fin 1
      end.

    Global Instance syntax : SAT.t := {
        ops := ops;
        arity := arity;
    }.
  End syntax.

  Section semantics.
    Context {τ : TypG.t} {α : GAT.t} (PROP : bi).

    Local Open Scope bi_scope.

    Definition interp_aux n (s : ops) :
      (arity s (GTerm.t_prev n) → GTerm.t n) →
      (arity s (GTerm.t_prev n) → PROP) →
      PROP :=
      match s with
      | _emp => λ _ _, emp
      | _pure P => λ _ _, ⌜ P ⌝
      | _and => λ _ sem, sem 0%fin ∧ sem 1%fin
      | _or => λ _ sem, sem 0%fin ∨ sem 1%fin
      | _impl => λ _ sem, sem 0%fin → sem 1%fin
      | _forall i ty => λ _ sem, bi_forall sem
      | _exist i ty => λ _ sem, bi_exist sem
      | _sep => λ _ sem, sem 0%fin ∗ sem 1%fin
      | _wand => λ _ sem, sem 0%fin -∗ sem 1%fin
      | _persistently => λ _ sem, <pers> sem 0%fin
      end.

    Global Instance interp : @SATIntp.t PROP α syntax := interp_aux.
  End semantics.

  Class G (PROP : bi) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t) := {
    #[local] G_inG_syntax :: GAT.inG syntax α;
    #[local] G_inG_interp :: GATIntp.inG syntax α (interp PROP) β;
  }.
  (* TODO: Good hint mode... *)
  (* Global Hint Mode G - - - + : typeclass_instances. *)

  Section definitions.
    Context `{!G PROP α β τ}.

    Definition syn_emp {n} : GTerm.t n.
    Proof.
      refine ⟨ _emp, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition syn_pure {n} (P : Prop) : GTerm.t n.
    Proof.
      refine ⟨ _pure P, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition syn_and {n} (p1 p2 : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _and, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition syn_or {n} (p1 p2 : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _or, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition syn_impl {n} (p1 p2 : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _impl, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition syn_forall `{IN: @GAT.inG T τ} {n} (ty: T.(SAT.ops)) (p: T.(SAT.arity) ty (GTerm.t_prev n) → GTerm.t n)
        : GTerm.t n.
    Proof.
      destruct IN. subst.
      exact ⟨ _forall _ ty, p ⟩%SAT.
    Defined.

    Definition syn_exist `{IN: @GAT.inG T τ} {n} (ty: T.(SAT.ops)) (p: T.(SAT.arity) ty (GTerm.t_prev n) → GTerm.t n)
        : GTerm.t n.
    Proof.
      destruct IN. subst.
      exact ⟨ _exist _ ty, p ⟩%SAT.
    Defined.

    Definition syn_sep {n} (p1 p2 : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _sep, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition syn_wand {n} (p1 p2 : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _wand, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition syn_persistently {n} (p : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _persistently, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.

  End definitions.

  Module Import notations.
    Notation "'emp'" := (syn_emp) : SAT_scope.
    Notation "'⌜' P '⌝'" := (syn_pure P%type%stdpp) : SAT_scope.
    Infix "∧" := (syn_and) : SAT_scope.
    Notation "(∧)" := (syn_and) (only parsing) : SAT_scope.
    Infix "∨" := (syn_or) : SAT_scope.
    Notation "(∨)" := (syn_or) (only parsing) : SAT_scope.
    Infix "→" := (syn_impl) : SAT_scope.
    Notation "(→)" := (syn_impl) (only parsing) : SAT_scope.
    Notation f_forall A := (syn_forall A).
    Notation "∀'" := (f_forall _) (only parsing) : SAT_scope.
    Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%SAT)) ..)) : SAT_scope.
    Notation f_exist A := (syn_exist A).
    Notation "∃'" := (f_exist _) (only parsing) : SAT_scope.
    Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%SAT)) ..)) : SAT_scope.
    Infix "∗" := (syn_sep) : SAT_scope.
    Notation "(∗)" := (syn_sep) (only parsing) : SAT_scope.
    Infix "-∗" := (syn_wand) : SAT_scope.
    Notation "'<pers>' P" := (syn_persistently P) : SAT_scope.
  End notations.

  Section derived.
    Context `{!G PROP α β τ}.

    Definition syn_affinely {n} (p : GTerm.t n) : GTerm.t n :=
      emp ∧ p.

    Fixpoint syn_big_sepL {n A} (f : nat → A → GTerm.t n) (xs : list A) : GTerm.t n :=
      match xs with
      | [] => emp
      | x :: xs => f 0 x ∗ syn_big_sepL (λ n, f (S n)) xs
      end.

    Definition syn_big_sepM {n K} `{Countable K} {A} (f : K → A → GTerm.t n)
      (m : gmap K A) : GTerm.t n := syn_big_sepL (λ _, uncurry f) (map_to_list m).

    Definition syn_big_sepS {n A} `{Countable A} (f : A → GTerm.t n)
      (X : gset A) : GTerm.t n := syn_big_sepL (λ _, f) (elements X).

    Definition syn_big_sepMS {n A} `{Countable A} (f : A → GTerm.t n)
      (X : gmultiset A) : GTerm.t n := syn_big_sepL (λ _, f) (elements X).

    Fixpoint syn_big_sepL2 {n A B} (f : nat → A → B → GTerm.t n) (l1 : list A) (l2 : list B)
      : GTerm.t n :=
      match l1, l2 with
      | [], [] => emp
      | x1 :: l1, x2 :: l2 => (f 0 x1 x2) ∗ (syn_big_sepL2 (λ m, f (S m)) l1 l2)
      | _, _ => ⌜False⌝
      end.
  End derived.

  Module Import notations_derived.
    Notation "'<affine>' P" := (syn_affinely P) : SAT_scope.
    Notation "□ P" := (<affine> <pers> P) : SAT_scope.

    Notation "'[∗' 'list]' k ↦ x ∈ l , P" :=
      (syn_big_sepL (λ k x, P)%SAT l) : SAT_scope.
    Notation "'[∗' 'list]' x ∈ l , P" :=
      (syn_big_sepL (λ _ x, P)%SAT l) : SAT_scope.

    Notation "'[∗' 'map]' k ↦ x ∈ m , P" :=
      (syn_big_sepM (λ k x, P)%SAT m) : SAT_scope.
    Notation "'[∗' 'map]' x ∈ m , P" :=
      (syn_big_sepM (λ _ x, P)%SAT m) : SAT_scope.

    Notation "'[∗' 'set]' x ∈ X , P" :=
      (syn_big_sepS (λ x, P)%SAT X) : SAT_scope.

    Notation "'[∗' 'mset]' x ∈ X , P" :=
      (syn_big_sepMS (λ x, P)%SAT X) : SAT_scope.

    Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P" :=
      (syn_big_sepL2 (λ k x1 x2, P)%SAT l1 l2) : SAT_scope.
    Notation "'[∗' 'list]' x1 ; x2 ∈ l1 ; l2 , P" :=
      (syn_big_sepL2 (λ _ x1 x2, P)%SAT l1 l2) : SAT_scope.
  End notations_derived.

  Section reduction.
    Context `{!G PROP α β τ}.

    Global Instance empty_red n :
      SLRed n emp emp.
    Proof. solve_base_sl_red. Qed.

    Global Instance pure_red n P :
      SLRed n ⌜P⌝ ⌜P⌝.
    Proof. solve_base_sl_red. Qed.

    Global Instance and_red n p q P Q :
      SLRed n p P → SLRed n q Q →
      SLRed n (p ∧ q) (P ∧ Q).
    Proof. solve_base_sl_red. Qed.

    Global Instance or_red n p q P Q :
      SLRed n p P → SLRed n q Q →
      SLRed n (p ∨ q) (P ∨ Q).
    Proof. solve_base_sl_red. Qed.

    Global Instance impl_red n p q P Q :
      SLRed n p P → SLRed n q Q →
      SLRed n (p → q) (P → Q).
    Proof. solve_base_sl_red. Qed.

    Global Instance forall_red `{IN: @GAT.inG T τ} n ty
      (p : SAT.arity ty _ → _) (f : SAT.arity ty _ → _) :
      (∀ z, SLRed n (p z) (f z)) →
      SLRed n (∀ z, p z) (∀ z, f z) | 3.
    Proof.
      rewrite /SLRed. intros Hpf. destruct IN. subst.
      solve_base_sl_red.
      by setoid_rewrite <-Hpf.
    Qed.

    Global Instance exist_red `{IN: @GAT.inG T τ} n ty
      (p : SAT.arity ty _ → _) (f : SAT.arity ty _ → _) :
      (∀ z, SLRed n (p z) (f z)) →
      SLRed n (∃ z, p z) (∃ z, f z) | 3.
    Proof.
      rewrite /SLRed. intros Hpf. destruct IN. subst.
      solve_base_sl_red.
      by setoid_rewrite <-Hpf.
    Qed.

    (* Reduction specialized for ST types, as above instances can't be auto-inferenced well. *)
    Section STRed.
      Context `{!GAT.inG ST.t τ}.
      Global Instance forall_red_ST n {A : ST.type} (p : τ{A} → _) (f : τ{A} → _) :
        (∀ z, SLRed n (p z) (f z)) →
        SLRed n (∀ z, p z) (∀ z, f z) | 2.
      Proof. apply _. Qed.

      Global Instance exist_red_ST n {A : ST.type} (p : τ{A} → _) (f : τ{A} → _) :
        (∀ z, SLRed n (p z) (f z)) →
        SLRed n (∃ z, p z) (∃ z, f z) | 2.
      Proof. apply _. Qed.
    End STRed.

    Global Instance sep_red n p q P Q:
      SLRed n p P → SLRed n q Q →
      SLRed n (p ∗ q) (P ∗ Q).
    Proof. solve_base_sl_red. Qed.

    Global Instance wand_red n p q P Q:
      SLRed n p P → SLRed n q Q →
      SLRed n (p -∗ q) (P -∗ Q).
    Proof. solve_base_sl_red. Qed.

    Global Instance persistently_red n p P :
      SLRed n p P →
      SLRed n (<pers> p) (<pers> P).
    Proof. solve_base_sl_red. Qed.

    (* Derived forms. *)
    Global Instance affinely_red n p P :
      SLRed n p P →
      SLRed n (<affine> p) (<affine> P).
    Proof. solve_base_sl_red. Qed.

    Global Instance intuitionistically_red n p P :
      SLRed n p P →
      SLRed n (□ p) (□ P).
    Proof. solve_base_sl_red. Qed.

    Global Instance sepL_red n A (l : list A) f P :
      (∀ k x, SLRed n (f k x) (P k x)) →
      SLRed n ([∗ list] k↦x ∈ l, f k x) ([∗ list] k↦x ∈ l, P k x).
    Proof. revert f P. induction l; solve_base_sl_red. Qed.

    Global Instance sepM_red n `{Countable K} A (m : gmap K A) f P :
      (∀ k x, SLRed n (f k x) (P k x)) →
      SLRed n ([∗ map] k↦x ∈ m, f k x) ([∗ map] k↦x ∈ m, P k x).
    Proof. rewrite big_op.big_opM_unseal /big_op.big_opM_def. apply _. Qed.

    Global Instance sepS_red n `{Countable K} (X : gset K) f P :
      (∀ x, SLRed n (f x) (P x)) →
      SLRed n ([∗ set] x ∈ X, f x) ([∗ set] x ∈ X, P x).
    Proof. rewrite big_op.big_opS_unseal /big_op.big_opS_def. apply _. Qed.

    Global Instance sepMS_red n `{Countable K} (X : gmultiset K) f P :
      (∀ x, SLRed n (f x) (P x)) →
      SLRed n ([∗ mset] x ∈ X, f x) ([∗ mset] x ∈ X, P x).
    Proof. rewrite big_op.big_opMS_unseal /big_op.big_opMS_def. apply _. Qed.

    Global Instance sepL2_red {n A B} f P (l1 : list A) (l2 : list B) :
      (∀ k a b, SLRed n (f k a b) (P k a b)) →
      SLRed n ([∗ list] k ↦ x1 ; x2 ∈ l1 ; l2 , f k x1 x2) ([∗ list] k ↦ x1 ; x2 ∈ l1 ; l2 , P k x1 x2).
    Proof. revert l2 f P. induction l1; intros []; solve_base_sl_red. Qed.

    Lemma and_red_base n p q :
      ⟦p ∧ q, n⟧ ⊣⊢ ⟦ p ⟧ ∧ ⟦ q ⟧.
    Proof. apply: sl_red. Qed.

    Lemma or_red_base n p q :
      ⟦p ∨ q,n⟧ ⊣⊢ ⟦ p ⟧ ∨ ⟦ q ⟧.
    Proof. apply: sl_red. Qed.

    Lemma impl_red_base n p q :
      ⟦p → q,n⟧ ⊣⊢ (⟦ p ⟧ → ⟦ q ⟧).
    Proof. apply: sl_red. Qed.

    Lemma forall_red_base `{IN: @GAT.inG T τ} n ty (p : SAT.arity ty _ → _) :
      ⟦∀ z, p z,n⟧ ⊣⊢ ∀ x, ⟦ p x ⟧.
    Proof. apply: sl_red. Qed.

    Lemma exist_red_base `{IN: @GAT.inG T τ} n ty (p : SAT.arity ty _ → _) :
      ⟦∃ z, p z,n⟧ ⊣⊢ ∃ x, ⟦ p x ⟧.
    Proof. apply: sl_red. Qed.

    Lemma sep_red_base n p q :
      ⟦p ∗ q,n⟧ ⊣⊢ ⟦ p ⟧ ∗ ⟦ q ⟧.
    Proof. apply: sl_red. Qed.

    Lemma wand_red_base n p q :
      ⟦p -∗ q,n⟧ ⊣⊢ (⟦ p ⟧ -∗ ⟦ q ⟧).
    Proof. apply: sl_red. Qed.

    Lemma persistently_red_base n p :
      ⟦<pers> p,n⟧ ⊣⊢ (<pers> ⟦ p ⟧).
    Proof. apply: sl_red. Qed.

    Lemma affinely_red_base n p :
      ⟦<affine> p,n⟧ ⊣⊢ (<affine> ⟦ p ⟧).
    Proof. apply: sl_red. Qed.

    Lemma intuitionistically_red_base n p :
      ⟦□ p,n⟧ ⊣⊢ □ ⟦ p ⟧.
    Proof. apply: sl_red. Qed.

    Lemma sepL_red_base n A (l : list A) f :
      ⟦ [∗ list] k↦x ∈ l, f k x, n ⟧ ⊣⊢ [∗ list] k↦x ∈ l, ⟦ f k x ⟧.
    Proof. apply: sl_red. Qed.

    Lemma sepM_red_base n `{Countable K} A (m : gmap K A) f :
      ⟦ [∗ map] k↦x ∈ m, f k x,n ⟧ ⊣⊢ [∗ map] k↦x ∈ m, ⟦ f k x ⟧.
    Proof. apply: sl_red. Qed.

    Lemma sepS_red_base n `{Countable K} (X : gset K) f :
      ⟦ [∗ set] x ∈ X, f x,n ⟧ ⊣⊢ [∗ set] x ∈ X, ⟦ f x ⟧.
    Proof. apply: sl_red. Qed.

    Lemma sepMS_red_base n `{Countable K} (X : gmultiset K) f :
      ⟦[∗ mset] x ∈ X, f x,n ⟧ ⊣⊢ [∗ mset] x ∈ X, ⟦ f x ⟧.
    Proof. apply: sl_red. Qed.

  End reduction.

  Global Opaque syn_emp.
  Global Opaque syn_pure.
  Global Opaque syn_and.
  Global Opaque syn_or.
  Global Opaque syn_impl.
  Global Opaque syn_forall.
  Global Opaque syn_exist.
  Global Opaque syn_sep.
  Global Opaque syn_wand.
  Global Opaque syn_persistently.

  Global Opaque syn_affinely.
  Global Opaque syn_big_sepL.
  Global Opaque syn_big_sepM.
  Global Opaque syn_big_sepS.
  Global Opaque syn_big_sepMS.

End SPropBi.
Export SPropBi.notations SPropBi.notations_derived.

Module SPropBiPlainly.
  Section syntax.

    Variant ops :=
    | _plainly
    .

    Definition arity (s : ops) (Prev : Type) : Type :=
      match s with
      | _plainly => fin 1
      end.

    Global Instance syntax : SAT.t := {
        ops := ops;
        arity := arity;
    }.
  End syntax.

  Section semantics.
    Context {α : GAT.t} (PROP : bi) `{!BiPlainly PROP}.

    Local Open Scope bi_scope.

    Definition interp_aux n (s : ops) :
      (arity s (GTerm.t_prev n) → GTerm.t n) →
      (arity s (GTerm.t_prev n) → PROP) →
      PROP :=
      match s with
      | _plainly => λ _ sem, ■ (sem 0%fin)
      end.

    Global Instance interp : @SATIntp.t PROP α syntax := interp_aux.
  End semantics.

  Class G (PROP : bi) `{!BiPlainly PROP} (α : GAT.t) (β : GATIntp.t) := {
    #[local] G_inG_syntax :: GAT.inG syntax α;
    #[local] G_inG_interp :: GATIntp.inG syntax α (interp PROP) β;
  }.
  (* Global Hint Mode G - + + + : typeclass_instances. *)

  Section definitions.
    Context `{!BiPlainly PROP} `{!G PROP α β}.

    Definition syn_plainly {n} (p : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _plainly, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.
  End definitions.

  Module Import notations.
    Notation "'■' P" := (syn_plainly P) : SAT_scope.
  End notations.

  Section reduction.
    Context `{!BiPlainly PROP} `{!G PROP α β}.

    Global Instance plainly_red n p P :
      SLRed n p P →
      SLRed n (■ p) (■ P).
    Proof. solve_base_sl_red. Qed.

    Lemma plainly_red_base n p :
      ⟦■ p,n⟧ ⊣⊢ ■ ⟦ p ⟧.
    Proof. apply: sl_red. Qed.

  End reduction.

  Global Opaque syn_plainly.

End SPropBiPlainly.
Export SPropBiPlainly.notations.

Module SPropBiBUpd.
  Section syntax.

    Variant ops :=
    | _bupd
    .

    Definition arity (s : ops) (Prev : Type) : Type :=
      match s with
      | _bupd => fin 1
      end.

    Global Instance syntax : SAT.t := {
        ops := ops;
        arity := arity;
    }.
  End syntax.

  Section semantics.
    Context {α : GAT.t} (PROP : bi) `{!BiBUpd PROP}.

    Local Open Scope bi_scope.

    Definition interp_aux n (s : ops) :
      (arity s (GTerm.t_prev n) → GTerm.t n) →
      (arity s (GTerm.t_prev n) → PROP) →
      PROP :=
      match s with
      | _bupd => λ _ sem, |==> (sem 0%fin)
      end.

    Global Instance interp : @SATIntp.t PROP α syntax := interp_aux.
  End semantics.

  Class G (PROP : bi) `{!BiBUpd PROP} (α : GAT.t) (β : GATIntp.t) := {
    #[local] G_inG_syntax :: GAT.inG syntax α;
    #[local] G_inG_interp :: GATIntp.inG syntax α (interp PROP) β;
  }.

  Section definitions.
    Context `{!BiBUpd PROP} `{!G PROP α β}.

    Definition syn_bupd {n} (p : GTerm.t n) : GTerm.t n.
    Proof.
      refine ⟨ _bupd, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.

  End definitions.

  Module Import notations.
    Notation "|==> P" := (syn_bupd P) : SAT_scope.
    Notation "P ==∗ Q" := (P -∗ |==> Q) : SAT_scope.
  End notations.

  Section reduction.
    Context `{!BiBUpd PROP} `{!G PROP α β}.

    Global Instance bupd_red n p P :
      SLRed n p P →
      SLRed n (|==> p) (|==> P).
    Proof. solve_base_sl_red. Qed.

    Lemma bupd_red_base n p :
      ⟦ |==> p, n ⟧ ⊣⊢ (|==> ⟦ p ⟧).
    Proof. apply: sl_red. Qed.

  End reduction.

  Global Opaque syn_bupd.

End SPropBiBUpd.
Export SPropBiBUpd.notations.

(* For BiFUpd, the impl depends on [SATIntp.t], so we can't create simple forms like above.
  We could have an operational TC for this for notation overloading.
*)

From iris.algebra Require Import cmra.
Require Export base_logic iprop own.

(* Small collection of RA for use in syntactic own. *)

Class HRA : Type := HRA_mk : GRA.
Class subHG (Γ : HRA) (Σ : GRA) := subHG_mk : subG Γ Σ.
Global Hint Mode subHG - - : typeclass_instances.

Global Instance subG_reflHH (Γ : HRA) : subG Γ Γ.
Proof. exact: subG_refl. Qed.
Global Instance subG_reflHG (Γ : HRA) : subG Γ (Γ : GRA).
Proof. exact: subG_refl. Qed.

Global Instance subG_app_lGGH (Σ : GRA) (Σ1 : GRA) (Σ2 : HRA) :
  subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_l. Qed.
Global Instance subG_app_lHGG (Σ : HRA) (Σ1 : GRA) (Σ2 : GRA) :
  subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_l. Qed.
Global Instance subG_app_lHGH (Σ : HRA) (Σ1 : GRA) (Σ2 : HRA) :
  subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_l. Qed.
Global Instance subG_app_lHHG (Σ : HRA) (Σ1 : HRA) (Σ2 : GRA) :
  subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_l. Qed.
Global Instance subG_app_lHHH (Σ : HRA) (Σ1 : HRA) (Σ2 : HRA) :
  subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_l. Qed.

Global Instance subG_app_rGHG (Σ : GRA) (Σ1 : HRA) (Σ2 : GRA) :
  subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_r. Qed.
Global Instance subG_app_rHGG (Σ : HRA) (Σ1 : GRA) (Σ2 : GRA) :
  subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_r. Qed.
Global Instance subG_app_rHGH (Σ : HRA) (Σ1 : GRA) (Σ2 : HRA) :
  subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_r. Qed.
Global Instance subG_app_rHHG (Σ : HRA) (Σ1 : HRA) (Σ2 : GRA) :
  subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_r. Qed.
Global Instance subG_app_rHHH (Σ : HRA) (Σ1 : HRA) (Σ2 : HRA) :
  subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof. exact: subG_app_r. Qed.

Global Instance subG_subHG (Γ : HRA) (Σ : GRA) : subG Γ Σ → subHG Γ Σ.
Proof. intros H. exact: H. Qed.

Global Instance index_in_subG (Γ : HRA) (i : gid Γ) :
  inG (@GRA_lookup Γ i) Γ.
Proof. exists i. reflexivity. Defined.
Global Instance in_subG (Γ : HRA) (Σ : GRA) `{Hin : !inG M Γ} :
  subHG Γ Σ → inG M Σ.
Proof.
  intros HΓΣ. destruct Hin. subst M.
  destruct (HΓΣ inG_id) as [j ->].
  exists j. reflexivity.
Qed.

Module SPropiProp.
  Section syntax.
    Context {Γ : HRA}.

    Variant ops : Type :=
    | _own {i} (γ : gname) (r : (@GRA_lookup Γ) i)
    | _own_bupd
    .

    Definition arity (s : ops) (Prev : Type) : Type :=
      match s with
      | _own _ _ => fin 0
      | _own_bupd => fin 1
      end.

    Global Instance syntax : SAT.t := {
        ops := ops;
        arity := arity;
    }.
  End syntax.

  Section semantics.
    Context {α : GAT.t} {Γ : HRA} {Σ : GRA} `{!subHG Γ Σ}.

    Local Open Scope bi_scope.

    Definition interp_aux n (s : ops) :
      (arity s (GTerm.t_prev n) → GTerm.t n) →
      (arity s (GTerm.t_prev n) → iProp Σ) →
      iProp Σ :=
      match s with
      | _own γ r => λ _ _, own γ r
      | _own_bupd => λ _ sem, o=> (sem 0%fin)
      end.

    Global Instance interp : @SATIntp.t (iProp Σ) α syntax := interp_aux.
  End semantics.

  Class G (Σ : GRA) (Γ : HRA) (α : GAT.t) (β : GATIntp.t) `{!subHG Γ Σ} := {
    #[local] G_inG_syntax :: GAT.inG syntax α;
    #[local] G_inG_interp :: GATIntp.inG syntax α interp β;
  }.

  Section definitions.
    Context `{!subHG Γ Σ, !G Σ Γ α β}.
    Definition syn_own `{IN: !inG M Γ} {n} (γ : positive) (r : M) : GTerm.t n.
      destruct IN. subst.
      refine ⟨ _own γ r, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition syn_own_bupd {n} (p : GTerm.t n) : GTerm.t n.
      refine ⟨ _own_bupd, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.
  End definitions.

  Module Import notations.
    Notation "'sown'" := (syn_own) : SAT_scope.
    Notation "o=> P" := (syn_own_bupd P%SAT) : SAT_scope.
    Notation "P o==∗ Q" := (P -∗ o=> Q)%SAT : SAT_scope.
  End notations.

  Section reduction.
    Context `{!subHG Γ Σ, !G Σ Γ α β}.

    Global Instance own_red `{IN: !inG M Γ} n γ (r : M) :
      SLRed n (sown γ r) (own γ r).
    Proof. destruct IN. subst. solve_base_sl_red. Qed.

    Global Instance own_bupd_red n (p : GTerm.t n) P :
      SLRed n p P →
      SLRed n (o=> p) (o=> P).
    Proof. solve_base_sl_red. Qed.

    Lemma own_bupd_red_base n (p : GTerm.t n) :
      ⟦o=> p⟧ ⊣⊢ o=> ⟦p⟧.
    Proof. apply: sl_red. Qed.
  End reduction.

  Global Opaque syn_own.
End SPropiProp.
Export SPropiProp.notations.

Module SL.
  Class G (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t) `{!subHG Γ Σ} := {
    #[global] G_Bi :: SPropBi.G (iProp Σ) α β τ;
    #[global] G_BiPlainly :: SPropBiPlainly.G (iProp Σ) α β;
    #[global] G_BiBUpd :: SPropBiBUpd.G (iProp Σ) α β;
    #[global] G_iProp :: SPropiProp.G Σ Γ α β;
  }.
End SL.

(* Simple sProp reduction tactics. *)
From stdpp Require Import ssreflect.

From iris.prelude Require Import options.

Local Open Scope SAT_scope.

Import SPropBi SPropBiPlainly SPropBiBUpd SPropiProp.

(* Theoretically, we could unfold defs and call apply _. But this should give better "progress" in case something fails. *)
Ltac solve_sl_red :=
  intros;
  lazymatch goal with
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _ _) _ => unfold fs
  | |- SLRed _ (?fs _ _) _ => unfold fs
  | |- SLRed _ (?fs _) _ => unfold fs
  | |- SLRed _ ?fs _ => unfold fs
  | _ => idtac
  end;
  lazymatch goal with
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _ _) => unfold Ps
  | |- SLRed _ _ (?Ps _) => unfold Ps
  | |- SLRed _ _ ?Ps => unfold Ps
  | _ => idtac
  end;
  match goal with
  | |- SLRed _ _ _ => unfold SLRed
  | _ => idtac
  end;
  match goal with
  | |- ⟦ match ?x with _ => _ end ⟧ ⊣⊢ _ => destruct x; solve_sl_red
  | |- ⟦ ⟨ _, _ ⟩ ⟧ ⊣⊢_ => rewrite SATRed.cur /=; try reflexivity
  | |- ⟦ ⤉ _ ⟧ ⊣⊢ _ => rewrite lift_red_base; solve_sl_red
  | |- ⟦ sown _ _ ⟧ ⊣⊢ _ => rewrite own_red; try reflexivity
  | |- ⟦ o=> _ ⟧ ⊣⊢ _ =>
    rewrite own_bupd_red_base; apply bupd_proper; solve_sl_red
  | |- ⟦ ⌜ _ ⌝ ⟧ ⊣⊢ _ => rewrite pure_red; try reflexivity
  | |- ⟦ _ ∧ _ ⟧ ⊣⊢ _ =>
    rewrite and_red_base; apply bi.and_proper; solve_sl_red
  | |- ⟦ _ ∨ _ ⟧ ⊣⊢ _ =>
    rewrite or_red_base; apply bi.or_proper; solve_sl_red
  | |- ⟦ _ → _ ⟧ ⊣⊢ _ =>
    rewrite impl_red_base; apply bi.impl_proper; solve_sl_red
  | |- ⟦ ∀ _, _ ⟧ ⊣⊢ _ =>
    rewrite forall_red_base; apply bi.forall_proper; intros ?; solve_sl_red
  | |- ⟦ ∃ _, _ ⟧ ⊣⊢ _ =>
    rewrite exist_red_base; apply bi.exist_proper; intros ?; solve_sl_red
  | |- ⟦ emp ⟧ ⊣⊢ _ => rewrite empty_red; reflexivity
  | |- ⟦ _ ∗ _ ⟧ ⊣⊢ _ =>
    rewrite sep_red_base; apply bi.sep_proper; solve_sl_red
  | |- ⟦ _ -∗ _ ⟧ ⊣⊢ _ =>
    rewrite wand_red_base; apply bi.wand_proper; solve_sl_red
  | |- ⟦ □ _ ⟧ ⊣⊢ _ =>
    rewrite intuitionistically_red_base; apply bi.intuitionistically_proper; solve_sl_red
  | |- ⟦ ■ _ ⟧ ⊣⊢ _ =>
    rewrite plainly_red_base; apply plainly_proper; solve_sl_red
  | |- ⟦ |==> _ ⟧ ⊣⊢ _ =>
    rewrite bupd_red_base; apply bupd_proper; solve_sl_red
  | |- ⟦ [∗ list] _ ↦ _ ∈ _, _ ⟧ ⊣⊢ _ =>
    rewrite sepL_red_base; apply big_sepL_proper; solve_sl_red
  | |- ⟦ [∗ map] _ ↦ _ ∈ _, _ ⟧ ⊣⊢ _ =>
    rewrite sepM_red_base; apply big_sepM_proper; solve_sl_red
  | |- ⟦ [∗ set] _ ∈ _, _ ⟧ ⊣⊢ _ =>
    rewrite sepS_red_base; apply big_sepS_proper; solve_sl_red
  | |- ⟦ [∗ mset] _ ∈ _, _ ⟧ ⊣⊢ _ =>
    rewrite sepMS_red_base; apply big_sepMS_proper; solve_sl_red
  | |- ⟦ ?f ⟧ ⊣⊢ _ =>
    (* Stuck on base case. *)
    try (reflexivity || rewrite {1}(sl_red f));
    (* Derived form. *)
    try (reflexivity || f_equiv; try intros ?; solve_sl_red) (* [try intros ?] helps with [Proper] instances involing pointwise relations. *)
  | _ => idtac
  end.

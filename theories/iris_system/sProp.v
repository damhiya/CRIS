From iris.algebra Require Import cmra.
From stdpp Require Import coPset gmap namespaces.
Require Import sflib.
From iris Require Import bi.big_op.
(* From iris Require base_logic.lib.invariants. *)
From Coq Require Import Program Arith.
Require Export Coqlib base_logic iprop own SAT.

Global Instance domain (Σ : GRA) : SemDom.t := { dom := iProp Σ }.

(* Note that the types in a group has the type PF.t *)
(* The types in all groups *)
Module TypG.
  Class t: Type := __TYP : GAT.t.
End TypG.

Class HRA : Type := HRA_mk : GRA.
(* Class subG (Γ : HRA) (Σ : GRA) := subG_mk : subG Γ Σ. *)
(* Global Instance subG_subG (Γ : HRA) (Σ : GRA) : subG Γ Σ → subG Γ Σ. auto. Qed. *)

Global Instance index_inG (Γ : HRA) (i : gid Γ) : inG (GRA_lookup i) Γ.
Proof.
  econstructor; eauto.
Defined.
Global Program Instance in_subG (Γ : HRA) (Σ : GRA) `{emb : !inG M Γ} : subG Γ Σ → inG M Σ.
Next Obligation.
  intros. destruct emb. destruct (s inG_id). exact x.
Defined.
Next Obligation.
  intros. destruct emb. simpl. destruct (s inG_id). subst. f_equal. eauto.
Defined.
Lemma inG_id_in_subG (Γ : HRA) (Σ : GRA) (RA : cmra) inΓ ΓinΣ :
  @inG_id RA Σ (@in_subG Γ Σ RA inΓ ΓinΣ) = let '(exist _ id _) := (ΓinΣ (inG_id inΓ)) in id.
Proof.
  unfold in_subG; simpl. unfold sProp.in_subG_obligation_1. destruct inΓ. simpl. reflexivity.
Qed.

(** Types for Separation Logic **)
Module ST. Section ST.
  Inductive type : Type :=
  | baseT (t : Type) : type
  | sPropT : type
  | funT : type → type → type
  | prodT : type → type → type
  | sumT : type → type → type
  | listT : type → type
  | gmapT : type → type
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

Module GST.
  Class t (τ : TypG.t) := { #[global] inG :: @GAT.inG ST.t τ }.
End GST.

(** Notations and Coercions. *)
Coercion ST.baseT : Sortclass >-> ST.type.

Notation "⇣ T" := (ST.baseT T) (at level 90) : SAT_scope.
Notation "'Φ'" := (ST.sPropT) : SAT_scope.
Infix "->" := (ST.funT) : SAT_scope.
Infix "*" := (ST.prodT) : SAT_scope.
Infix "+" := (ST.sumT) : SAT_scope.

Notation "'τ{' t ',' n '}'" := (@SAT.arity ST.t t (GTerm.t_prev n)) : SAT_scope.
Notation "'τ{' t '}'" := (@SAT.arity ST.t t (GTerm.t_prev _)) : SAT_scope.

(* Separation Logic *)
(* TODO : The functionalities below need to be separated! after coarse refactoring *)
Module SL.
  Section syntax.
    Context {τ : TypG.t} {α : @GAT.t} {Γ : HRA}.

    Variant ops : Type :=
    | _own i (γ : positive) (r : (@GRA_lookup Γ) i)
    | _pure (P : Prop)
    | _and
    | _or
    | _impl
    | _univ i (ty : (τ i).(SAT.ops))
    | _ex   i (ty : (τ i).(SAT.ops))
    | _empty
    | _sepconj
    | _wand
    | _persistently
    | _plainly
    | _upd.

    Definition arity (op : ops) (term_prev : Type) : Type :=
      match op with
      | _own γ i r => fin 0
      | _pure P => fin 0
      | _and => fin 2
      | _or => fin 2
      | _impl => fin 2
      | _univ i ty => (τ i).(SAT.arity) ty term_prev
      | _ex   i ty => (τ i).(SAT.arity) ty term_prev
      | _empty => fin 0
      | _sepconj => fin 2
      | _wand => fin 2
      | _persistently => fin 1
      | _plainly => fin 1
      | _upd => fin 1
      end.

    Global Instance syntax : SAT.t := {
        ops := ops;
        arity := arity;
    }.
  End syntax.

  Section semantics.
    Context {τ : TypG.t} {α : @GAT.t} {Γ : HRA} {Σ : GRA} `{!subG Γ Σ}.
    Definition interp_aux n (op : ops)
        : (arity op (GTerm.t_prev n) → GTerm.t n) → (arity op (GTerm.t_prev n) → iProp Σ) → iProp Σ :=
      match op with
      | _own i γ r => λ _ _, @own _ _ _ γ r
      | _pure P => λ _ _, ⌜P⌝%I
      | _and => λ _ sem, ((sem 0%fin) ∧ (sem 1%fin))%I
      | _or => λ _ sem, ((sem 0%fin) ∨ (sem 1%fin))%I
      | _impl => λ _ sem, ((sem 0%fin) → (sem 1%fin))%I
      | _univ i ty => λ _ sem, bi_forall sem
      | _ex   i ty => λ _ sem, bi_exist sem
      | _empty => λ _ _, emp%I
      | _sepconj => λ _ sem, ((sem 0%fin) ∗ (sem 1%fin))%I
      | _wand => λ _ sem, ((sem 0%fin) -∗ (sem 1%fin))%I
      | _persistently => λ _ sem, (<pers> (sem 0%fin))%I
      | _plainly => λ _ sem, (■ (sem 0%fin))%I
      | _upd => λ _ sem, (|==> (sem 0%fin))%I
      end.

    Global Instance interp : @SATIntp.t _ α syntax := interp_aux.
  End semantics.

  Class G (Σ : GRA) (Γ : HRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t) `{!subG Γ Σ} := {
    #[local] G_inG :: GATIntp.inG SL.syntax α SL.interp β;
  }.

  Section definitions.
    Context `{!subG (Γ : HRA) Σ, !G Σ Γ α β τ}.
    Local Existing Instances G_inG.

    Definition own `{IN: !inG M Γ} {n} (γ : positive) (r : M) : GTerm.t n.
      destruct IN. subst.
      refine ⟨ _own _ γ r, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition pure {n} (P : Prop) : GTerm.t n.
      refine ⟨ _pure P, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition and {n} (p1 p2 : GTerm.t n) : GTerm.t n.
      refine ⟨ _and, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition or {n} (p1 p2 : GTerm.t n) : GTerm.t n.
      refine ⟨ _or, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition impl {n} (p1 p2 : GTerm.t n) : GTerm.t n.
      refine ⟨ _impl, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.
    
    Definition univ `{IN: @GAT.inG T τ} {n} (ty: T.(SAT.ops)) (p: T.(SAT.arity) ty (GTerm.t_prev n) → GTerm.t n)
        : GTerm.t n.
      destruct IN. subst.
      exact ⟨ _univ _ ty, p ⟩%SAT.
    Defined.

    Definition ex `{IN: @GAT.inG T τ} {n} (ty: T.(SAT.ops)) (p: T.(SAT.arity) ty (GTerm.t_prev n) → GTerm.t n)
        : GTerm.t n.
      destruct IN. subst.
      exact ⟨ _ex _ ty, p ⟩%SAT.
    Defined.

    Definition empty {n} : GTerm.t n.
      refine ⟨ _empty, _ ⟩%SAT.
      i. inv X.
    Defined.

    Definition sepconj {n} (p1 p2 : GTerm.t n) : GTerm.t n.
      refine ⟨ _sepconj, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition wand {n} (p1 p2 : GTerm.t n) : GTerm.t n.
      refine ⟨ _wand, _ ⟩%SAT.
      i. destruct X.
      - exact p1.
      - exact p2.
    Defined.

    Definition persistently {n} (p : GTerm.t n) : GTerm.t n.
      refine ⟨ _persistently, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.

    Definition plainly {n} (p : GTerm.t n) : GTerm.t n.
      refine ⟨ _plainly, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.

    Definition upd {n} (p : GTerm.t n) : GTerm.t n.
      refine ⟨ _upd, _ ⟩%SAT.
      i. inv X; [|inv H0].
      exact p.
    Defined.

    Definition affinely {n} (p : GTerm.t n) : GTerm.t n :=
      and empty p.

    Definition sepM
              n {K} {H1 : EqDecision K} {H2 : Countable K}
              {A} (I : @gmap K H1 H2 A)
              (f : K → A → GTerm.t n)
      : GTerm.t n :=
      fold_right (fun hd tl => sepconj (uncurry f hd) tl) empty (map_to_list I).

    Definition sepS n {K} {H1 : EqDecision K} {H2 : Countable K}
        (I : @gset K H1 H2)
        (f : K → GTerm.t n)
        : GTerm.t n :=
      fold_right (fun hd tl => sepconj (f hd) tl) empty (elements I).

    Definition sepL1
              n {A} (I : list A)
              (f : A → GTerm.t n)
      : GTerm.t n :=
      fold_right (fun hd tl => sepconj (f hd) tl) empty I.

  End definitions.
End SL.

(* Module CtxSL.
  Class t (Σ : GRA) (Γ : HRA) α β τ 
    `{!subG Γ Σ} `{!CtxST.t τ} `{!SATIntp.inG SL.syntax α SL.t β} := mk_t : unit.
End CtxSL. *)

(** Notations *)
Local Open Scope SAT_scope.

Notation "'⌜' P '⌝'" := (SL.pure P) : SAT_scope.
Notation "'⊤'" := ⌜True⌝ : SAT_scope.
Notation "'⊥'" := ⌜False⌝ : SAT_scope.

Notation "<own>" := (SL.own) (at level 20) : SAT_scope.
Notation "'<pers>' P" := (SL.persistently P) : SAT_scope.
Notation "'<affine>' P" := (SL.affinely P) : SAT_scope.
Notation "□ P" := (<affine> <pers> P) : SAT_scope.
Notation "■ P" := (SL.plainly P) : SAT_scope.
Notation "|==> P" := (SL.upd P) : SAT_scope.
Infix "∧" := (SL.and) : SAT_scope.
Infix "∨" := (SL.or) : SAT_scope.
Infix "→" := (SL.impl) : SAT_scope.
Notation "¬ P" := (P → False) : SAT_scope.
Infix "∗" := (SL.sepconj) : SAT_scope.
Infix "-∗" := (SL.wand) : SAT_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : SAT_scope.
Notation f_forall A := (SL.univ A).
Notation "∀'" := (f_forall _) (only parsing) : SAT_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%SAT)) ..)) : SAT_scope.
Notation f_exist A := (SL.ex A).
Notation "∃'" := (f_exist _) (only parsing) : SAT_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%SAT)) ..)) : SAT_scope.
Notation "'emp'" := (SL.empty) : SAT_scope.

Notation "'[∗' n 'map]' k ↦ x ∈ m , P" :=
  (SL.sepM n m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x at level 1, right associativity,
      format "[∗  n  map]  k  ↦  x  ∈  m ,  P") : SAT_scope.
Notation "'[∗' n , A 'map]' k ↦ x ∈ m , P" :=
  (SL.sepM n (A:=A) m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x, A at level 1, right associativity,
      format "[∗  n  ,  A  map]  k  ↦  x  ∈  m ,  P") : SAT_scope.
Notation "'[∗' n 'set]' x ∈ X , P" :=
  (SL.sepS n X (fun x => P))
    (at level 200, n at level 1, X at level 10, x at level 1, right associativity,
      format "[∗  n  set]  x  ∈  X ,  P") : SAT_scope.
Notation "'[∗' n 'list]' x ∈ l , P" :=
  (SL.sepL1 n l (fun x => P))
    (at level 200, n at level 1, l at level 10, x at level 1, right associativity,
      format "[∗  n  list]  x  ∈  l ,  P") : SAT_scope.
Notation "'[∗' n , A 'list]' x ∈ l , P" :=
  (SL.sepL1 n (A:=A) l (fun x => P))
    (at level 200, n at level 1, l at level 10, x, A at level 1, right associativity,
      format "[∗  n ,  A  list]  x  ∈  l ,  P") : SAT_scope.

Module SLRed. Section RED.
  Context `{!subG (Γ : HRA) Σ, !SL.G Σ Γ α β τ}.
  Notation interp := (GTermSem.t (Δ := domain Σ)).

  Lemma own `{!inG M Γ} n γ (r : M) :
    interp n (SL.own γ r) = own γ r.
  Proof.
    depdes inG0. subst. unfold SL.own, eq_rect_r. ss.
    rewrite @SATRed.cur. ss.
  Qed.

  Lemma pure n P : interp n (SL.pure P) = ⌜P⌝%I.
  Proof. unfold SL.pure. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma and n p q :
    interp n (SL.and p q) = (interp n p ∧ interp n q)%I.
  Proof. unfold SL.and. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma or n p q :
    interp n (SL.or p q) = (interp n p ∨ interp n q)%I.
  Proof. unfold SL.or. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma impl n p q :
    interp n (SL.impl p q) = (interp n p → interp n q)%I.
  Proof. unfold SL.impl. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma univ `{T : SAT.t} `{@GAT.inG T τ} n (ty: T.(SAT.ops)) p :
    interp n (SL.univ ty p) = (∀ x : (T.(SAT.arity) ty (GTerm.t_prev n)), interp n (p x))%I.
  Proof.
    destruct H0 eqn : EQ. subst.
    unfold SL.univ, eq_rect_r. ss.
    rewrite @SATRed.cur. reflexivity.
  Qed.

  Lemma ex `{@GAT.inG T τ} n ty p :
    interp n (SL.ex ty p) = (∃ x, interp n (p x))%I.
  Proof.
    destruct H0 eqn : EQ. subst.
    unfold SL.ex, eq_rect_r. ss.
    rewrite @SATRed.cur. reflexivity.
  Qed.

  Lemma empty n :
    interp n SL.empty = emp%I.
  Proof. unfold SL.empty. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma sepconj n p q :
    interp n (SL.sepconj p q) = (interp n p ∗ interp n q)%I.
  Proof. unfold SL.sepconj. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma wand n p q :
    interp n (SL.wand p q) = (interp n p -∗ interp n q)%I.
  Proof. unfold SL.wand. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma persistently n p :
    interp n (SL.persistently p) = (<pers> interp n p)%I.
  Proof. unfold SL.persistently. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma plainly n p :
    interp n (SL.plainly p) = (■ (interp n p))%I.
  Proof. unfold SL.plainly. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma upd n p :
    interp n (SL.upd p) = (|==> interp n p)%I.
  Proof. unfold SL.upd. rewrite @SATRed.cur. reflexivity. Qed.

  Lemma affinely n p :
    interp n (SL.affinely p) = (<affine> interp n p)%I.
  Proof. unfold SL.affinely. rewrite ->and, empty. reflexivity. Qed.

  Lemma intuitionistically n p :
    interp n (SL.affinely (SL.persistently p)) = (□ interp n p)%I.
  Proof. rewrite ->affinely, persistently. reflexivity. Qed.

  Lemma sepM n K {H1 : EqDecision K} {H2 : Countable K} A I f :
    interp n (SL.sepM n I f (K:=K) (A:=A)) = ([∗ map] i ↦ a ∈ I, interp n (f i a))%I.
  Proof.
    ss. unfold big_opM. rewrite seal_eq. unfold big_op.big_opM_def.
    unfold SL.sepM. simpl. remember (map_to_list I) as L.
    clear HeqL I. induction L.
    { ss. rewrite empty. eauto. }
    ss. rewrite sepconj. rewrite IHL. f_equal.
    destruct a. ss.
  Qed.

  Lemma sepS n K {H1 : EqDecision K} {H2 : Countable K} I f :
    interp n (SL.sepS n I f (K:=K)) = ([∗ set] i ∈ I, interp n (f i))%I.
  Proof.
    ss. unfold big_opS. rewrite seal_eq. unfold big_op.big_opS_def.
    unfold SL.sepS. remember (elements I) as L.
    clear HeqL I. induction L.
    { ss. rewrite empty. eauto. }
    ss. rewrite sepconj. rewrite IHL. f_equal.
  Qed.

  Lemma sepL1 n A I f :
    interp n (SL.sepL1 n I f (A:=A)) = ([∗ list] a ∈ I, interp n (f a))%I.
  Proof.
    ss. induction I; ss.
    { rewrite empty. ss. }
    rewrite sepconj. rewrite IHI. f_equal.
  Qed.

  End RED.
End SLRed.

Global Opaque SL.own.
Global Opaque SL.pure.
Global Opaque SL.and.
Global Opaque SL.or.
Global Opaque SL.impl.
Global Opaque SL.univ.
Global Opaque SL.ex.
Global Opaque SL.empty.
Global Opaque SL.sepconj.
Global Opaque SL.wand.
Global Opaque SL.persistently.
Global Opaque SL.plainly.
Global Opaque SL.upd.

Global Opaque GTermSem.t.

(* Simple sProp reduction tactics. *)
From stdpp Require Import ssreflect.
Ltac SL_red :=
  (hrepeat do 1
   (tryany (do 1 rewrite ! @SLRed.sepconj)
    tryany (do 1 rewrite ! @SLRed.and)
    tryany (do 1 rewrite ! @SLRed.or)
    tryany (do 1 rewrite ! @SLRed.impl)
    tryany (do 1 rewrite ! @SLRed.wand)
    tryany (do 1 rewrite ! @SLRed.pure)
    tryany (do 1 rewrite ! @SLRed.univ)
    tryany (do 1 rewrite ! @SLRed.ex)
    tryany (do 1 rewrite ! @SLRed.empty)
    tryany (do 1 rewrite ! @SLRed.persistently)
    tryany (do 1 rewrite ! @SLRed.plainly)
    tryany (do 1 rewrite ! @SLRed.upd)
    tryany (do 1 rewrite ! @SLRed.affinely)
    tryany (do 1 rewrite ! @SLRed.intuitionistically)
    tryany (do 1 rewrite ! @SLRed.sepM)
    tryany (do 1 rewrite ! @SLRed.sepS)
    tryany (do 1 rewrite ! @SLRed.sepL1)
    tryany (do 1 rewrite ! @SLRed.own)
           (try (change (GTerm.t_prev (S ?n)) with (); fail 1);
            change (GTerm.t_prev (S ?n)) with (GTerm.t n)));
    simpl);
  simpl.

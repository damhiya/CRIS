From iris.algebra Require Import cmra.
From stdpp Require Import coPset gmap namespaces.
Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Export Coqlib PCM IPM SRF.

Module HRA.

  Section HRA.

  Class t := __HRA : GRA.t.

  Class subG (Γ : t) (Σ : GRA.t) : Type := {
    subG_map : nat -> nat;
    subG_prf : forall i, (@GRA.gra_map Σ) (subG_map i) = (@GRA.gra_map Γ) i;
  }.

  Coercion subG_map : subG >-> Funclass.

  Context `{sub : @subG Γ Σ}.

  Global Program Instance embed (i:nat) : @GRA.inG (@GRA.gra_map Γ i) Σ := {
      inG_id := sub i;
    }.
  Next Obligation. i. symmetry. apply HRA.subG_prf. Qed.

  Global Program Instance in_subG `{M : ucmra} `{emb : @GRA.inG M Γ} : @GRA.inG M Σ := {
      inG_id := sub.(subG_map) emb.(GRA.inG_id);
      }.
  Next Obligation.
    i. destruct emb. subst. destruct sub. ss.
  Qed.

  End HRA.

End HRA.

Coercion HRA.subG_map : HRA.subG >-> Funclass.

(* Note that the types in a group has the type PF.t *)

(* The types in all groups *)
Module Typ.

  Class t: Type := __TYP : GPF.t.

End Typ.

(** Types for Separation Logic **)

Module ST.

  Section TYPES.

  Inductive type : Type :=
  | baseT (t : Type) : type
  | sPropT : type
  | funT : type -> type -> type
  | prodT : type -> type -> type
  | sumT : type -> type -> type
  | listT : type -> type
  | gmapT : type -> type
  | metaT : type
  .

  Fixpoint interp (ty : type) (sProp : Type) : Type :=
    match ty with
    | baseT b => b
    | sPropT => sProp
    | funT ty1 ty2 => (interp ty1 sProp -> interp ty2 sProp)
    | prodT ty1 ty2 => prod (interp ty1 sProp) (interp ty2 sProp)
    | sumT ty1 ty2 => sum (interp ty1 sProp) (interp ty2 sProp)
    | listT ty1 => list (interp ty1 sProp)
    | gmapT ty1 => gmap positive (interp ty1 sProp)
    | metaT => Type
    end.

  Global Instance t : PF.t := {
      shp := type;
      deg := interp;
    }.

  End TYPES.

End ST.

Module CtxST.

  Class t `{τ: Typ.t}
    `{_C: @GPF.inG ST.t τ}
    := ctxSL: unit.

End CtxST.

(** Notations and Coercions. *)
Coercion ST.baseT : Sortclass >-> ST.type.

Notation "⇣ T" := (ST.baseT T) (at level 90) : SRF_scope.
Notation "'Φ'" := (ST.sPropT) : SRF_scope.
Infix "->" := (ST.funT) : SRF_scope.
Infix "*" := (ST.prodT) : SRF_scope.
Infix "+" := (ST.sumT) : SRF_scope.

Notation "'τ{' t ',' n '}'" := (@PF.deg ST.t t (SRFSyn.t_prev n)) : SRF_scope.
Notation "'τ{' t '}'" := (@PF.deg ST.t t (SRFSyn.t_prev _)) : SRF_scope.

(* Separation Logic *)

Module SL.

  Section SL.

  Context `{τ: Typ.t}.
  Context `{Γ: HRA.t}.
  
  Variant shape : Type :=
    | _ownm i (r : (@GRA.gra_map Γ) i)
    | _pure (P : Prop)
    | _and
    | _or
    | _impl
    | _univ i (ty : (τ i).(PF.shp))
    | _ex   i (ty : (τ i).(PF.shp))
    | _empty
    | _sepconj
    | _wand
    | _persistently
    | _plainly
    | _upd
  .

  Definition degree (s : shape) (Prev : Type) : Type :=
    match s with
    | _ownm i r => fin 0
    | _pure P => fin 0
    | _and => fin 2
    | _or => fin 2
    | _impl => fin 2
    | _univ i ty => (τ i).(PF.deg) ty Prev
    | _ex   i ty => (τ i).(PF.deg) ty Prev
    | _empty => fin 0
    | _sepconj => fin 2
    | _wand => fin 2
    | _persistently => fin 1
    | _plainly => fin 1
    | _upd => fin 1
    end.

  Global Instance syntax : PF.t := {
      shp := shape;
      deg := degree;
  }.

  Context `{α: @SRFCons.t}.
  Context `{_C0: @HRA.subG Γ Σ}.
  
  Global Instance domain : SRFDom.t := {
    dom := iProp;
  }.

  Definition interp n (s : shape)
      : (degree s (SRFSyn.t_prev n) -> SRFSyn.t n) -> (degree s (SRFSyn.t_prev n) -> iProp) -> iProp :=
    match s with
    | _ownm i r => fun _ _ => OwnM r
    | _pure P => fun _ _ => ⌜P⌝%I
    | _and => fun _ sem => ((sem 0%fin) ∧ (sem 1%fin))%I
    | _or => fun _ sem => ((sem 0%fin) ∨ (sem 1%fin))%I
    | _impl => fun _ sem => ((sem 0%fin) → (sem 1%fin))%I
    | _univ i ty => fun _ sem => bi_forall sem
    | _ex   i ty => fun _ sem => bi_exist sem
    | _empty => fun _ _ => emp%I
    | _sepconj => fun _ sem => ((sem 0%fin) ∗ (sem 1%fin))%I
    | _wand => fun _ sem => ((sem 0%fin) -∗ (sem 1%fin))%I
    | _persistently => fun _ sem => (<pers> (sem 0%fin))%I
    | _plainly => fun _ sem => (■ (sem 0%fin))%I
    | _upd => fun _ sem => (|==> (sem 0%fin))%I
    end.

  Global Instance t: SRFIntpM.t := interp.

  Context `{@SRFIntp.inG _ _ _ t β}.
  
  Definition ownm `{IN: @GRA.inG M Γ} {n} (r: M) : SRFSyn.t n.
    destruct IN. subst.
    refine ⟨ _ownm _ r, _ ⟩%SRF.
    i. inv X.
  Defined.

  Definition pure {n} (P : Prop) : SRFSyn.t n.
    refine ⟨ _pure P, _ ⟩%SRF.
    i. inv X.
  Defined.

  Definition and {n} (p1 p2 : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _and, _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition or {n} (p1 p2 : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _or, _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition impl {n} (p1 p2 : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _impl, _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.
  
  Definition univ `{IN: @GPF.inG T τ} {n} (ty: T.(PF.shp)) (p: T.(PF.deg) ty (SRFSyn.t_prev n) -> SRFSyn.t n) : SRFSyn.t n.
    destruct IN. subst.
    exact ⟨ _univ _ ty, p ⟩%SRF.
  Defined.

  Definition ex `{IN: @GPF.inG T τ} {n} (ty: T.(PF.shp)) (p: T.(PF.deg) ty (SRFSyn.t_prev n) -> SRFSyn.t n) : SRFSyn.t n.
    destruct IN. subst.
    exact ⟨ _ex _ ty, p ⟩%SRF.
  Defined.

  Definition empty {n} : SRFSyn.t n.
    refine ⟨ _empty, _ ⟩%SRF.
    i. inv X.
  Defined.

  Definition sepconj {n} (p1 p2 : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _sepconj, _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition wand {n} (p1 p2 : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _wand, _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition persistently {n} (p : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _persistently, _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition plainly {n} (p : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _plainly, _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition upd {n} (p : SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ _upd, _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition affinely {n} (p : SRFSyn.t n) : SRFSyn.t n :=
    and empty p.

  Definition sepM
             n {K} {H1 : EqDecision K} {H2 : Countable K}
             {A} (I : @gmap K H1 H2 A)
             (f : K -> A -> SRFSyn.t n)
    : SRFSyn.t n :=
    fold_right (fun hd tl => sepconj (uncurry f hd) tl) empty (map_to_list I).

  Definition sepS n {K} {H1 : EqDecision K} {H2 : Countable K}
      (I : @gset K H1 H2)
      (f : K -> SRFSyn.t n)
      : SRFSyn.t n :=
    fold_right (fun hd tl => sepconj (f hd) tl) empty (elements I).

  Definition sepL1
             n {A} (I : list A)
             (f : A -> SRFSyn.t n)
    : SRFSyn.t n :=
    fold_right (fun hd tl => sepconj (f hd) tl) empty I.

  End SL.

End SL.

Module CtxSL.

  Class t `{Γ: HRA.t} `{Σ: GRA.t} `{α: SRFCons.t} `{β: @SRFIntp.t SL.domain α}
    `{_C: CtxST.t}
    `{_C: @HRA.subG Γ Σ}
    `{_C: @SRFIntp.inG SL.domain _ α SL.t β}
    := ctxSL: unit.
  
End CtxSL.

(** Notations *)

Local Open Scope SRF_scope.

Notation "'⌜' P '⌝'" := (SL.pure P) : SRF_scope.
Notation "'⊤'" := ⌜True⌝ : SRF_scope.
Notation "'⊥'" := ⌜False⌝ : SRF_scope.

Notation "'<ownm>' r" := (SL.ownm r) (at level 20) : SRF_scope.
Notation "'<pers>' P" := (SL.persistently P) : SRF_scope.
Notation "'<affine>' P" := (SL.affinely P) : SRF_scope.
Notation "□ P" := (<affine> <pers> P) : SRF_scope.
Notation "■ P" := (SL.plainly P) : SRF_scope.
Notation "|==> P" := (SL.upd P) : SRF_scope.
Infix "∧" := (SL.and) : SRF_scope.
Infix "∨" := (SL.or) : SRF_scope.
Infix "→" := (SL.impl) : SRF_scope.
Notation "¬ P" := (P → False) : SRF_scope.
Infix "∗" := (SL.sepconj) : SRF_scope.
Infix "-∗" := (SL.wand) : SRF_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : SRF_scope.
Notation f_forall A := (SL.univ A).
Notation "∀'" := (f_forall _) (only parsing) : SRF_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%SRF)) ..)) : SRF_scope.
Notation f_exist A := (SL.ex A).
Notation "∃'" := (f_exist _) (only parsing) : SRF_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%SRF)) ..)) : SRF_scope.
Notation "'emp'" := (SL.empty) : SRF_scope.

Notation "'[∗' n 'map]' k ↦ x ∈ m , P" :=
  (SL.sepM n m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x at level 1, right associativity,
      format "[∗  n  map]  k  ↦  x  ∈  m ,  P") : SRF_scope.
Notation "'[∗' n , A 'map]' k ↦ x ∈ m , P" :=
  (SL.sepM n (A:=A) m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x, A at level 1, right associativity,
      format "[∗  n  ,  A  map]  k  ↦  x  ∈  m ,  P") : SRF_scope.
Notation "'[∗' n 'set]' x ∈ X , P" :=
  (SL.sepS n X (fun x => P))
    (at level 200, n at level 1, X at level 10, x at level 1, right associativity,
      format "[∗  n  set]  x  ∈  X ,  P") : SRF_scope.
Notation "'[∗' n 'list]' x ∈ l , P" :=
  (SL.sepL1 n l (fun x => P))
    (at level 200, n at level 1, l at level 10, x at level 1, right associativity,
      format "[∗  n  list]  x  ∈  l ,  P") : SRF_scope.
Notation "'[∗' n , A 'list]' x ∈ l , P" :=
  (SL.sepL1 n (A:=A) l (fun x => P))
    (at level 200, n at level 1, l at level 10, x, A at level 1, right associativity,
      format "[∗  n ,  A  list]  x  ∈  l ,  P") : SRF_scope.

Module SLRed.

  Section RED.

  Context `{_C : CtxSL.t}.
  Notation interp := (SRFSem.t (Δ := @SL.domain Σ)).

  Lemma ownm `{@GRA.inG M Γ} n (r : M) :
    interp n (SL.ownm r) = OwnM r.
  Proof.
    depdes H. subst. unfold SL.ownm, eq_rect_r. ss.
    rewrite @SRFRed.cur. ss.
    f_equal. unfold HRA.in_subG, HRA.embed. ss.
    erewrite (UIP _ _ _ _). reflexivity.
  Qed.

  Lemma pure n P :
    interp n (SL.pure P) = ⌜P⌝%I.
  Proof. unfold SL.pure. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma and n p q :
    interp n (SL.and p q) = (interp n p ∧ interp n q)%I.
  Proof. unfold SL.and. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma or n p q :
    interp n (SL.or p q) = (interp n p ∨ interp n q)%I.
  Proof. unfold SL.or. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma impl n p q :
    interp n (SL.impl p q) = (interp n p → interp n q)%I.
  Proof. unfold SL.impl. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma univ `{T:PF.t} `{@GPF.inG T τ} n (ty: T.(PF.shp)) p :
    SRFSem.t n (SL.univ ty p) = (∀ x: (T.(PF.deg) ty (SRFSyn.t_prev n)), SRFSem.t n (p x))%I.
  Proof.
    destruct H eqn : EQ. subst.
    unfold SL.univ, eq_rect_r. ss.
    rewrite @SRFRed.cur. reflexivity.
  Qed.

  Lemma ex `{@GPF.inG T τ} n ty p :
    interp n (SL.ex ty p) = (∃ x, interp n (p x))%I.
  Proof.
    destruct H eqn : EQ. subst.
    unfold SL.ex, eq_rect_r. ss.
    rewrite @SRFRed.cur. reflexivity.
  Qed.

  Lemma empty n :
    interp n SL.empty = emp%I.
  Proof. unfold SL.empty. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma sepconj n p q :
    interp n (SL.sepconj p q) = (interp n p ∗ interp n q)%I.
  Proof. unfold SL.sepconj. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma wand n p q :
    interp n (SL.wand p q) = (interp n p -∗ interp n q)%I.
  Proof. unfold SL.wand. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma persistently n p :
    interp n (SL.persistently p) = (<pers> interp n p)%I.
  Proof. unfold SL.persistently. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma plainly n p :
    interp n (SL.plainly p) = (■ (interp n p))%I.
  Proof. unfold SL.plainly. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma upd n p :
    interp n (SL.upd p) = (|==> interp n p)%I.
  Proof. unfold SL.upd. rewrite @SRFRed.cur. reflexivity. Qed.

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

Global Opaque SL.ownm.
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

Global Opaque SRFSem.t.

(* Simple sProp reduction tactics. *)
Ltac SL_red := repeat (try rewrite ! @SLRed.sepconj;
                      try rewrite ! @SLRed.and;
                      try rewrite ! @SLRed.or;
                      try rewrite ! @SLRed.impl;
                      try rewrite ! @SLRed.wand;
                      try rewrite ! @SLRed.pure;
                      try rewrite ! @SLRed.univ;
                      try rewrite ! @SLRed.ex;
                      try rewrite ! @SLRed.empty;
                      try rewrite ! @SLRed.persistently;
                      try rewrite ! @SLRed.plainly;
                      try rewrite ! @SLRed.upd;
                      try rewrite ! @SLRed.affinely;
                      try rewrite ! @SLRed.intuitionistically;
                      try rewrite ! @SLRed.sepM;
                      try rewrite ! @SLRed.sepS;
                      try rewrite ! @SLRed.sepL1
                      ).

Ltac SL_red_all := repeat (try rewrite ! @SLRed.sepconj in *;
                          try rewrite ! @SLRed.and in *;
                          try rewrite ! @SLRed.or in *;
                          try rewrite ! @SLRed.impl in *;
                          try rewrite ! @SLRed.wand in *;
                          try rewrite ! @SLRed.pure in *;
                          try rewrite ! @SLRed.univ in *;
                          try rewrite ! @SLRed.ex in *;
                          try rewrite ! @SLRed.empty in *;
                          try rewrite ! @SLRed.persistently in *;
                          try rewrite ! @SLRed.plainly in *;
                          try rewrite ! @SLRed.upd in *;
                          try rewrite ! @SLRed.affinely in *;
                          try rewrite ! @SLRed.intuitionistically in *;
                          try rewrite ! @SLRed.sepM in *;
                          try rewrite ! @SLRed.sepS in *;
                          try rewrite ! @SLRed.sepL1 in *
                          ).

Ltac SL_red_ownm := try rewrite ! @SLRed.ownm.
Ltac SL_red_ownm_all := try rewrite ! @SLRed.ownm in *.
(** * Global resource algebras *)
(** GRA is a structure that corresponds to gFunctors in iris, but with a
requirement that every resource algebras contained in it should be discrete
since CRIS is a framework with no step-indexing. Refer to explanation of
resource management of iris for further information. *)
From iris.algebra Require Import cmra updates functions gmap_view.
Require Import sflib.
Require Import base_logic.
Require Import allocs.

(** * Discrete resource algebras (internal use only) *)
Record DRA := DRA_mk {
  DRA_RA :> cmra;
  DRA_discrete : CmraDiscrete DRA_RA
}.
Global Arguments DRA_mk _ {_}.
Global Existing Instance DRA_discrete.

Class GRA := GRA_mk {
  GRA_len : nat;
  GRA_lookup : fin GRA_len → DRA;
}.

Definition gname := positive.
Canonical Structure gnameO := leibnizO gname.

Definition base_γ : gname := 1%positive.

Definition gid (Σ : GRA) := fin GRA_len.

Definition GRAUR (Σ : GRA) : ucmra := discrete_funUR (λ i, allocsUR positive (GRA_lookup i)).
Global Coercion GRAUR : GRA >-> ucmra.

Definition initial {Σ : GRA} : GRAUR Σ :=
  (λ i, allocs_auth (@GRA_lookup Σ i) (λ _, True)).
Lemma initial_valid {Σ : GRA} : ✓ initial.
Proof. rewrite /initial /allocs_auth; intros i g; des_ifs. Qed.

Global Instance GRA_discrete {Σ : GRA} : CmraDiscrete Σ.
Proof. apply _. Qed.

(** * Typeclass for individual cmras being included in GRAs *)
Class inG (RA : cmra) (Σ : GRA) := inG_mk {
  inG_id : gid Σ;
  inG_prf : RA = GRA_lookup inG_id
}.
Global Arguments inG_id {_ _} _.
Global Hint Mode inG ! - : typeclass_instances.

Module GRAs.
  Definition nil : GRA := GRA_mk 0 (fin_0_inv _).

  Definition singleton (A : DRA) : GRA :=
    GRA_mk 1 (fin_S_inv (λ _, DRA) A (fin_0_inv _)).

  Program Definition app (Σ1 Σ2 : GRA) : GRA :=
    GRA_mk (@GRA_len Σ1 + @GRA_len Σ2) (fin_add_inv _ (@GRA_lookup Σ1) (@GRA_lookup Σ2)).
End GRAs.
Global Coercion GRAs.singleton : DRA >-> GRA.
Notation "#[ ]" := GRAs.nil (format "#[ ]").
(* TODO : Reversible coercions do not work - find a way *)
Notation "#[ Σ1 ; .. ; Σn ]" := (GRAs.app (DRA_mk Σ1) .. (GRAs.app (DRA_mk Σn) GRAs.nil) ..).
Notation "##[ Σ1 ; .. ; Σn ]" := (GRAs.app Σ1 .. (GRAs.app Σn GRAs.nil) ..).

(** * GRA being included in another GRA *)
Class subG (Σ1 Σ2 : GRA) := subG_in i :
  { j | @GRA_lookup Σ1 i = @GRA_lookup Σ2 j }.
Global Hint Mode subG ! + : typeclass_instances.

(* Hint Database for resolving GRA indices - add subG_RAG & RA_inG typeclasses here *)
Create HintDb GRA_index.
Lemma subG_inv Σ1 Σ2 Σ : subG (GRAs.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  - move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=; rewrite fin_add_inv_l; eauto.
  - move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=; rewrite fin_add_inv_r; eauto.
Defined.
Hint Unfold subG_inv : GRA_index.

Global Instance subG_refl Σ : subG Σ Σ.
Proof. move=> i; by exists i. Defined.
Hint Unfold subG_refl : GRA_index.

Global Instance subG_app_l Σ Σ1 Σ2 : subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.L _ j). by rewrite /= fin_add_inv_l.
Defined.
Lemma subG_app_l_inG_id Σ Σ1 Σ2 subGins i :
    (subG_app_l Σ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.L _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_l (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
Proof. unfold subG_app_l. destruct (subGins i). reflexivity. Qed.

Global Instance subG_app_r Σ Σ1 Σ2 : subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.R _ j). by rewrite /= fin_add_inv_r.
Defined.
Lemma subG_app_r_inG_id Σ Σ1 Σ2 subGins i :
    (subG_app_r Σ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.R _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_r (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
Proof. unfold subG_app_r. destruct (subGins i). reflexivity. Qed.

Lemma subG_inG Σ (A : DRA) : subG A Σ → inG A Σ.
Proof.
  intros H; destruct (H 0%fin). exists x. rewrite -e. econstructor.
Defined.
Lemma inG_id_subG_inG Γ (RA : DRA) inΓ :
  inG_id (subG_inG Γ RA inΓ) = let '(exist _ id _) := inΓ 0%fin in id.
Proof. unfold subG_inG. destruct (inΓ 0%fin). simpl. done. Qed.

(** This tactic solves the usual obligations "subG ? Σ → {in,?}G ? Σ" *)
Ltac solve_inG :=
  (* Get all assumptions *)
  intros;
  (* Unfold the top-level xΣ. We need to support this to be a function. *)
  lazymatch goal with
  | H : subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _) _ |- _ => try unfold xΣ in H
  | H : subG ?xΣ _ |- _ => try unfold xΣ in H
  end;
  (* Take apart subG for non-"atomic" lists *)
  (hrepeat do 1 match goal with
         | H : subG (GRAs.app _ _) _ |- _ => apply subG_inv in H; destruct H
         end);
  (* Try to turn singleton subG into inG; but also keep the subG for typeclass
     resolution -- to keep them, we put them onto the goal. *)
  (hrepeat do 1 match goal with
         | H : subG _ _ |- _ => move:(H); (apply subG_inG in H || clear H)
         end);
  (* Again get all assumptions and simplify the functors *)
  intros; simpl in *;
  (* We support two kinds of goals: Things convertible to inG;
     and records with inG and typeclass fields. Try to solve the
     first case. *)
  try assumption;
  (* That didn't work, now we're in for the second case. *)
  split; (assumption || by apply _).

(* iProps are parameterized on GRAs, without step-indexing *)
Notation iProp Σ := (uPredI Σ).

(* Require Import ucmra_list.
Class GRAL := GRAL_mk {
  l : cmra_list
}.
Local Coercion l : GRAL >-> cmra_list.

Definition GRALUR (Σ : GRAL) : ucmra :=
  discrete_funUR (λ i, allocsUR positive (UList.nth i Σ Empty_set)).
Global Coercion GRALUR : GRAL >-> ucmra.

Global Instance GRAL_discrete {Σ : GRAL} : CmraDiscrete Σ.
Proof.
  rewrite /GRALUR. apply discrete_funR_cmra_discrete. destruct Σ. induction l0; ss.
  { intros i; des_ifs; apply _. }
  { intros i; des_ifs; apply _. }
Qed.

Definition InitRes {Σ : GRA} : Type := (ucmra * )

Class A (Γ : HRA) := { inG RA Γ; }.
Definition initial_resource : InitRes := a. *)
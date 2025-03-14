From iris.algebra Require Import cmra updates functions gmap_view.
Require Import sflib.
Require Import base_logic.
Require Import allocs.

Record DRA := DRA_mk {
  DRA_RA :> cmra;
  DRA_res : option DRA_RA;
  DRA_discrete : CmraDiscrete DRA_RA
}.
Global Arguments DRA_mk _ _ {_}.
Global Existing Instance DRA_discrete.

Class GRA := GRA_mk {
  GRA_len : nat;
  GRA_lookup : fin GRA_len → DRA;
}.

Definition gname := positive.
Canonical Structure gnameO := leibnizO gname.

Definition base_γ : gname := 1%positive.

Definition gid (Σ : GRA) := fin GRA_len.

Definition GRAUR (Σ : GRA) : ucmra :=
  discrete_funUR (λ i, allocsUR positive (GRA_lookup i)).
Global Coercion GRAUR : GRA >-> ucmra.

Class inG (RA : cmra) (Σ : GRA) := inG_mk {
  inG_id : gid Σ;
  inG_prf : RA = GRA_lookup inG_id;
}.
Global Arguments inG_id {_ _} _.
Global Hint Mode inG ! - : typeclass_instances.

Module GRAs.
  Definition nil : GRA := GRA_mk 0 (fin_0_inv _).

  Definition singleton (sig : DRA) : GRA :=
    GRA_mk 1 (fin_S_inv (λ _, DRA) sig (fin_0_inv _)).

  Program Definition app (Σ1 Σ2 : GRA) : GRA :=
    GRA_mk (@GRA_len Σ1 + @GRA_len Σ2) (fin_add_inv _ (@GRA_lookup Σ1) (@GRA_lookup Σ2)).
End GRAs.
Coercion GRAs.singleton : DRA >-> GRA.

Notation "#[ ]" := GRAs.nil (format "#[ ]").
Notation "#[ Σ1 ; .. ; Σn ]" := (GRAs.app Σ1 .. (GRAs.app Σn GRAs.nil) ..).

(* Debug #0 *)
(* Section test.
  Context `{A : cmra, a : A, CmraDiscrete A}.
  Context `{B : cmra, b : B, CmraDiscrete B}.
  Context `{C : cmra, CmraDiscrete C}.

  Let test := #[DRA_mk A (Some a); DRA_mk B (Some b); DRA_mk C None].
End test. *)

Class subG (Σ1 Σ2 : GRA) := subG_in i :
  { j | @GRA_lookup Σ1 i = @GRA_lookup Σ2 j }.
Global Hint Mode subG ! + : typeclass_instances.

Lemma subG_inv Σ1 Σ2 Σ : subG (GRAs.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  { move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=; rewrite fin_add_inv_l; eauto. }
  { move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=; rewrite fin_add_inv_r; eauto. }
Qed.

Lemma subG_inG Σ (A : DRA) : subG A Σ → inG (DRA_RA A) Σ.
Proof.
  intros H; destruct (H 0%fin). exists x. rewrite -e. econstructor.
Qed.

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

Global Instance subG_refl Σ : subG Σ Σ.
Proof. move=> i; by exists i. Qed.

Global Instance subG_app_l Σ Σ1 Σ2 : subG Σ Σ1 → subG Σ (GRAs.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.L _ j). by rewrite /= fin_add_inv_l.
Qed.

Global Instance subG_app_r Σ Σ1 Σ2 : subG Σ Σ2 → subG Σ (GRAs.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.R _ j). by rewrite /= fin_add_inv_r.
Qed.

Notation iProp Σ := (uPredI Σ).

(* Debug #1 *)
(* From iris Require Import excl auth numbers.

Class AGΣ (Σ : GRA) := {
  #[local] A_inG :: inG (exclR unitO) Σ;
}.
Definition AΣ : GRA := #[DRA_mk (exclR unitO) None].
Global Instance subG_AGΣ {Σ : GRA} : subG AΣ Σ → AGΣ Σ.
Proof. solve_inG. Qed.

Section a.
  Context `{!AGΣ Σ}.
  Definition a : inG (exclR unitO) Σ. Proof. apply _. Defined.
End a.

Class BGΣ (Σ : GRA) := {
  #[local] B_inG :: inG (authUR (optionUR (exclR unitO))) Σ;
}.
Definition BΣ : GRA := #[DRA_mk (authUR (optionUR (exclR unitO))) (Some (● (Excl' ())))].
Global Instance subG_BGΣ {Σ : GRA} : subG BΣ Σ → BGΣ Σ.
Proof. solve_inG. Qed.

Section b.
  Context `{!BGΣ Σ}.
  Definition b : inG (authUR (optionUR (exclR unitO))) Σ. Proof. apply _. Defined.
End b.

Class CGΣ (Σ : GRA) := {
  #[local] C_inG :: inG (ZR) Σ;
}.
Definition CΣ : GRA := #[DRA_mk (ZR) (Some 1%Z)].
Global Instance subG_CGΣ {Σ : GRA} : subG CΣ Σ → CGΣ Σ.
Proof. solve_inG. Qed. *)

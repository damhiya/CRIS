(** * Global resource algebras *)
(** GRA is a structure that corresponds to gFunctors in iris, but with a
requirement that every resource algebras contained in it should be discrete
since CRIS is a framework with no step-indexing. Refer to explanation of
resource management of iris for further information. *)
From iris.algebra Require Import cmra updates functions gmap_view.
From CRIS.base_logic Require Export base_logic.
From CRIS.lib Require Import allocs.

(** * Discrete unital resource algebras (internal use only) *)
Record DRA := DRA_mk {
  DRA_RA :> ucmra;
  DRA_discrete : CmraDiscrete DRA_RA
}.
Global Arguments DRA_mk _ {_}.
Global Existing Instance DRA_discrete.

Record GRA := GRA_mk {
  GRA_len : nat;
  GRA_lookup : fin GRA_len → DRA;
}.

Definition gname := positive.
Canonical Structure gnameO := leibnizO gname.

Definition gid (Σ : GRA) := fin (GRA_len Σ).

Definition GRAUR (Σ : GRA) : ucmra :=
  discrete_funUR (λ i, gmapUR gname (allocsUR (GRA_lookup Σ i))).
Global Coercion GRAUR : GRA >-> ucmra.

Global Instance GRA_discrete {Σ : GRA} : CmraDiscrete Σ.
Proof. apply _. Qed.

(** * Typeclass for individual ucmras being included in GRAs *)
Class inG (RA : ucmra) (Σ : GRA) := inG_mk {
  inG_id : gid Σ;
  inG_prf : RA = GRA_lookup Σ inG_id
}.
Global Arguments inG_id {_ _} _.
Global Hint Mode inG ! - : typeclass_instances.

Module GRAs.
  Definition nil : GRA := GRA_mk 0 (fin_0_inv _).

  Definition singleton (RA : ucmra) `{CmraDiscrete RA} : GRA :=
    GRA_mk 1 (fin_S_inv (λ _, DRA) (DRA_mk RA) (fin_0_inv _)).

  Program Definition app (Σ1 Σ2 : GRA) : GRA :=
    GRA_mk (GRA_len Σ1 + GRA_len Σ2) (fin_add_inv _ (GRA_lookup Σ1) (GRA_lookup Σ2)).
End GRAs.
Notation "#[ ]" := GRAs.nil (format "#[ ]").
Notation "#[ Σ1 ; .. ; Σn ]" := (GRAs.app Σ1 .. (GRAs.app Σn GRAs.nil) ..).

(** * GRA being included in another GRA *)
Class subG (Σ1 Σ2 : GRA) := in_subG i :
  { j | GRA_lookup Σ1 i = GRA_lookup Σ2 j }.

Global Hint Mode subG ! + : typeclass_instances.

Lemma subG_inv Σ1 Σ2 Σ : subG (GRAs.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  - move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=; rewrite fin_add_inv_l; eauto.
  - move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=; rewrite fin_add_inv_r; eauto.
Qed.

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

(* iProps are parameterized on GRAs, without step-indexing *)
Section iProp.
  Context {Σ : GRA}.
  Definition iProp := uPredI Σ.
End iProp.
Global Arguments iProp {_}.


  (* Program Definition of_list (RAs : ucmra_list) : t :=
    {| gra_map := λ n, (UList.nth n RAs (optionUR Empty_setR)) |}.
  Next Obligation. induction RAs; destruct i; apply _. Qed.

  Definition to_URA (Σ : t) : ucmra := discrete_funUR Σ.
  Coercion to_URA : t >-> ucmra.



  Global Instance inG_cmra_discrete `{!inG A Σ} : CmraDiscrete A.
  Proof. erewrite inG_prf. apply _. Qed.

  (* a : cmra_car =ty= RAs inG_id =ty= RAs n *)
  Definition embed `{!inG A Σ} (a : A) : Σ :=
    discrete_fun_singleton inG_id (cmra_transport (f_equal _ inG_prf) a).
  Local Instance : Params (@embed) 3 := {}. *)

(* Section lemmas.
  Context `{!inG A Σ}.
  Implicit Types a : A.

  Lemma embed_wf
        a
        (WF : ✓ embed a)
    :
      <<WF : ✓ a>>
  .
  Proof. by rewrite /embed discrete_fun_singleton_valid cmra_transport_valid in WF. Qed.

  Lemma wf_embed
        a
        (WF : ✓ a)
    :
      <<WF : ✓ embed a >>
  .
  Proof. by rewrite /NW /embed discrete_fun_singleton_valid cmra_transport_valid. Qed.

  Global Instance embed_ne : NonExpansive (@embed A Σ _).
  Proof. by intros ????; apply discrete_fun_singleton_ne, cmra_transport_ne. Qed.
  Global Instance embed_proper : Proper ((≡) ==> (≡)) (@embed A Σ _) := ne_proper _.

  Lemma embed_add
        a0 a1
    :
      embed a0 ⋅ embed a1 ≡ embed (a0 ⋅ a1)
    .
  Proof. by rewrite /embed discrete_fun_singleton_op cmra_transport_op. Qed.

  Lemma embed_updatable_set
        a P
        (UPD : a ~~>: P)
    :
      <<UPD : embed a ~~>: λ b, ∃ a', b = embed a' ∧ P a' >>
  .
  Proof.
    eapply discrete_fun_singleton_updateP.
    { eapply cmra_transport_updateP', UPD. }
    ii. ss. des. subst. eauto.
  Qed.

  Lemma embed_updatable
        a0 a1
        (UPD : a0 ~~> a1)
    :
      <<UPD : embed a0 ~~> embed a1 >>
  .
  Proof.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    - apply embed_updatable_set, cmra_update_updateP, UPD.
    - ii. ss. des. subst. done.
  Qed.

  Lemma embed_core a : embed (core a) ≡ core (embed a).
  Proof. by rewrite /embed discrete_fun_singleton_core cmra_transport_core. Qed.

  (* Note : NOT a general lemma for [cmra_transport]. Tailed for the proof pattern
    of [GRA]. I.e., upstreaming this to iris doesn't make sense. *)
  Local Lemma cmra_transport_unit {B C : ucmra} (H : B = C) : cmra_transport (f_equal _ H) ε = ε.
  Proof. by destruct H. Qed.
  Lemma embed_unit : embed ε ≡ ε.
  Proof. by rewrite /embed cmra_transport_unit discrete_fun_singleton_unit. Qed.

End lemmas.
End GRA.
Coercion GRA.to_URA : GRA.t >-> ucmra.

Global Opaque GRA.to_URA. *)

(* A resource algebra for pointwise lifting.
Designed as a workaround for CRIS's weak-update problems by reserving every indices upfront. *)
From iris.algebra Require Import functions csum excl updates big_op.
From iris.algebra Require Import stepindex_finite.
From stdpp Require Import coPset.
Require Import sflib.

Definition allocsUR (K : Type) (A : cmra) : ucmra :=
  K -d> optionUR (csumR (exclR unitO) A).
Lemma allocsUR_lookup_op {K A} (f g : allocsUR K A) x : (f ⋅ g) x = f x ⋅ g x.
Proof. rewrite discrete_fun_lookup_op //. Qed.

(* TODO : SEAL *)
Definition allocs_auth {K} (A : cmra) (P : K → Prop) `{∀ k, Decision (P k)} : allocsUR K A :=
  λ k, if decide (P k) then Some (Cinl (Excl tt)) else None.
Definition allocs_frag `{EqDecision K} {A} k a : allocsUR K A :=
  discrete_fun_singleton k (Some (Cinr a)).
Global Instance: Params (@allocs_frag) 4 := {}.
Global Arguments allocs_frag {_ _ _} k a.

Section allocs.
  Context `{!CmraDiscrete A} `{EqDecision K}.
  Local Notation allocs_auth := (@allocs_auth K A).
  Implicit Types a b : A.
  Implicit Types γ : K.

  Global Instance allocs_frag_ne γ : NonExpansive (@allocs_frag _ _ A γ).
  Proof using. intros n x y eq. apply discrete_fun_singleton_ne. f_equiv. solve_proper. Qed.
  Global Instance allocs_frag_proper γ : Proper ((≡) ==> (≡)) (@allocs_frag _ _ A γ) := ne_proper _.

  (** Operation *)
  Lemma allocs_frag_op γ a b : allocs_frag γ a ⋅ allocs_frag γ b ≡ allocs_frag γ (a ⋅ b).
  Proof using. by rewrite discrete_fun_singleton_op -Some_op -Cinr_op. Qed.

  (** Validity *)
  Lemma allocs_auth_valid P `{∀ k, Decision (P k)} : ✓ allocs_auth P.
  Proof. rewrite /allocs_auth; intros k; des_ifs. Qed.

  Lemma allocs_frag_valid γ a : ✓ allocs_frag γ a ↔ ✓ a.
  Proof. by rewrite discrete_fun_singleton_valid Some_valid Cinr_valid. Qed.

  Lemma allocs_both_valid `{∀ k, Decision (P k)} γ a :
    ✓ (allocs_auth P ⋅ allocs_frag γ a) →
    ¬ P γ ∧ ✓ a.
  Proof.
    rewrite /allocs_auth /allocs_frag.
    intros Hv; specialize (Hv γ);
      rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton in Hv.
    by des_ifs; ss.
  Qed.
    
  (** Frame-preserving updates *)
  Lemma allocs_frag_update γ a b (UPD : a ~~> b) : allocs_frag γ a ~~> allocs_frag γ b.
  Proof using. by apply discrete_fun_singleton_update, option_update, csum_update_r. Qed.

  Lemma allocs_alloc a (P Q : K → Prop) γ (WF : ✓ a) `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)}
      (IMPL : ∀ k, Q k → P k)
      (DISJ : P γ ∧ ~ Q γ) :
    allocs_auth P ~~> allocs_auth Q ⋅ allocs_frag γ a.
  Proof using.
    eapply discrete_fun_update; intros k; rewrite /allocs_auth /allocs_frag discrete_fun_lookup_op.
    des_ifs; rewrite ?left_id.
    { destruct (decide (γ = k)); clarify; des; ss. rewrite discrete_fun_lookup_singleton_ne; ss. }
    { destruct (decide (γ = k)); clarify;
        [rewrite discrete_fun_lookup_singleton|rewrite discrete_fun_lookup_singleton_ne]; ss.
      { apply option_update, cmra_update_exclusive; ss. }
      { eapply cmra_update_included; ss. }
    }
    { naive_solver. }
    { destruct (decide (γ = k)); clarify; des; ss. rewrite discrete_fun_lookup_singleton_ne; ss. }
  Qed.

  Lemma allocs_auth_split (P Q R : K → Prop)
      `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)} `{∀ k, Decision (R k)}
      (DISJ : ∀ k, ~ (Q k ∧ R k))
      (IMPL : ∀ k, Q k ∨ R k → P k) :
    allocs_auth P ~~> allocs_auth Q ⋅ allocs_auth R.
  Proof.
    apply discrete_fun_update; intros p; rewrite discrete_fun_lookup_op ?/allocs_auth /allocs_frag.
    des_ifs; try (exfalso; eapply DISJ; eauto; fail).
    { rewrite right_id cmra_discrete_total_update; intros [z|]; ss; rewrite left_id -Some_op.
      intros ?%exclusive_l; ss; apply Cinl_exclusive; ss.
    }
    { hexploit IMPL; eauto; i; ss. }
    { hexploit IMPL; eauto; i; ss. }
  Qed.

  Lemma allocs_auth_split_2 (P Q R : K → Prop)
      `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)} `{∀ k, Decision (R k)} :
    (∀ k, P k ↔ Q k ∨ R k) →
    (∀ k, ¬ (Q k ∧ R k)) →
    allocs_auth P ≡ allocs_auth Q ⋅ allocs_auth R.
  Proof.
    intros Hiff Hdisj; rewrite /allocs_auth => i.
    by rewrite discrete_fun_lookup_op; des_ifs; naive_solver.
  Qed.

  Lemma allocs_auth_split_2_L (P Q R : K → Prop)
      `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)} `{∀ k, Decision (R k)} :
    (∀ k, P k ↔ Q k ∨ R k) →
    (∀ k, ¬ (Q k ∧ R k)) →
    allocs_auth P = allocs_auth Q ⋅ allocs_auth R.
  Proof.
    intros Hiff Hdisj; rewrite /allocs_auth; extensionalities i.
    by rewrite discrete_fun_lookup_op; des_ifs; naive_solver.
  Qed.
End allocs.
From iris.algebra Require Import functions csum excl updates.
Require Import sflib.

Definition allocsR (A : cmra) : cmra :=
  positive -d> optionUR (csumR (exclR unitO) A).
Definition allocsUR (A : cmra) : ucmra :=
  positive -d> optionUR (csumR (exclR unitO) A).

Definition allocs_auth (A : cmra) (P : positive → Prop) `{∀ p, Decision (P p)} : allocsR A :=
  λ γ, if decide (P γ) then Some (Cinl (Excl tt)) else None.
Definition allocs_frag {A : cmra} γ a : allocsR A :=
  discrete_fun_singleton γ (Some (Cinr a)).
Global Instance: Params (@allocs_frag) 4 := {}.
Global Arguments allocs_auth A P {_}.

Section allocs.
  Context `{CmraDiscrete A}.
  Implicit Types a b : A.
  Implicit Types γ : positive.

  Global Instance allocs_frag_ne γ : NonExpansive (@allocs_frag A γ).
  Proof. intros n x y eq. apply discrete_fun_singleton_ne. f_equiv. solve_proper. Qed.
  Global Instance allocs_frag_proper γ : Proper ((≡) ==> (≡)) (@allocs_frag A γ) := ne_proper _.

  (** Operation *)
  Lemma allocs_frag_op γ a b : allocs_frag γ a ⋅ allocs_frag γ b ≡ allocs_frag γ (a ⋅ b).
  Proof. by rewrite discrete_fun_singleton_op -Some_op -Cinr_op. Qed.

  (** Validity *)
  Lemma allocs_frag_valid γ a : ✓ allocs_frag γ a ↔ ✓ a.
  Proof. by rewrite discrete_fun_singleton_valid Some_valid Cinr_valid. Qed.

  (** Frame-preserving updates *)
  (* TODO : This can be further generalized to yielding list of resources. *)
  Lemma allocs_alloc a `{∀ p, Decision (P p)} `{∀ p, Decision (Q p)}
      (WF : ✓ a) (EX : ∃ γ, P γ ∧ ~ Q γ) (INCL : ∀ γ, Q γ → P γ) :
    ∃ γ, allocs_auth A P ~~> allocs_auth A Q ⋅ allocs_frag γ a.
  Proof.
    destruct EX as [γ [HP HNQ]]; exists γ.
    apply discrete_fun_update; intros p; rewrite discrete_fun_lookup_op ?/allocs_auth /allocs_frag.
    des_ifs.
    { rewrite discrete_fun_lookup_singleton_ne; ss. ii; clarify; ss. }
    { rewrite left_id.
      destruct (decide (γ = p)); clarify;
        [rewrite discrete_fun_lookup_singleton | rewrite discrete_fun_lookup_singleton_ne]; ss.
      { apply option_update, cmra_update_exclusive; ss. }
      { rewrite cmra_discrete_total_update.
        intros [z|]; ss; rewrite left_id -Some_op; intros CONT%exclusive_l; ss.
        apply Cinl_exclusive; ss.
      }
    }
    { naive_solver. }
    { destruct (decide (γ = p)); clarify.
      rewrite discrete_fun_lookup_singleton_ne; ss.
    }
  Qed.
End allocs.
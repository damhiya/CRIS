From iris.algebra Require Import functions csum excl updates.
Require Import sflib.

Definition allocsR (A : cmra) : cmra :=
  positive -d> optionUR (csumR (exclR unitO) A).
Definition allocsUR (A : cmra) : ucmra :=
  positive -d> optionUR (csumR (exclR unitO) A).

Definition allocs_auth (A : cmra) (u : positive) : allocsR A :=
  λ γ, if decide (γ < u)%positive then None else Some (Cinl (Excl tt)).
Definition allocs_frag {A : cmra} γ a : allocsR A :=
  discrete_fun_singleton γ (Some (Cinr a)).
Global Instance: Params (@allocs_frag) 4 := {}.

Section allocs.
  Context {A : cmra}.
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
  Lemma allocs_alloc u a (WF : ✓ a) : allocs_auth A u ~~> allocs_auth A (u + 1) ⋅ allocs_frag u a.
  Proof.
    apply discrete_fun_update; intros p; rewrite discrete_fun_lookup_op ?/allocs_auth /allocs_frag.
    destruct (decide (p < u))%positive.
    { rewrite discrete_fun_lookup_singleton_ne; des_ifs; lia. }
    { des_ifs; rewrite ?left_id.
      { assert (u = p) by lia; subst; rewrite discrete_fun_lookup_singleton.
        by apply option_update, cmra_update_exclusive.
      }
      { rewrite discrete_fun_lookup_singleton_ne; try lia; ss. }
    }
  Qed.
End allocs.
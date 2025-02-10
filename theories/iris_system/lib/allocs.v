(* A resource algebra for pointwise lifting.
Designed as a workaround for CRIS's weak-update problems by reserving every indices upfront. *)
From iris.algebra Require Import functions csum excl updates big_op.
From stdpp Require Import coPset.
Require Import sflib.

Definition allocsUR (A : cmra) : ucmra :=
  positive -d> optionUR (csumR (exclR unitO) A).

(* TODO : SEAL *)
Definition allocs_auth (A : cmra) (X : coPset) : allocsUR A :=
  λ γ, if decide (γ ∈ X) then Some (Cinl (Excl tt)) else None.
Definition allocs_frag {A : cmra} γ a : allocsUR A :=
  discrete_fun_singleton γ (Some (Cinr a)).
Global Instance: Params (@allocs_frag) 4 := {}.
Global Arguments allocs_frag {_} γ a.

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
  Lemma allocs_frag_update γ a b (UPD : a ~~> b) : allocs_frag γ a ~~> allocs_frag γ b.
  Proof. by apply discrete_fun_singleton_update, option_update, csum_update_r. Qed.
  (* TODO : This can be further generalized to yielding a set of resources.
  Refactor when required. *)
  Lemma allocs_alloc a (X : coPset) (γ : positive) (IN : γ ∈ X) (WF : ✓ a) :
    allocs_auth A X ~~> allocs_auth A (X ∖ {[γ]}) ⋅ allocs_frag γ a.
  Proof.
    apply discrete_fun_update; intros p; rewrite discrete_fun_lookup_op ?/allocs_auth /allocs_frag.
    des_ifs.
    { rewrite discrete_fun_lookup_singleton_ne; ss. set_solver. }
    { rewrite left_id.
      destruct (decide (γ = p)); clarify;
        [rewrite discrete_fun_lookup_singleton | rewrite discrete_fun_lookup_singleton_ne]; ss.
      { apply option_update, cmra_update_exclusive; ss. }
      { rewrite cmra_discrete_total_update.
        intros [z|]; ss; rewrite left_id -Some_op; intros CONT%exclusive_l; ss.
        apply Cinl_exclusive; ss.
      }
    }
    { set_solver. }
    { destruct (decide (γ = p)); clarify.
      rewrite discrete_fun_lookup_singleton_ne; ss.
    }
  Qed.

  Lemma allocs_auth_split (X Y Z : coPset) (DISJ : X ∩ Y = ∅) (EQ : Z = X ∪ Y) :
    allocs_auth A Z ≡ allocs_auth A X ⋅ allocs_auth A Y.
  Proof.
    rewrite EQ => x; rewrite discrete_fun_lookup_op /allocs_auth; des_ifs; try set_solver.
  Qed.
End allocs.
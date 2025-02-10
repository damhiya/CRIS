(* TODO : remove this file *)
From iris.algebra Require Export functions.
Require Import sflib.

Section cmra.
  Context {A : Type} `{Heqdec : !EqDecision A} {B : A → ucmra}.
  Implicit Types x y : A.
  Implicit Types f g h : discrete_funUR B.

  Lemma discrete_fun_delete i f :
    f ≡ (((λ x, if (decide (x = i)) then ε else (f x)) : discrete_funUR B)
        ⋅ (discrete_fun_singleton i (f i)) : discrete_funUR B).
  Proof.
    intros x; rewrite discrete_fun_lookup_op; des_ifs; first by rewrite discrete_fun_lookup_singleton left_id.
    rewrite discrete_fun_lookup_singleton_ne; first by rewrite (comm op) left_id.
    ii; clarify.
  Qed.
End cmra.
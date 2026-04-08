From Stdlib Require Import ClassicalFacts FunctionalExtensionality ChoiceFacts IndefiniteDescription ProofIrrelevance.

Lemma func_ext_dep {A} {B : A -> Type} (f g : forall x, B x) : (forall x, f x = g x) -> f = g.
Proof.
  apply @FunctionalExtensionality.functional_extensionality_dep.
Qed.

Lemma func_ext {A B} (f g : A -> B) : (forall x, f x = g x) -> f = g.
Proof.
  apply func_ext_dep.
Qed.

Lemma dependent_functional_choice {A : Type} (B : A -> Type) :
  forall R : forall x : A, B x -> Prop,
    (forall x : A, exists y : B x, R x y) ->
    (exists f : (forall x : A, B x), forall x : A, R x (f x)).
Proof.
  eapply ChoiceFacts.non_dep_dep_functional_choice.
  clear. exact IndefiniteDescription.functional_choice.
Qed.

Lemma proof_irr : ClassicalFacts.proof_irrelevance.
Proof.
  red. intros. apply ProofIrrelevance.proof_irrelevance.
Qed.
Arguments proof_irr [A].

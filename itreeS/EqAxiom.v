(** * Strong bisimulation is propositional equality *)

(** This is not provable but admissible as an axiom.

    This axiom is not used by this library, but only exported for
    convenience, as it can certainly simplify some developments.
 *)

(* begin hide *)
From ITreeS Require Import
     ITreeDefinition
     Eqit.

(* end hide *)

(** Strong bisimulation is propositional equality.
    The converse is reflexivity of strong bisimulation
    (and is provable without axioms). *)
Axiom bisim_is_eq :
  forall {E R} {t1 t2 : itree E R},
    t1 ≅ t2 -> t1 = t2.

Lemma eq_univ_up:
  forall (X Y : Type),
    @eq Type X Y -> @eq Type X Y.
Proof.
  intros. destruct H. reflexivity.
Qed.

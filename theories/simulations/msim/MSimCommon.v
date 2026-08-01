From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod.

Variant contextuality : Type := 
| open 
| closed.

Notation retr_type Σ Rs Rt :=
  (Rs → Rt → iProp Σ).
Notation msim_type Σ Rs Rt :=
  (bool → bool → itree crisE Rs → itree crisE Rt → Σ → Prop).

Section Ist.

  Context {Σ : GRA}.

  Open Scope bi_scope.

  Definition ist_with_eq {R} (Ist : iProp Σ) : retr_type Σ R R :=
    fun r_src r_tgt => ⌜ r_src = r_tgt ⌝ ∗ Ist.

End Ist.

Lemma submseteq_NoDup {A} (lt ls: list A):
  ls ⊆+ lt → NoDup lt → NoDup ls.
Proof.
  intros SUB. induction SUB; i; et.
  - depdes H. econs; et.
    ii. apply H. eauto using elem_of_submseteq.
  - depdes H. rewrite not_elem_of_cons in H. destruct H as [a_nin_y a_nin_l].
    depdes H0. econs.
    + rewrite not_elem_of_cons. et.
    + econs; et.
  - depdes H. et.
Qed.

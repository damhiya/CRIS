From stdpp Require Import strings countable gmap.
From CRIS.lib Require Import Coqlib.
From CRIS.common Require Import Events.

Variant fname : Type :=
| funid (fn : string)
| entry.

Notation "'fid' fs" := (funid (fs).1) (at level 10).

Global Instance fn_id_eq_dec : EqDecision fname.
Proof. solve_decision. Defined.
Global Instance fn_id_countable : Countable fname.
Proof.
  refine (inj_countable'
   (λ k, match k with funid f => Some f | entry => None end)
   (λ k,
    match k with
    | Some f => funid f
    | None => entry
    end) _).
   by intros [].
Defined.

Definition fname_to_option (f: fname): option string :=
  match f with
  | funid fn => Some fn
  | _ => None
  end.

Definition get_fids (fns: gset fname) : gset string :=
  set_omap fname_to_option fns.

Lemma maxlen_get_fids_union fns1 fns2:
  maxlen (elements (get_fids (fns1 ∪ fns2))) =
    max (maxlen (elements (get_fids fns1))) (maxlen (elements (get_fids fns2))).
Proof.
  unfold maxlen, get_fids. rewrite set_omap_union.
  eapply Nat.le_antisymm, Nat.max_lub;
    rewrite list_max_le, list_relations.Forall_forall;
    intros sz IN; eapply elem_of_list_fmap_2 in IN; des;
    rewrite elem_of_elements in IN0; subst.
  - rewrite elem_of_union in IN0; des.
    + rewrite <-Nat.le_max_l.
      eapply list_max_in, in_map, elem_of_list_In, elem_of_elements; et.
    + rewrite <-Nat.le_max_r.
      eapply list_max_in, in_map, elem_of_list_In, elem_of_elements; et.
  - eapply list_max_in, in_map, elem_of_list_In, elem_of_elements, elem_of_union; et.
  - eapply list_max_in, in_map, elem_of_list_In, elem_of_elements, elem_of_union; et.
Qed.

Require Export Common FSpec Fn.
From iris.proofmode Require Import proofmode.

(* Global Notation specmap := ((gmap fname fspec_rel) * bool)%type. *)
Definition specmap `{Σ: GRA} : Type := (gmap fname fspec_rel) * bool.

Variant fn_has_spec_in `{Σ : GRA} (sp : specmap) (f : string) (fsp : fspec) : Prop :=
| fn_has_spec_in_intro fsp2
    (SPEC: sp.1 !! funid f = fsp_some fsp2)
    (WEAK : ⊢ fspec_imply fsp2 fsp).
Hint Constructors fn_has_spec_in : core.

Definition gmap_to_specmap `{Σ: GRA} (m : gmap fname fspec_rel) : specmap := (m, false).
#[warnings="-uniform-inheritance"]
Coercion gmap_to_specmap : gmap >-> specmap.

Global Instance specmap_empty `{Σ: GRA} : Empty specmap := (∅, false).

Global Instance specmap_union `{Σ: GRA} : Union specmap :=
  λ sp sp', (sp.1 ∪ sp'.1, sp.2 || sp'.2).

Global Instance specmap_subseteq `{Σ: GRA} : SubsetEq specmap :=
  λ sp sp', sp.1 ⊆ sp'.1 ∧ (sp.2 → sp'.2).

Global Instance specmap_subseteq_reflexive `{Σ: GRA} : Reflexive (specmap_subseteq).
Proof. intros []. split; et. Qed.

Global Instance specmap_subseteq_transitive `{Σ: GRA} : Transitive (specmap_subseteq).
Proof. intros [] [] [] [] []. ss. split; et. etrans; et. Qed.

Require Import Common FSpec.
From iris.proofmode Require Import proofmode.

Variant speckey : Type :=
| speckey_fn (fn : string)
| speckey_entry
| speckey_concE.

Global Instance speckey_eq_dec : EqDecision speckey.
Proof. solve_decision. Qed.
Global Instance speckey_countable : Countable speckey.
Proof.
  refine (inj_countable'
   (λ k, match k with speckey_fn fn => Some (Some fn) | speckey_entry => Some None | _ => None end)
   (λ k,
    match k with
    | Some (Some fn) => speckey_fn fn
    | Some None => speckey_entry
    | _ => speckey_concE end) _).
   by intros [].
Qed.

Global Notation specmap := (gmap speckey fspec_rel).

Variant fn_has_spec_in `{Σ : GRA} (sp : specmap) (fn : string) (fsp : fspec) : Prop :=
| fn_has_spec_in_intro fsp2
    (SPEC: sp !! (speckey_fn fn) = fsp_some fsp2)
    (WEAK : ⊢ fspec_imply fsp2 fsp).
Hint Constructors fn_has_spec_in : core.
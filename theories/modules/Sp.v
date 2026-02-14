Require Export Common FSpec Fn.
From iris.proofmode Require Import proofmode.

Global Notation specmap := (gmap (option fname) fspec_rel).

Variant fn_has_spec_in `{Σ : GRA} (sp : specmap) (f : string) (fsp : fspec) : Prop :=
| fn_has_spec_in_intro fsp2
    (SPEC: sp !! Some (fid f) = fsp_some fsp2)
    (WEAK : ⊢ fspec_imply fsp2 fsp).
Hint Constructors fn_has_spec_in : core.
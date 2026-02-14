From stdpp Require Import strings countable.

Variant fname : Type :=
| fid (fn : string)
| entry.

Global Instance fn_id_eq_dec : EqDecision fname.
Proof. solve_decision. Defined.
Global Instance fn_id_countable : Countable fname.
Proof.
  refine (inj_countable'
   (λ k, match k with fid f => Some f | entry => None end)
   (λ k,
    match k with
    | Some f => fid f
    | None => entry
    end) _).
   by intros [].
Defined.

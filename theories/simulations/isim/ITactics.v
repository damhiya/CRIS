Require Import Common.

Require Import ISim.
Require Export ITacticsCore.

(***
 Module-level tactics
 ***)

Ltac unfold_hmod_fn :=
  s; match goal with
     | |-context[_ \/ False] => idtac
     | _ => unfold_hmod; unfold_hmod_fn
     end.

Ltac init_sim :=
  clear_trivials;
  first [eapply hmod_sim_reflR; [(hrepeat do 1 unfold_hmod); eauto|..] | econs];
  [i; s; (hrepeat do 1 unfold_hmod); s
  |eauto
  |try prove_sub_perm
  |try prove_sub_perm
  |unfold_hmod_fn; i; des; subst; ss].

Require Import Common.

Require Import ISim.
Require Export ITacticsCore.

(***
 Module-level tactics
 ***)

Ltac init_sim :=
  first [eapply hmod_sim_reflR; [(hrepeat do 1 unfold_hmod); eauto|..] | econs];
  [i; s; (hrepeat do 1 unfold_hmod); s
  |eauto
  |try prove_sub_perm
  |try prove_sub_perm
  |unfold_hmod; s; i; des; subst; ss].

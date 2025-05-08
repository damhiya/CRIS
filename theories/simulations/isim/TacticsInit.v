Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import ISimInit.
Require Import TacticsCommon.

(***
 Module-level tactics
 ***)

Ltac unfold_hmod_fn :=
  s; match goal with
     | |-context[_ \/ False] => idtac
     | _ => unfold_hmod; unfold_hmod_fn
     end.

Ltac prove_ist :=
  i; first [iIntros "->" | iIntros "[% ->]"];
  des; iPureIntro; esplits;
  try rewrite state_scopes_update;
  et.

Ltac init_sim :=
  clear_trivials;
  (first
   [ eapply hmod_sim_reflR; [ hrepeat do 1 unfold_hmod; et | prove_ist | prove_ist | .. ]
   | econs ]
  );
  [ i; s; hrepeat do 1 unfold_hmod; s
  | eauto
  | try prove_sub_perm
  | try prove_sub_perm
  | try unfold_hmod_fn; i; des; subst; ss ].

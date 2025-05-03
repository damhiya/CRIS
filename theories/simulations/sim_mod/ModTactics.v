Require Import Common.
Require Import Mod ModSim.
Require Import SimGlobal SimGlobalFacts.

Module ModTac.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_indC_spec; econs; et; i.
  Ltac steps := (hrepeat do 1 step); ired_both.

  Ltac step_l :=
    let ITREE := fresh "ITREE" in
    match goal with [|- _ _ ?it] => remember it as ITREE end;
    step;
    subst ITREE.
    
  Ltac step_r :=
    let ITREE := fresh "ITREE" in
    match goal with [|- _ ?it _] => remember it as ITREE end;
    step;
    subst ITREE.
  
End ModTac.

Require Import Common.
Require Import ISim WSim ITactics WTactics.
Require Export TacticsCommon.

Tactic Notation "iwcase" tactic(itac) tactic(wtac) :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _) ] => itac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
  end.

Ltac norm_l := iwcase (do 1 inorm_l) (do 1 wnorm_l).
Tactic Notation "norm_l" "with" tactic(tac) := iwcase (do 1 inorm_l with tac) (do 1 wnorm_l with tac).

Ltac norm_r := iwcase (do 1 inorm_r) (do 1 wnorm_r).
Tactic Notation "norm_r" "with" tactic(tac) := iwcase (do 1 inorm_r with tac) (do 1 wnorm_r with tac).

Tactic Notation "norm" "with" tactic(tac) := iwcase (do 1 inorm with tac) (wnorm with tac).

Ltac step_l := iwcase (do 1 istep_l) (do 1 wstep_l).
Ltac steps_l := iwcase (do 1 isteps_l) (do 1 wsteps_l).

Ltac step_r := iwcase (do 1 istep_r) (do 1 wstep_r).
Ltac steps_r := iwcase (do 1 isteps_r) (do 1 wsteps_r).

Ltac step := iwcase (do 1 istep) (do 1 wstep).

Tactic Notation "force_l" := iwcase (do 1 iforce_l) (do 1 wforce_l).
Tactic Notation "force_l" uconstr(p) := iwcase (do 1 iforce_l p) (do 1 wforce_l p).
Ltac forces_l := iwcase (do 1 iforces_l) (do 1 wforces_l).

Tactic Notation "force_r" := iwcase (do 1 iforce_r) (do 1 wforce_r).
Tactic Notation "force_r" uconstr(p) := iwcase (do 1 iforce_r p) (do 1 wforce_r p).
Ltac forces_r := iwcase (do 1 iforces_r) (do 1 wforces_r).

Ltac inline_l := iwcase (do 1 iinline_l) (do 1 winline_l).
Ltac inline_r := iwcase (do 1 iinline_r) (do 1 winline_r).

Ltac call hyps := iwcase (do 1 icall hyps) (do 1 wcall hyps).

Ltac yield hyps := iwcase (do 1 iyield hyps) (do 1 wyield hyps).

Ltac by_coind CIH := iwcase (do 1 iby_coind CIH) (do 1 wby_coind CIH).

Tactic Notation "init_simF" := iinit_simF.
Tactic Notation "init_simF" open_constr(u_src) open_constr(u_tgt) := winit_simF u_src u_tgt.





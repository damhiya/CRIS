From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import ISim WSim.
Require Export TacticsCommon ITactics WTactics.

Tactic Notation "iwcase" tactic(itac) tactic(wtac) :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _) ] => itac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
  end.

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

Ltac spawn := iwcase (do 1 ispawn) (do 1 wspawn).

Ltac yield hyps := iwcase (do 1 iyield hyps) (do 1 wyield hyps).

Ltac by_coind CIH := iwcase (do 1 iby_coind CIH) (do 1 wby_coind CIH).

Tactic Notation "init_simF" := winit_simF. (* for isim mode, use iinit_simF directly *)
(* Tactic Notation "init_simF" open_constr(u_src) open_constr(u_tgt) := winit_simF u_src u_tgt. *)

(** Special Tactics for AssumeProph in Source **)

(* Tactic Notation "asmproph_simple" :=
  iwcase (do 1 iasmproph_simple) (do 1 wasmproph_simple).
                 
Tactic Notation "asmproph_simple" uconstr(p) :=
  iwcase (do 1 iasmproph_simple p) (do 1 wasmproph_simple p).

Ltac asmproph_standard :=
  iwcase (do 1 iasmproph_standard) (do 1 wasmproph_standard).
  
Ltac asmproph_advanced :=
  iwcase (do 1 iasmproph_advanced) (do 1 wasmproph_advanced). *)

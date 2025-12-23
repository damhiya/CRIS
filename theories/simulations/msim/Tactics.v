From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import FSpec ISim WSim.
Require Export TacticsCommon ITactics WTactics.

Tactic Notation "iwcase" tactic(itac) tactic(wtac) :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _) ] => itac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
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

(** Special Tactics for RealUpdate **)

(* Tactic Notation "ru_l_advanced" uconstr(P) := *)
(*   iwcase (do 1 iru_l_advanced P) (do 1 wru_l_advanced P). *)

Tactic Notation "ru_l" uconstr(P) :=
  iwcase (do 1 iru_l P) (do 1 wru_l P).

Ltac ru_r :=
  iwcase (do 1 iru_r) (do 1 wru_r).

(* *)
(*  unfold_lat *)
(* *)

(* Lemma unfold_lat_img `{Σ:GRA} peeking fsp lbody body arg: *)
(*   lat_img peeking fsp lbody body arg = *)
(*     r <- lat_img_body peeking fsp lbody body arg;; *)
(*     match r with *)
(*     | inl _ => tau;; lat_img peeking fsp lbody body arg *)
(*     | inr r => Ret r *)
(*     end. *)
(* Proof. *)
(*   rewrite /lat_img. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1. *)
(*   f_equal. extensionalities. destruct H; et. *)
(*   repeat f_equal. destruct u; et. *)
(* Qed. *)

(* Lemma unfold_lat_real `{Σ:GRA} peeking fsp lbody body arg: *)
(*   lat_real peeking fsp lbody body arg = *)
(*     r <- lat_real_body peeking fsp lbody body arg;; *)
(*     match r with *)
(*     | inl _ => tau;; lat_real peeking fsp lbody body arg *)
(*     | inr r => Ret r *)
(*     end. *)
(* Proof. *)
(*   rewrite /lat_real. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1. *)
(*   f_equal. extensionalities. destruct H; et. *)
(*   repeat f_equal. destruct u; et. *)
(* Qed. *)

(* Ltac unfold_lat_img_l := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_l; *)
(*   rewrite {1}unfold_lat_img {1}/lat_img_body; *)
(*   show_until marker; *)
(*   steps_l. *)

(* Ltac unfold_lat_img_r := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_r; *)
(*   rewrite {1}unfold_lat_img {1}/lat_img_body; *)
(*   show_until marker; *)
(*   steps_r. *)

(* Ltac unfold_lat_real_l := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_l; *)
(*   rewrite {1}unfold_lat_real {1}/lat_real_body; *)
(*   show_until marker; *)
(*   steps_l. *)

(* Ltac unfold_lat_real_r := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_r; *)
(*   rewrite {1}unfold_lat_real {1}/lat_real_body; *)
(*   show_until marker; *)
(*   steps_r. *)

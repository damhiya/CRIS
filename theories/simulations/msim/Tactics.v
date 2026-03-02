From iris.proofmode Require Import proofmode.
Require Import Common ConcRA.
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

Tactic Notation "step" ident(name) := iwcase (do 1 istep name) (do 1 wstep name).
Tactic Notation "step" := iwcase (do 1 istep) (do 1 wstep).

Tactic Notation "force_l" := iwcase (do 1 iforce_l) (do 1 wforce_l).
Tactic Notation "force_l" uconstr(p) := iwcase (do 1 iforce_l p) (do 1 wforce_l p).
Ltac forces_l := iwcase (do 1 iforces_l) (do 1 wforces_l).

Tactic Notation "force_r" := iwcase (do 1 iforce_r) (do 1 wforce_r).
Tactic Notation "force_r" uconstr(p) := iwcase (do 1 iforce_r p) (do 1 wforce_r p).
Ltac forces_r := iwcase (do 1 iforces_r) (do 1 wforces_r).

Ltac inline_l := iwcase (do 1 iinline_l) (do 1 winline_l).
Ltac inline_r := iwcase (do 1 iinline_r) (do 1 winline_r).

Ltac call hyps := iwcase (do 1 icall hyps) (do 1 wcall hyps).

(* Ltac spawn := iwcase (do 1 ispawn) (do 1 wspawn). *)

Ltac yield hyps := iwcase (do 1 iyield hyps) (do 1 wyield hyps).

Ltac by_coind CIH := iwcase (do 1 iby_coind CIH) (do 1 wby_coind CIH).

Ltac _clear_ibot H :=
  let ty := type of H in
  try match ty with context[ibot _ _ _ _ _ _ _ ⊢ _] => clear H end.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) :=
  iStopProof;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH;
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id1) :=
  iStopProof;
  revert id1;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH id1;
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id2 id1];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id3 [id2 id1]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id4 [id3 [id2 id1]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id5 [id4 [id3 [id2 id1]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id6 [id5 [id4 [id3 [id2 id1]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id18) ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17; combine_quant id18;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id18 [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id19) ident(id18) ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17; combine_quant id18; combine_quant id19;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id19 [id18 [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

(* Tactic Notation "init_simF" := winit_simF. (* for isim mode, use iinit_simF directly *) *)
(* (* Tactic Notation "init_simF" open_constr(u_src) open_constr(u_tgt) := winit_simF u_src u_tgt. *) *)

(* (** Special Tactics for RealUpdate **) *)

(* (* Tactic Notation "ru_l_advanced" uconstr(P) := *) *)
(* (*   iwcase (do 1 iru_l_advanced P) (do 1 wru_l_advanced P). *) *)

(* Tactic Notation "ru_l" uconstr(P) := *)
(*   iwcase (do 1 iru_l P) (do 1 wru_l P). *)

(* Ltac ru_r := *)
(*   iwcase (do 1 iru_r) (do 1 wru_r). *)

(* (* *)
(*  unfold_lat *)
(* *) *)

(* Lemma unfold_lat_img `{Σ:GRA} peeking fsp lbody body arg:
  lat_img peeking fsp lbody body arg =
    r <- lat_img_body peeking fsp lbody body arg;;
    match r with
    | inl _ => tau;; lat_img peeking fsp lbody body arg
    | inr r => Ret r
    end.
Proof.
  rewrite /lat_img. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1.
  f_equal. extensionalities. destruct H; et.
  repeat f_equal. destruct u; et.
Qed.

Lemma unfold_lat_real `{Σ:GRA} peeking fsp lbody body arg:
  lat_real peeking fsp lbody body arg =
    r <- lat_real_body peeking fsp lbody body arg;;
    match r with
    | inl _ => tau;; lat_real peeking fsp lbody body arg
    | inr r => Ret r
    end.
Proof.
  rewrite /lat_real. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1.
  f_equal. extensionalities. destruct H; et.
  repeat f_equal. destruct u; et.
Qed.

Ltac unfold_lat_img_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_l.

Ltac unfold_lat_img_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_r.

Ltac unfold_lat_real_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_l.

Ltac unfold_lat_real_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_r. *)

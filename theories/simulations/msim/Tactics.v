From iris.proofmode Require Import proofmode.
Require Import Common ConcRA.
Require Import FSpec ISim WSim.
Require Export TacticsCommon ITactics WTactics.

Tactic Notation "iwcase" tactic(itac) tactic(wtac) :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _) ] => itac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
  end.

Ltac cStepS := iwcase (do 1 istep_s) (do 1 wstep_s).
Ltac cStepsS := iwcase (do 1 isteps_s) (do 1 wsteps_s).

Ltac cStepT := iwcase (do 1 istep_t) (do 1 wstep_t).
Ltac cStepsT := iwcase (do 1 isteps_t) (do 1 wsteps_t).

Tactic Notation "cStep" ident(name) := iwcase (do 1 istep name) (do 1 wstep name).
Tactic Notation "cStep" := iwcase (do 1 istep) (do 1 wstep).

Tactic Notation "cForceS" := iwcase (do 1 iforce_s) (do 1 wforce_s).
Tactic Notation "cForceS" uconstr(p) := iwcase (do 1 iforce_s p) (do 1 wforce_s p).
Ltac cForcesS := iwcase (do 1 iforces_s) (do 1 wforces_s).

Tactic Notation "cForceT" := iwcase (do 1 iforce_t) (do 1 wforce_t).
Tactic Notation "cForceT" uconstr(p) := iwcase (do 1 iforce_t p) (do 1 wforce_t p).
Ltac cForcesT := iwcase (do 1 iforces_t) (do 1 wforces_t).

Ltac cInlineS := iwcase (do 1 iinline_s) (do 1 winline_s).
Ltac cInlineT := iwcase (do 1 iinline_t) (do 1 winline_t).

Ltac cCall hyps := iwcase (do 1 icall hyps) (do 1 wcall hyps).
Ltac cYield hyps := iwcase (do 1 iyield hyps) (do 1 wyield hyps).

Ltac cByCoind CIH := iwcase (do 1 iby_coind CIH) (do 1 wby_coind CIH).

Tactic Notation "cBind" uconstr(RR) := iwcase (do 1 ibind RR) (do 1 wbind RR).

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

(* (** Special Tactics for RealUpdate **) *)

(* (* Tactic Notation "ru_s_advanced" uconstr(P) := *) *)
(* (*   iwcase (do 1 iru_s_advanced P) (do 1 wru_s_advanced P). *) *)

(* Tactic Notation "ru_s" uconstr(P) := *)
(*   iwcase (do 1 iru_s P) (do 1 wru_s P). *)

(* Ltac ru_t := *)
(*   iwcase (do 1 iru_t) (do 1 wru_t). *)

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

Ltac unfold_lat_img_s :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_s.

Ltac unfold_lat_img_t :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_t.

Ltac unfold_lat_real_s :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_s.

Ltac unfold_lat_real_t :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_t. *)

Require Import Common ConcRA.
From iris.proofmode Require Export proofmode.
Require Import TacticsCommon ITactics WTactics Tactics.
Require Import Mod ISim ISimFacts WSim SModTr.

(***
 Module-level tactics
 ***)

(* Ltac hide_flist :=
  let FLS := fresh "FLS" in let FLT := fresh "FLT" in
  match goal with [|- context[(isim_fsem ?fls ?flt)]] =>
    set (FLS := fls); set (FLT := flt)
  end. *)

(* Ltac kill_trivial :=
  match goal with |-?T => match type of T with Prop => econs; fail end end. *)

(* Ltac clear_trivials :=
  (hrepeat do 1
   lazymatch goal with H: ?T |-_ =>
     revert H; 
     try match type of T with Prop =>
       let TMP := fresh "TMP" in
       assert (TMP: T) by (econs; fail); clear TMP; intros []; []
     end
   end);
  i. *)

(* Ltac pre_simF :=
  clear_trivials;
  unfold ISim.sim_fun; i;
  match goal with [H: _|-_] => revert H end;
  hide_flist. *)

(* Ltac post_simF :=
  eexists; split; [eauto|];
  ii; subst; iIntros "IST";
  unfold_cris_defs;
  move_aux. *)

(* Ltac initialize_simF :=
  pre_simF;
  alist_find_simpl;
  let H := fresh "H" in intro H; eapply some_injective in H; subst;
  alist_find_simpl;
  post_simF. *)

(* Ltac unfold_mod_fn :=
  s; match goal with
     | |-context[_ \/ _] => idtac
     | _ => unfold_mod; ss; unfold_mod_fn
     end. *)

(* Ltac prove_ist :=
  i; first [iIntros "->" | iIntros "[% ->]"];
  des; iPureIntro; esplits;
  try rewrite state_scopes_update;
  et. *)

Ltac init_sim :=
  (* clear_trivials; *)
  (first
    [ eapply ISim_reflR;
      [ intros fn; rewrite ?dom_fmap /= ?dom_insert_L;
        set_unfold; intros Hfn; des; subst; last inv Hfn
      | multiset_solver
      | multiset_solver
      | try set_solver
      |]
    | econs; intros Hwf;
      [ multiset_solver
      |
      | intros fn; eapply ISim.sim_fun_strong; rewrite ?dom_fmap /= ?dom_insert_L;
        set_unfold; intros Hfn; des; subst; last inv Hfn
      ]
    ]).

(* Ltac iinit_simF := initialize_simF. *)
(* Lemma wsim_HoareFun_src `{!crisG Γ Σ α β τ _S _I, !concG}
    fsp msk fbd arg fl_src fl_tgt Ist RR r g ps pt st_src st_tgt itr_tgt :
  (∀ N tid x varg,
    precond fsp (N, tid) x varg arg -∗
    wsim fl_src fl_tgt Ist (↑N, ↑N) r g Any.t Any.t
      (λ src tgt, ∃ ret, postcond fsp (N, tid) x src.2 ret ∗ RR (src.1, ret) tgt)
      true pt
      (st_src, SB.sandbox msk (fbd N tid varg))
      (st_tgt, itr_tgt)) ⊢
  wsim fl_src fl_tgt Ist (∅, ∅) r g Any.t Any.t RR ps pt
    (st_src, SB.sandbox msk (SModTr.HoareFun (Some fsp) fbd arg))
    (st_tgt, itr_tgt).
Proof.
  iIntros "sim".
  rewrite /SModTr.HoareFun.
  norm_l. des_if; step_l; ss. destruct _q as [N tid].
  steps_l. des_if; step_l; ss. rename _q into m.
  steps_l. des_if; step_l; ss. rename _q into varg.
  steps_l. des_if; step_l; ss.
  iDestruct "ASM" as "[? [? W]]"; iApply wsim_fold; iFrame "W".
  steps_l. des_if; step_l; ss. steps_l.
  rewrite {2}(bind_ret_r_rev itr_tgt).
  iPoseProof ("sim" with "[$] [$] [$]") as "sim".
  iApply wsim_bind; iFrame "sim".
  clear dependent st_src st_tgt.
  iIntros (st_src r_s st_tgt r_t) "[? [? [W [%ret [Post RR]]]]]".
  steps_l. des_ifs; steps_l; ss.
  force_l ret. steps_l. des_ifs; steps_l; ss.
  forces_l. iFrame. steps_l. des_ifs; steps_l; ss. force_l. iFrame "Post". step; ss.
Qed. *)

Ltac init_simF :=
  rewrite /ISim.sim_fun; simpl_map; intros ??; eexists; split; first refl;
  iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
  rewrite /SB.sandbox_body; simpl fst; simpl snd.

Ltac iStartSim := init_simF; unfold_cris_defs.
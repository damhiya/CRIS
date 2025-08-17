Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import Mod ISim ISimFacts SModTr.
Require Import TacticsCommon ITactics.

(***
 Module-level tactics
 ***)

Ltac hide_flist :=
  let FLS := fresh "FLS" in let FLT := fresh "FLT" in
  match goal with [|- context[(isim_fsem ?fls ?flt)]] =>
    set (FLS := fls); set (FLT := flt)
  end.

Ltac kill_trivial :=
  match goal with |-?T => match type of T with Prop => econs; fail end end.

Ltac clear_trivials :=
  (hrepeat do 1
   lazymatch goal with H: ?T |-_ =>
     revert H; 
     try match type of T with Prop =>
       let TMP := fresh "TMP" in
       assert (TMP: T) by (econs; fail); clear TMP; intros []; []
     end
   end);
  i.

Ltac pre_simF :=
  clear_trivials;
  unfold ISim.sim_fun; i;
  match goal with [H: _|-_] => revert H end;
  hide_flist.

Ltac post_simF :=
  eexists; split; [eauto|];
  ii; subst; iIntros "IST";
  unfold_cris_defs;
  move_aux.

Ltac initialize_simF :=
  pre_simF;
  alist_find_simpl;
  let H := fresh "H" in intro H; eapply some_injective in H; subst;
  alist_find_simpl;
  post_simF.

Ltac unfold_mod_fn :=
  s; match goal with
     | |-context[_ \/ _] => idtac
     | _ => unfold_mod; ss; unfold_mod_fn
     end.

Ltac prove_ist :=
  i; first [iIntros "->" | iIntros "[% ->]"];
  des; iPureIntro; esplits;
  try rewrite state_scopes_update;
  et.

Ltac init_sim :=
  clear_trivials;
  (first
  [ eapply ISim_reflR;
    [ hrepeat do 1 unfold_mod; et
    | try prove_sub_perm
    | try prove_sub_perm
    | r; (hrepeat do 1 unfold_mod; s); i; ss
    | try unfold_mod_fn; i; des; subst; ss
    ]
  | econs; i;
    [ try prove_sub_perm
    | try prove_sub_perm
    | r; (hrepeat do 1 unfold_mod; s); i; ss
    | eapply ISim.sim_fun_strong; try unfold_mod_fn; i; des; subst; ss
    ]
  ]).

Ltac iinit_simF := initialize_simF.

Ltac prove_fr_to_img :=
  iinit_simF; iDestruct "IST" as "->"; iIntros "_"; isteps_r;
  match goal with |- context[fancy_real_update ?fsp _] =>
    iApply (isim_fr_to_img fsp)
  end;
  rewrite !SRed.core !SBRed.choose; refl.

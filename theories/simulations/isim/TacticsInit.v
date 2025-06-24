Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import ISimInit SModTr.
Require Import TacticsCommon.

(***
 Module-level tactics
 ***)

Ltac hide_flist :=
  let FLS := fresh "FLS" in let FLT := fresh "FLT" in
  match goal with [|- context[(isim_fsem ?fls ?flt _ _)]] =>
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
  unfold HSim.sim_fun; i;
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
  let H := fresh "H" in intro H; inv H;
  alist_find_simpl;
  post_simF.

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
   [ eapply hmod_sim_reflR; [ hrepeat do 1 unfold_hmod; et | .. ]
   | econs ]
  ); i;
  [ try rewrite /Ist_monotone; eauto
  | try prove_sub_perm
  | try prove_sub_perm
  | r; hrepeat do 1 unfold_hmod; s; i
  | eapply HSim.sim_fun_strong; try unfold_hmod_fn; i; des; subst; ss ].

Ltac iinit_simF := initialize_simF.

Ltac prove_proph_sim :=
  s; et; ii;
  match goal with [H: _|-_] => revert H; alist_find_simpl; i; depdes H end;
  alist_find_simpl; esplits; et;
  eapply isim_fsem_proph_to_normal; i;
  rewrite SRed.fbody_trivial;
  iIntros; iApply isim_refl; et; i; iIntros "%"; subst; et.

From CRIS.common Require Import Common.
From CRIS.modules Require Import LMod.
From CRIS.simulations.lsim Require Import LSim.

Set Implicit Arguments.

#[export] Hint Resolve lsim_mon : paco.
#[export] Hint Resolve cpn8_wcompat : paco.

Ltac ired_s := try (prw _red_gen 2 1 0).
Ltac ired_t := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_s; ired_t.

Ltac prep := ired_both. (* prepare *)
  
Ltac _step :=
  ired_both; apply lsimC_spec; econs; i;
  match goal with
  | [ |- exists (_ : unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end.

Ltac step := prep; _step; simpl; des_ifs_safe.
Ltac steps := (hrepeat ltac:(step)); prep.

Tactic Notation "hide" constr(tm) integer(occ) :=
  let tmp := fresh "tmp" in let TMP := fresh "TMP" in
  set (xxx := tm) at occ; remember xxx as tmp eqn : TMP;
  unfold xxx in *; clear xxx; guardH TMP.
Ltac unhide :=
  unguard; subst.

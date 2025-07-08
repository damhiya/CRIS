Require Import Common.
Require Import Mod ModSim.
Require Import SimGlobal SimGlobalFacts.

Definition ztac_id {X: Type} (x: X) : X := x.
Global Opaque ztac_id.

Ltac zss :=
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * ).

Ltac zonly_l :=
  let ITREE := fresh "ITREE" in
  let GPACO := fresh "GPACO" in 
  match goal with
    [|- ?rel _ ?it] =>
      set (GPACO := rel); first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end;
  change ITREE with (ztac_id ITREE);
  move ITREE at top.

Ltac zonly_r :=
  let ITREE := fresh "ITREE" in
  let GPACO := fresh "GPACO" in 
  match goal with
    [|- ?rel ?it _] =>
      set (GPACO := rel); set (ITREE := it) at 1
  end;
  change ITREE with (ztac_id ITREE);
  move ITREE at top.

Ltac zshow :=
  match goal with
    [ITREE := ?t|-_] =>
      match type of ITREE with
        itree _ _ => change (ztac_id ITREE) with ITREE; subst ITREE
      end
  end;
  match goal with
    [GPACO := ?rel|-_] => subst GPACO
  end.

Ltac zsimpl_len :=
  simpl List.length in *;
  try rewrite ->!length_app in * ;
  try rewrite ->!length_insert in * ;
  try rewrite ->!length_app in * ;
  try rewrite ->!Nat.sub_diag in * ;
  simpl List.length in *;
  try nia.

Ltac zsimpl_ths :=
  ired;
  zsimpl_len;
  try (hrepeat do 1 (rewrite insert_app_l; [|zsimpl_len; fail]));
  try (rewrite !list_insert_insert).

Ltac zsimpl_lookup :=
  try (rewrite lookup_app_l; [|zsimpl_len; fail]);
  try (rewrite lookup_app_r; [|zsimpl_len; fail]).

Ltac zlookup_insert :=
  try (rewrite list_lookup_insert); zsimpl_len.

Ltac zlookup_insert_ne :=
  try (rewrite list_lookup_insert_ne); zsimpl_len.

Ltac ziter :=
  rewrite unfold_iterV; ired;
  try rewrite /ModTr.interp_stateE;
  try rewrite /ModTr.pure_state;
  zsimpl_lookup;
  zlookup_insert;
  zsimpl_ths;
  zss.

Ltac zstep :=
  ired; guclo simg_indC_spec; econs; et; i;
  zsimpl_ths;
  zss.

Ltac ziter_l := zonly_l; ziter; zshow.
Ltac ziter_r := zonly_r; ziter; zshow.

Ltac zstep_l := zonly_l; zstep; zshow.
Ltac zstep_r := zonly_r; zstep; zshow.

Ltac zprogress :=
  gstep; econs; eapply simg_progress; eauto using smj_lt_mid_top.

Tactic Notation "zprogress" "with" uconstr(ps0) uconstr(pt0) uconstr(ps) uconstr(pt) :=
  gstep; econs; eapply (simg_progress _ _ _ ps pt ps0 pt0); eauto.

Ltac cziter_r := unshelve ziter_r; try match goal with | |- smj => exact smj_top end.
Ltac cziter_l := unshelve ziter_l; try match goal with | |- smj => exact smj_top end.
Ltac czstep_r := unshelve zstep_r; try match goal with | |- smj => exact smj_top end.
Ltac czstep_l := unshelve zstep_l; try match goal with | |- smj => exact smj_top end.
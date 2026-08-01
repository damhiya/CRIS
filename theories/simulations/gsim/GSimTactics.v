From CRIS.common Require Import Common.
From CRIS.modules Require Import LMod.
From CRIS.simulations.msim Require Import TacticsCommon.
From CRIS.modules Require Export Mod SMod.
From CRIS.simulations.gsim Require Export GSim.

Section auxilliary.
  Context {Σ : GRA}.

  Lemma Red_vis_Assume {R} P (ktr : () → itree crisE R) :
    ModTr.trans (vis (Events.Assume P) ktr) =
    a <- itreeV_itree (ModTr.handle_Assume P);; ModTr.trans (ktr a).
  Proof using. rewrite vis_trigger Red.bind Red.Assume; ss. Qed.

  Lemma Red_vis_Take {R} X (ktr : X → itree crisE R) :
    ModTr.trans (vis (Events.Take X) ktr) =
    x <- trigger (Take X);; ModTr.trans (ktr x).
  Proof using. rewrite /ModTr.trans interpV_vis /itreeV_itree /=. grind. Qed.

  Lemma Red_unwrapUK {X R} x (ktr : X -> itree crisE R) :
    ModTr.trans (unwrapUK x ktr) = unwrapUK x (fun x => ModTr.trans (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.
End auxilliary.

Ltac greplace_s :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ ?itr _ =>
    pattern itr;
    match goal with
    | |- ?f ?a =>
      refine (eq_ind_r f _ _); cycle 1
    end
  end.

Ltac greplace_t :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ _ ?itr =>
    pattern itr;
    match goal with
    | |- ?f ?a =>
      refine (eq_ind_r f _ _); cycle 1
    end
  end.

Tactic Notation "red_LModTr" tactic(tac) :=
  match goal with
  | |- ?H => idtac H
  end.

Tactic Notation "red_ModTr" tactic(tac) :=
  lazymatch goal with
  | [ |- @ModTr.trans _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply Red.ret
      | Tau _ =>
          eapply Red.tau
      | vis (Assume _) _ =>
          eapply Red_vis_Assume
      | vis (Take _) _ =>
          eapply Red_vis_Take
      (* | unwrapUK _ _ =>
          eapply Red_unwrapUK *)
      (* | vis (Red_AssumeRes _) _ =>
          eapply SRed.vis_ag
      | vis (Guarantee _) _ =>
          eapply SRed.vis_ag
      | vis (Spawn ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_spawn
          | unfold SModTr.HoareSpawn, SModTr.NativeSpawn;
            unfold_sp_exact sp fn; s;
            tac
          ]
      | vis (Yield _) _ =>
          etransitivity;
          [ eapply SRed.vis_yield
          | tac
          ]
      | vis (Call ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_call
          | unfold SModTr.HoareCall;
            unfold_sp_exact sp fn; s;
            tac
          ]
      | vis (SPut _ _) _ =>
          eapply SRed.vis_pg
      | vis (SGet _) _ =>
          eapply SRed.vis_pg
      | vis (Choose _) _ =>
          eapply SRed.vis_core
      | vis (IO _ _) _ =>
          eapply SRed.vis_core
      | assumeK _ _ =>
          eapply SRed.assumeK
      | guaranteeK _ _ =>
          eapply SRed.guaranteeK
      | unwrapNK _ _ =>
          eapply SRed.unwrapNK
      | RealUpdateK _ _ _ _ =>
          eapply SRed.update_prophK
      | @ITree.bind _ _ _ _ _ =>
          eapply SRed.bind *)
      | _ =>
          reflexivity
      end
  end.

Tactic Notation "red_LModTr_state" tactic(tac) :=
  lazymatch goal with
  | [ |- @LModTr.interp_stateE ?Σ ?E ?T ?itr ?state = _] =>
    match itr with
    | @iterV ?A ?B ?C ?handle ?itr => reflexivity
    | _ =>
      etransitivity;
      [rewrite /= /LModTr.interp_stateE;
        lazymatch itr with
        | @ITree.bind _ _ _ _ _ =>
          eapply interp_state_bind
        | Ret _ =>
          eapply interp_state_ret
        | vis _ _ =>
          etransitivity; [eapply interp_state_vis|tac; refl]
        | Tau _ =>
          eapply interp_state_tau
        | unwrapUK _ _ =>
          etransitivity; [rewrite /unwrapUK; refl|tac]
        | _ =>
          reflexivity
        end
      | fold (@LModTr.interp_stateE Σ coreE); refl]
    end
  end.

Ltac _gnorm_itr :=
  lazymatch goal with
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      reflexivity
  | [ |- @ITree.bind ?E ?T ?U ?itr ?ktr = _ ] =>
      etransitivity;
      [ let itr' := fresh "itr" in cong (fun (itr' : itree E T) => @ITree.bind E T U itr' ktr); _gnorm_itr
      | s; red_bind (do 1 _gnorm_itr) ]
  | [ |- @SB.sandbox ?Σ ?R ?img ?imports ?scopes ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ R img imports scopes); _gnorm_itr | red_SB (do 1 _gnorm_itr) ]
  | [ |- @SModTr.trans ?Σ ?sp ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Σ sp R); _gnorm_itr | red_S (do 1 _gnorm_itr) ]
  | [ |- @LModTr.interp_stateE ?Σ ?E ?T ?itr ?st = _] =>
      etransitivity;
      [ cong (λ i, @LModTr.interp_stateE Σ E T i st); _gnorm_itr
      | red_LModTr_state (do 1 _gnorm_itr)]
  (* | [ |- @iterV ?A ?B ?C ?handle ?itr = _ ] =>
      idtac "iterV "; idtac itr;
      (rewrite unfold_iterV /itreeV_itree;
      lazymatch goal with
      | |- context [@LModTr.handle_callE ?Σ ?prog ?a] =>
        pattern (@LModTr.handle_callE Σ prog a);
        lazymatch goal with
        | [ |- ?f ?a] =>
          refine (eq_ind_r f _ _); cycle 1;
          [_gnorm_itr
          | lazymatch goal with
            | |- context [_observe ?f] => idtac f; fail
            | |- _ => s; _gnorm_itr
            end
          ]
        end
      end
      + refl) *)
  | [ |- @case_ _ _ _ _ _ _ _ _ _ _ _ ?E = _] =>
      rewrite /case_ /LModTr.pure_state /=; _gnorm_itr
  | [ |- @ModTr.trans ?A ?B ?itr = _] =>
      etransitivity;
      [ cong (@ModTr.trans A B); _gnorm_itr | red_ModTr (do 1 _gnorm_itr) ]
  | [ |- @LModTr.handle_callE ?Σ ?prog ?a = _] =>
    rewrite /LModTr.handle_callE;
    match goal with
    | |- context [?a !! ?b] =>
      pattern (a !! b);
      match goal with
      | |- ?f ?a =>
        eapply (eq_ind_r f); cycle 1; [s; eapply (f_equal Some); _gnorm_itr|ss]
      end
    end
  | [ |- trigger _ = _ ] =>
      eapply trigger_vis
  | [ |- assume _ = _ ] =>
      eapply assume_assumeK
  | [ |- guarantee _ = _ ] =>
      eapply guarantee_guaranteeK
  | [ |- unwrapU _ = _ ] =>
      eapply unwrapU_unwrapUK
  | [ |- unwrapN _ = _ ] =>
      eapply unwrapN_unwrapNK
  | [ |- RealUpdate _ _ = _ ] =>
      eapply RealUpdate_RealUpdateK
  | [ |- SModTr.HoareCall _ _ _ = _ ] =>
      unfold SModTr.HoareCall;
      _gnorm_itr
  | [ |- fbody_trivial _ = _ ] =>
      unfold fbody_trivial;
      _gnorm_itr
  | [ |- cput _ _ = _ ] =>
      unfold cput;
      _gnorm_itr
  | [ |- cgetU _ = _ ] =>
      unfold cgetU;
      _gnorm_itr
  | [ |- cgetN _ = _ ] =>
      unfold cgetN;
      _gnorm_itr
  | [ |- cfunU _ _ = _ ] =>
      unfold cfunU;
      _gnorm_itr
  | [ |- cfunN _ _ = _ ] =>
      unfold cfunN;
      _gnorm_itr
  | [ |- ccallU _ _ = _ ] =>
      unfold ccallU;
      _gnorm_itr
  | [ |- ccallN _ _ = _ ] =>
      unfold ccallN;
      _gnorm_itr
  | [ |- triggerUB = _ ] =>
      unfold triggerUB;
      _gnorm_itr
  | [ |- triggerNB = _ ] =>
      unfold triggerNB;
      _gnorm_itr
  | [ |- ?itr = _ ] =>
      reflexivity
end.
Ltac gnorm_itr :=
etransitivity;
[ _gnorm_itr
| s;
  lazymatch goal with
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      eapply vis_trigger
  | [ |- _ = _ ] =>
      reflexivity
  end
].

Ltac gcNormS :=
  greplace_s; [s; gnorm_itr|].
Ltac gcNormT :=
  greplace_t; [s; gnorm_itr|].

Ltac giter_s :=
  greplace_s; [rewrite unfold_iterV /itreeV_itree //|].
Ltac giter_t :=
  greplace_t; [rewrite unfold_iterV /itreeV_itree //|].

Ltac gstep_t := gcNormT; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
Ltac gstep_s := gcNormS; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).

Ltac gsteps_t :=
  gcNormT; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try gcNormT)).
Ltac gsteps_s :=
  gcNormS; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try gcNormS)).

Definition ztac_id {X: Type} (x: X) : X := x.
Global Opaque ztac_id.

Ltac zss :=
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * ).

Ltac zonly_s :=
  let ITREE := fresh "ITREE" in
  let GPACO := fresh "GPACO" in 
  match goal with
    [|- ?rel _ ?it] =>
      set (GPACO := rel); first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end;
  change ITREE with (ztac_id ITREE);
  move ITREE at top.

Ltac zonly_t :=
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
  try rewrite /LModTr.interp_stateE;
  try rewrite /LModTr.pure_state;
  zsimpl_lookup;
  zlookup_insert;
  zsimpl_ths;
  zss.

Ltac zstep :=
  ired; guclo gsim_indC_spec; econs; et; i;
  zsimpl_ths;
  zss.

Ltac zinst := try match goal with | |- smj => exact smj_top end.

Ltac ziter_s := zonly_s; ziter; zshow.
Ltac ziter_t := zonly_t; ziter; zshow.

Ltac zostep_s := zonly_s; zstep; zshow.
Ltac zostep_t := zonly_t; zstep; zshow.
  
Ltac zstep_s := unshelve zostep_s; zinst.
Ltac zstep_t := unshelve zostep_t; zinst.

Ltac zprogress :=
  gstep; econs; eapply gsim_progress; eauto using smj_lt_mid_top.

Tactic Notation "zprogress" "with" uconstr(ps0) uconstr(pt0) uconstr(ps) uconstr(pt) :=
  gstep; econs; eapply (gsim_progress _ _ _ ps pt ps0 pt0); eauto.

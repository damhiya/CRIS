Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.

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

Tactic Notation "red_bind" tactic(tac) :=
  lazymatch goal with
  | [ |- @ITree.bind _ _ _ ?itr _ = _ ] =>
      lazymatch itr with
      | Ret _ => etransitivity; [ eapply bind_ret_l | s; tac ]
      | Tau _ => eapply bind_tau
      | vis _ _ => eapply vis_bind
      | assumeK _ _ => eapply assumeK_bind
      | guaranteeK _ _ => eapply guaranteeK_bind
      | unwrapUK _ _ => eapply unwrapUK_bind
      | unwrapNK _ _ => eapply unwrapNK_bind
      (* | RealUpdateK _ _ => eapply RealUpdateK_bind *)
      (* | SBRed.putSB _ _ _ _ _ _ => eapply SBRed.putSB_bind *)
      (* | SBRed.getSB _ _ _ _ _ => eapply SBRed.getSB_bind *)
      (* | SBRed.callSB _ _ _ _ _ _ => eapply SBRed.callSB_bind *)
      (* | SBRed.spawnSB _ _ _ _ _ _ => eapply SBRed.spawnSB_bind *)
      | @ITree.bind _ _ _ _ _ => eapply bind_bind
      | _ => reflexivity
      end
  end.

(* Tactic Notation "red_SB" := *)
(*   lazymatch goal with *)
(*   | [ |- @SB.sandbox _ _ _ _ _ ?itr = _ ] => *)
(*       lazymatch itr with *)
(*       | Ret _ => *)
(*           eapply SBRed.ret *)
(*       | Tau _ => *)
(*           eapply SBRed.tau *)
(*       | vis (Assume _) _ => *)
(*           first [eapply SBRed.vis_Assume_img|eapply SBRed.vis_Assume] *)
(*       | vis (AssumeRes _) _ => *)
(*           eapply SBRed.vis_AssumeRes *)
(*       | vis (Guarantee _) _ => *)
(*           eapply SBRed.vis_Guarantee *)
(*       | vis (Spawn _ _) _ => *)
(*           eapply SBRed.Spawn_spawnSB *)
(*       | vis (Yield _) _ => *)
(*           eapply SBRed.vis_yield *)
(*       | vis (Call _ _) _ => *)
(*           eapply SBRed.Call_callSB *)
(*       | vis (SPut _ _) _ => *)
(*           eapply SBRed.SPut_putSB *)
(*       | vis (SGet _) _ => *)
(*           eapply SBRed.SGet_getSB *)
(*       | vis (Choose _) _ => *)
(*           eapply SBRed.vis_choose *)
(*       | vis (Take _) _ => *)
(*           first [eapply SBRed.vis_take_img|eapply SBRed.vis_take] *)
(*       | vis (IO _ _) _ => *)
(*           eapply SBRed.vis_io *)
(*       | assumeK _ _ => *)
(*           eapply SBRed.assumeK *)
(*       | guaranteeK _ _ => *)
(*           eapply SBRed.guaranteeK *)
(*       | unwrapUK _ _ => *)
(*           eapply SBRed.unwrapUK *)
(*       | unwrapNK _ _ => *)
(*           eapply SBRed.unwrapNK *)
(*       (* | RealUpdateK _ _ _ => *) *)
(*       (*     eapply SBRed.ruK *) *)
(*       | @ITree.bind _ _ _ _ _ => *)
(*           eapply SBRed.bind *)
(*       | _ => *)
(*           reflexivity *)
(*       end *)
(*   end. *)

(* Tactic Notation "red_S" tactic(tac) := *)
(*   lazymatch goal with *)
(*   | [ |- @SModTr.trans _ ?sp _ ?itr = _ ] => *)
(*       lazymatch itr with *)
(*       | Ret _ => *)
(*           eapply SRed.ret *)
(*       | Tau _ => *)
(*           eapply SRed.tau *)
(*       | vis (Assume _) _ => *)
(*           eapply SRed.vis_ag *)
(*       | vis (AssumeRes _) _ => *)
(*           eapply SRed.vis_ag *)
(*       | vis (Guarantee _) _ => *)
(*           eapply SRed.vis_ag *)
(*       | vis (Spawn ?fn _) _ => *)
(*           etransitivity; *)
(*           [ eapply SRed.vis_spawn *)
(*           | unfold SModTr.HoareSpawn, SModTr.NativeSpawn; *)
(*             unfold_sp_exact sp fn; s; *)
(*             tac *)
(*           ] *)
(*       | vis (Yield _) _ => *)
(*           etransitivity; *)
(*           [ eapply SRed.vis_yield *)
(*           | tac *)
(*           ] *)
(*       | vis (Call ?fn _) _ => *)
(*           etransitivity; *)
(*           [ eapply SRed.vis_call *)
(*           | unfold SModTr.HoareCall; *)
(*             unfold_sp_exact sp fn; s; *)
(*             tac *)
(*           ] *)
(*       | vis (SPut _ _) _ => *)
(*           eapply SRed.vis_pg *)
(*       | vis (SGet _) _ => *)
(*           eapply SRed.vis_pg *)
(*       | vis (Choose _) _ => *)
(*           eapply SRed.vis_core *)
(*       | vis (Take _) _ => *)
(*           eapply SRed.vis_core *)
(*       | vis (IO _ _) _ => *)
(*           eapply SRed.vis_core *)
(*       | assumeK _ _ => *)
(*           eapply SRed.assumeK *)
(*       | guaranteeK _ _ => *)
(*           eapply SRed.guaranteeK *)
(*       | unwrapUK _ _ => *)
(*           eapply SRed.unwrapUK *)
(*       | unwrapNK _ _ => *)
(*           eapply SRed.unwrapNK *)
(*       | RealUpdateK _ _ _ => *)
(*           eapply SRed.ruK *)
(*       | @ITree.bind _ _ _ _ _ => *)
(*           eapply SRed.bind *)
(*       | _ => *)
(*           reflexivity *)
(*       end *)
(*   end. *)

Ltac replace_l :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ ?itr _ =>
      pattern itr;
      match goal with
      | |- ?f ?a =>
          refine (eq_ind_r f _ _); cycle 1
      end
  end.

Ltac replace_r :=
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
      | unwrapUK _ _ =>
          eapply Red_unwrapUK
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

(* Local Lemma LModTr_interp_stateE_bind {A B} itr state : *)

Tactic Notation "red_LModTr_state" tactic(tac) :=
  lazymatch goal with
  | [ |- @LModTr.interp_stateE ?A ?B ?itr ?state = _] =>
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
          | fold (@LModTr.interp_stateE coreE); refl]
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
      [ cong (@SB.sandbox Σ R img imports scopes); _gnorm_itr | ]
  | [ |- @SModTr.trans ?Σ ?sp ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Σ sp R); _gnorm_itr | red_S (do 1 _gnorm_itr) ]
  | [ |- @LModTr.interp_stateE ?E ?T ?itr ?st = _] =>
      etransitivity;
      [ cong (λ i, @LModTr.interp_stateE E T i st); _gnorm_itr | red_LModTr_state (do 1 _gnorm_itr)]
  (* | [ |- @iterV ?A ?B ?C ?handle ?itr = _ ] =>
        idtac "iterV "; idtac itr;
        (rewrite unfold_iterV /itreeV_itree;
        lazymatch goal with
        | |- context [@LModTr.handle_callE ?A ?B] =>
          pattern (LModTr.handle_callE A B);
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
  | [ |- @LModTr.handle_callE ?prog ?a = _] =>
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

Ltac norm_l :=
  replace_l; [s; gnorm_itr|].
Ltac norm_r :=
  replace_r; [s; gnorm_itr|].

Ltac iter_l :=
  replace_l; [rewrite unfold_iterV /itreeV_itree //|]; norm_l.
Ltac iter_r :=
  replace_r; [rewrite unfold_iterV /itreeV_itree //|]; norm_r.

Ltac step_r :=
  norm_r; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
Ltac step_l :=
  norm_l; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).

Ltac replace_tp_r :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ _ (LModTr.interp_stateE _ (iterV _ ?tp) _) =>
      pattern tp;
      match goal with
      | |- ?f ?tp =>
          eapply (eq_ind_r f); cycle 1
      end
  end.
Ltac replace_tp_l :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ (LModTr.interp_stateE _ (iterV _ ?tp) _) _ =>
      pattern tp;
      match goal with
      | |- ?f ?tp =>
          eapply (eq_ind_r f); cycle 1
      end
  end.

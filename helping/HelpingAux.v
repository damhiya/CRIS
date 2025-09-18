Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff.

(* This file contains auxilliary lemmas for proving HelpOn ≼ HelpOff. *)
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
      | RealUpdateK _ _ => eapply RealUpdateK_bind
      | SBRed.putSB _ _ _ _ _ _ => eapply SBRed.putSB_bind
      | SBRed.getSB _ _ _ _ _ => eapply SBRed.getSB_bind
      | SBRed.callSB _ _ _ _ _ _ => eapply SBRed.callSB_bind
      | SBRed.spawnSB _ _ _ _ _ _ => eapply SBRed.spawnSB_bind
      | @ITree.bind _ _ _ _ _ => eapply bind_bind
      | _ => reflexivity
      end
  end.

Tactic Notation "red_SB" :=
  lazymatch goal with
  | [ |- @SB.sandbox _ _ _ _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SBRed.ret
      | Tau _ =>
          eapply SBRed.tau
      | vis (Assume _) _ =>
          first [eapply SBRed.vis_Assume_img|eapply SBRed.vis_Assume]
      | vis (AssumeRes _) _ =>
          eapply SBRed.vis_AssumeRes
      | vis (Guarantee _) _ =>
          eapply SBRed.vis_Guarantee
      | vis (Spawn _ _) _ =>
          eapply SBRed.Spawn_spawnSB
      | vis (Yield _) _ =>
          eapply SBRed.vis_yield
      | vis (Call _ _) _ =>
          eapply SBRed.Call_callSB
      | vis (SPut _ _) _ =>
          eapply SBRed.SPut_putSB
      | vis (SGet _) _ =>
          eapply SBRed.SGet_getSB
      | vis (Choose _) _ =>
          eapply SBRed.vis_choose
      | vis (Take _) _ =>
          first [eapply SBRed.vis_take_img|eapply SBRed.vis_take]
      | vis (IO _ _) _ =>
          eapply SBRed.vis_io
      | assumeK _ _ =>
          eapply SBRed.assumeK
      | guaranteeK _ _ =>
          eapply SBRed.guaranteeK
      | unwrapUK _ _ =>
          eapply SBRed.unwrapUK
      | unwrapNK _ _ =>
          eapply SBRed.unwrapNK
      | RealUpdateK _ _ _ =>
          eapply SBRed.ruK
      | @ITree.bind _ _ _ _ _ =>
          eapply SBRed.bind
      | _ =>
          reflexivity
      end
  end.

Tactic Notation "red_S" tactic(tac) :=
  lazymatch goal with
  | [ |- @SModTr.trans _ ?sp _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SRed.ret
      | Tau _ =>
          eapply SRed.tau
      | vis (Assume _) _ =>
          eapply SRed.vis_ag
      | vis (AssumeRes _) _ =>
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
      | vis (Take _) _ =>
          eapply SRed.vis_core
      | vis (IO _ _) _ =>
          eapply SRed.vis_core
      | assumeK _ _ =>
          eapply SRed.assumeK
      | guaranteeK _ _ =>
          eapply SRed.guaranteeK
      | unwrapUK _ _ =>
          eapply SRed.unwrapUK
      | unwrapNK _ _ =>
          eapply SRed.unwrapNK
      | RealUpdateK _ _ _ =>
          eapply SRed.ruK
      | @ITree.bind _ _ _ _ _ =>
          eapply SRed.bind
      | _ =>
          reflexivity
      end
  end.

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
      [ cong (@SB.sandbox Σ R img imports scopes); _gnorm_itr | red_SB ]
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
  | [ |- SModTr.NativeSpawn _ _ = _ ] =>
      unfold SModTr.NativeSpawn;
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

Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
Notation "'⇓sb(' i ',' m ',' s ')'" := (interpV (SB.handle_sandbox i m s)).
Notation "'⇓smod(' img ',' sp ')'" := (interpV (SModTr.handle img sp)).

Section props.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  Lemma gsim_flag r g RR p_s p_t i_s i_t :
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
      i_s i_t →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      i_s i_t.
  Proof.
    intros ?; guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
  Qed.

  Lemma gsim_tau_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k2 : Any.t → _) :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (tau;; k));; k2 x) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k2 x)]> tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof. intros Hi ?. iter_l; rewrite Hi; ss. step_l; norm_l. done. Qed.

  Lemma gsim_tau_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k2 : Any.t → _) :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (tau;; k));; k2 x) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k2 x]> tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof. intros Hi ?. iter_r; rewrite Hi; ss. step_r; norm_r. done. Qed.

  Lemma gsim_Choose_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c X k (k2 : Any.t → _) :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (Choose X);; k x));; k2 x) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k x));; k2 x)]> tp_s)) st_s)
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi [x Hk]. iter_l; rewrite Hi; ss. step_l. exists x. norm_l. step_l. norm_l. ired. done.
  Qed.

  Lemma gsim_Choose_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c X k (k2 : Any.t → _) :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (Choose X);; k x));; k2 x) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k x));; k2 x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi Hk. iter_r; rewrite Hi; ss. step_r. intros x. norm_r. step_r. norm_r. ired. eapply Hk.
  Qed.

  Lemma gsim_Take_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c X k (k2 : Any.t → _) :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (Take X);; k x));; k2 x) →
    (∀ (x : X),
      (img_c = true ∨ (∃ P : Prop, X = P)) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k x));; k2 x)]> tp_s)) st_s)
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hk. iter_l. rewrite Hin; ss.
    destruct img_c; norm_l; cycle 1.
    { destruct (excluded_middle_informative _) as [?|?]; des; clarify; ss; step_l; ss.
      intros x; step_l; ired. norm_l. eapply Hk; right; eauto.
    }
    step_l. intros x. norm_l. step_l. norm_l. ired.
    eapply Hk; eauto.
  Qed.

  Lemma gsim_Take_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c X k (k2 : Any.t → _) :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (Take X);; k x));; k2 x) →
    (∃ (x : X),
      (img_c = true ∨ (∃ P : Prop, X = P)) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k x));; k2 x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi [x [Hx Hk]].
    iter_r; rewrite Hi; ss.
    destruct (orb _ _) eqn : E; ss; simpl_bool; cycle 1.
    { des; clarify; ss. destruct (excluded_middle_informative _); ss.
      exfalso; apply n; eexists; eauto.
    }
    norm_r. step_r. exists x. step_r. norm_r. ired. eapply Hk.
  Qed.

  Lemma gsim_sGet_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c key k (k2 : Any.t → _) r_t :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (SGet key);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →
    (∃ t, alist_find key st_t = Some t ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k t));; k2 x)]> tp_t))
          (Any.pair (ModTr.alist_encode st_t) r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair (ModTr.alist_encode st_t) r_t)).
  Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_r; rewrite Hin; ss.
    rewrite Hkey /=.
    norm_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode Ht /=. ired. eapply Hk.
  Qed.

  Lemma gsim_sGet_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c key k (k2 : Any.t → _) r_s :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- trigger (SGet key);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →
    (∃ t, alist_find key st_s = Some t ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k t));; k2 x)]> tp_s))
          (Any.pair (ModTr.alist_encode st_s) r_s))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (Any.pair (ModTr.alist_encode st_s) r_s))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_l; rewrite Hin; ss.
    rewrite Hkey /=.
    norm_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode Ht /=. ired. eapply Hk.
  Qed.

  Lemma gsim_s_cgetU_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t b sp
      img_c msk_c scp_c key {A} (k : A → _) (k2 : Any.t → _) r_t :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
      (x <- ⇓smod(b, sp)(cgetU key);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →      
    (∃ (t : A), alist_find key st_t = Some (t↑) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k t));; k2 x)]> tp_t))
          (Any.pair (ModTr.alist_encode st_t) r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair (ModTr.alist_encode st_t) r_t)).
  Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_r; rewrite Hin /= Hkey /=.
    norm_r. step_r. norm_r. hss. ired. rewrite ModTr.alist_encode_decode Ht /=. hss.
    rewrite ?interpV_ret. ired. eauto.
  Qed.

  Lemma gsim_s_cgetU_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t b sp
      img_c msk_c scp_c key {A} (k : A → _) (k2 : Any.t → _) r_s :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
      (x <- ⇓smod(b, sp)(cgetU key);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →      
    (∃ t, alist_find key st_s = Some t↑ ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k t));; k2 x)]> tp_s))
          (Any.pair (ModTr.alist_encode st_s) r_s))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (Any.pair (ModTr.alist_encode st_s) r_s))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_l; rewrite Hin /= Hkey; ss.
    norm_l. step_l. norm_l. hss. ired. rewrite ModTr.alist_encode_decode Ht //=. hss.
    rewrite ?interpV_ret. ired. done.
  Qed.

  Lemma gsim_s_cput_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t b sp
      img_c msk_c scp_c key {A} (v : A) (k : () → _) (k2 : Any.t → _) r_t :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
      (x <- ⇓smod(b, sp)(cput key v);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →      
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k ()));; k2 x)]> tp_t))
        (Any.pair (ModTr.alist_encode (alist_upd key (v↑) st_t)) r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair (ModTr.alist_encode st_t) r_t)).
  Proof.
    intros Hin Hkey Hk.
    eapply lookup_lt_Some in Hin as Hlen.
    iter_r; rewrite Hin /= Hkey /=. norm_r. step_r. norm_r. hss.
    iter_r; rewrite list_lookup_insert //=.
    norm_r. step_r. norm_r. rewrite list_insert_insert. ired.
    rewrite ModTr.alist_encode_decode /=.
    rewrite ?interpV_ret. ired. eauto.
  Qed.

  Lemma gsim_s_cput_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t b sp
      img_c msk_c scp_c key {A} (v : A) (k : () → _) (k2 : Any.t → _) r_s :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
      (x <- ⇓smod(b, sp)(cput key v);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →      
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k ()));; k2 x)]> tp_s))
        (Any.pair (ModTr.alist_encode (alist_upd key (v↑) st_s)) r_s))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (Any.pair (ModTr.alist_encode st_s) r_s))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hkey Hk.
    eapply lookup_lt_Some in Hin as Hlen.
    iter_l; rewrite Hin /= Hkey /=. norm_l. step_l. norm_l. hss.
    iter_l; rewrite list_lookup_insert //=.
    norm_l. step_l. norm_l. rewrite list_insert_insert. ired.
    rewrite ModTr.alist_encode_decode /=.
    rewrite ?interpV_ret. ired. eauto.
  Qed.

  Lemma gsim_Assume_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) P r_s :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Assume P);;; k));; k_2 x) →
    (∀ r_s2,
      img_c = true →
      ✓ r_s2 ∧ (Own r_s2 ⊢ |==> P ∗ Own r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_l; rewrite Hin; ss.
    destruct img_c; step_l; ss.
    norm_l. hss. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. intros r_s2. norm_l. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. intros Hr_s2. norm_l. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired. eapply Hk; done.
  Qed.

  Lemma gsim_Assume_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) P r_t :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Assume P);;; k));; k_2 x) →
    (∃ r_t2,
      img_c = true ∧
      ✓ r_t2 ∧ (Own r_t2 ⊢ |==> P ∗ Own r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof.
    intros Hin [r_t2 [-> [Hr_t2 Hk]]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_r; rewrite Hin; ss.
    step_r; ss.
    norm_r. hss. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. exists r_t2. norm_r. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. unshelve eexists; eauto; ss. norm_r. step_r.
    norm_r. rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired. eauto.
  Qed.

  Lemma gsim_AssumeRes_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_s r_s2 :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (AssumeRes r_s2);;; k));; k_2 x) →
    (✓ (r_s2 ⋅ r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_s))
          (Any.pair st_s ((r_s2 ⋅ r_s)↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_l; rewrite Hin; ss.
    step_l; ss. norm_l. hss. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. intros Hval. norm_l. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    eapply Hk; done.
  Qed.

  Lemma gsim_AssumeRes_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_t r_t2 :
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (AssumeRes r_t2);;; k));; k_2 x) →
    (✓ (r_t2 ⋅ r_t) ∧
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_t))
        (Any.pair st_t ((r_t2 ⋅ r_t)↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair st_t (r_t↑))).
  Proof.
    intros Hin [Hval Hk]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_r; rewrite Hin; ss.
    step_r; ss. norm_r. hss. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. exists Hval. norm_r. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    apply Hk; done.
  Qed.

  Lemma gsim_Guarantee_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_s P :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Guarantee P);;; k));; k_2 x) →
    (∃ r_s2, (✓ r_s2 ∧ (Own r_s ⊢ |==> P ∗ Own r_s2)) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hin [r_s2 [Hr_s2 Hk]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_l; rewrite Hin; ss.
    step_l; ss. norm_l. hss. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. exists r_s2. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. unshelve eexists; eauto. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. norm_l.
    rewrite list_insert_insert //=. ired.
    eapply Hk; done.
  Qed.

  Lemma gsim_Guarantee_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_t P :
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Guarantee P);;; k));; k_2 x) →
    (∀ r_t2, (✓ r_t2 ∧ (Own r_t ⊢ |==> P ∗ Own r_t2)) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair st_t (r_t↑))).
  Proof.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_r; rewrite Hin; ss.
    step_r; ss. norm_r. hss. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. intros r_t2. norm_r. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. intros Hr_t2. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. norm_r.
    rewrite list_insert_insert //=. ired.
    apply Hk; done.
  Qed.

  Context (sp : sp_type).

  Lemma HoareCall_prologue_sred img_c fsp arg :
    ⇓smod(img_c, sp) (HoareCall_prologue fsp arg) = HoareCall_prologue fsp arg.
  Proof.
    rewrite /HoareCall_prologue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareCall_epilogue_sred img_c fsp arg x :
    ⇓smod(img_c, sp) (HoareCall_epilogue fsp x arg) = HoareCall_epilogue fsp x arg.
  Proof.
    rewrite /HoareCall_epilogue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareFun_prologue_sred img_c fsp arg :
    ⇓smod(img_c, sp) (HoareFun_prologue fsp arg) = HoareFun_prologue fsp arg.
  Proof.
    rewrite /HoareFun_prologue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareFun_epilogue_sred img_c fsp arg x :
    ⇓smod(img_c, sp) (HoareFun_epilogue fsp x arg) = HoareFun_epilogue fsp x arg.
  Proof.
    rewrite /HoareFun_epilogue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma gsim_HoareCall_prologue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) arg :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_prologue fsp arg;; k_s x));; k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_prologue fsp arg;; k_t x));; k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_s x));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_t x));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue; unseal "Help". ss. step_r; ss. }
    { revert Hin_s Hin_t; rewrite /HoareCall_prologue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      specialize (Hk res ((), arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue; unseal "Help". ss.
      step_r; intros fsp2; step_l; exists fsp2. step_l; step_r. norm_l; norm_r. ired.
      eapply gsim_Choose_tgt; [rewrite list_lookup_insert; grind|]. intros varg.
      rewrite list_insert_insert.
      eapply gsim_Choose_src; [rewrite list_lookup_insert; grind|]. exists varg.
      rewrite list_insert_insert. ired.
      eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert; grind|]. intros r_t2 Hr_t2.
      rewrite list_insert_insert.
      eapply gsim_Guarantee_src; [rewrite list_lookup_insert; grind|]. exists r_t2; split; ss.
      rewrite list_insert_insert. ired.
      guclo flagC_spec; econs; last eapply (Hk r_t2 (fsp2, varg)).
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      by des.
    }
  Qed.

  Lemma gsim_HoareCall_epilogue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) arg x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_epilogue fsp arg x;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_epilogue fsp arg x;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_s x));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_t x));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue; unseal "Help". ss. step_r; ss. }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      specialize (Hk res x Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      eapply gsim_Take_src; [rewrite Hin_s //|intros y ?].
      eapply gsim_Take_tgt; [rewrite Hin_t //|eexists y; eauto].
      split; first done. ired.
      eapply gsim_Assume_src; [rewrite list_lookup_insert //|].
      intros res2 -> Hres2.
      eapply gsim_Assume_tgt; [rewrite list_lookup_insert //|].
      exists res2; splits; try by des.
      rewrite ?list_insert_insert.
      guclo flagC_spec; econs; last eapply (Hk res2).
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      by des.
    }
  Qed.

  Lemma gsim_HoareCall_epilogue_HoareFun_prologue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) pret x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareCall_epilogue fsp x pret;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareFun_prologue fsp pret;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_s ret));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_t (x, ret)));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue /HoareFun_prologue; unseal "Help".
      ss. step_r; ss.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue /HoareFun_prologue; unseal "Help"; ired.
      intros Hin_s Hin_t. destruct x.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue /HoareFun_prologue; unseal "Help".
      ss.
      step_l. intros varg. norm_l. step_l. norm_l. ired.
      step_r. exists x. norm_r. step_r. norm_r. ired.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //|exists varg; split; first eauto].
      rewrite list_insert_insert.

      eapply gsim_Assume_src; [rewrite list_lookup_insert //|].
      intros r_s2 _ Hr_s2. rewrite list_insert_insert. ired.
      eapply gsim_Assume_tgt; [rewrite list_lookup_insert //|].
      exists r_s2; esplits; try by (des; eauto). rewrite list_insert_insert.
      
      guclo flagC_spec; econs.
      { instantiate (1:=p_s). destruct p_s as [[|]|]; rr; ss; eauto. }
      { instantiate (1:=p_t). destruct p_t as [[|]|]; rr; ss; eauto. }
      eapply Hk; by des.
    }
  Qed.

  Lemma gsim_HoareCall_prologue_HoareFun_epilogue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) pret x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareCall_prologue fsp pret;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareFun_epilogue fsp x pret;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_s (x, ret)));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_t ret));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue /HoareFun_epilogue; unseal "Help".
      ss. step_r; ss.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_prologue /HoareFun_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t. destruct x.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue /HoareFun_epilogue; unseal "Help".
      ss.
      step_r. intros vret. norm_r. step_r. norm_r. ired.
      step_l. exists x. norm_l. step_l. norm_l. ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|exists vret; split; first eauto].
      rewrite list_insert_insert.

      eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //|].
      intros r_t2 Hr_t2. rewrite list_insert_insert. ired.
      eapply gsim_Guarantee_src; [rewrite list_lookup_insert //|].
      exists r_t2; esplits; try by (des; eauto). rewrite list_insert_insert.
      
      guclo flagC_spec; econs.
      { instantiate (1:=p_s). destruct p_s as [[|]|]; rr; ss; eauto. }
      { instantiate (1:=p_t). destruct p_t as [[|]|]; rr; ss; eauto. }
      eapply Hk; by des.
    }
  Qed.

  Lemma gsim_jobs_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) job :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) (k_s ())));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) (k_t ())));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) (x <- Helping.trans job;; k_s x)));; k_s1 x]>
        tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) (x <- Helping.trans job;; k_t x)));; k_t1 x]>
        tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hlen_s Hlen_t Hres Hk.
    apply gsim_flag.
    revert Hres; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres.
    ides job.
    {
      destruct r1.
      rewrite /Helping.trans (bisim_is_eq (translate_ret _ _)); grind.
      eapply gpaco7_mon; eauto.
    }
    {
      rewrite /Helping.trans (bisim_is_eq (translate_tau _ _)); fold (Helping.trans t).
      ired.
      eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
      { rewrite interpV_tau //. }
      eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
      { rewrite interpV_tau //. }
      zprogress.
      apply gsim_flag.
      gbase. eapply CIH; eauto using list_lookup_insert.
    }
    { (* agE *)
      destruct e as [|].
      { destruct a as [P | res2 | P].
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Assume_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros r_s2 -> Hr_s2.
          eapply gsim_Assume_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          exists r_s2; esplits; try by des.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
          by des.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros Hres2.
          eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          split; first done.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros r_t2 Hr_t2.
          eapply gsim_Guarantee_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          exists r_t2; split; first done.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
          by des.
        }
      }
      { (* coreE *)
        destruct c as [X | X | fn args].
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Choose_tgt;
            [rewrite list_lookup_insert //=|intros x; rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //=|exists x; rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Take_src;
            [rewrite list_lookup_insert //=|intros x; rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          intros Himg.
          eapply gsim_Take_tgt;
            [rewrite list_lookup_insert //=|exists x; rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          split; first done. zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { iter_l. rewrite list_lookup_insert //=.
          iter_r. rewrite list_lookup_insert //=.
          norm_l; norm_r.
          guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
          intros ?? ->.
          step_l; step_r. norm_l; norm_r. rewrite ?list_insert_insert. ired.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
      }
    }
  Unshelve. exact smj_top.
  Qed.
End props.

Ltac unfold_trans :=
  rewrite /ModTr.trans_ktree /SB.sandbox_body /SB.sandbox
    /ModTr.trans /SModTr.trans_ktree /SModTr.trans /=.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.
  (* sp, module name for the helping module *)
  Context (sp : sp_type) (mn : string).
  Context (Hyield : sp SchHdr.yield = None ∨ ∃ E, sp SchHdr.yield = Some (SchA.yield_spec E)).
  Context `{jobID} (jobs : jobID → itree Helping.pureE unit).
  Context (msk : string → bool). (* mask for the user module *)

  Definition mod_on :=  (HelpingOn.t mn jobs sp)  ★ (CFilter.filter msk SchI.t).
  Definition mod_off := (HelpingOff.t mn jobs sp) ★ (CFilter.filter msk SchI.t).

  Lemma get_tid_run_neq : SchHdr.get_tid ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.run; destruct (decide (String.length mn = 7)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma get_tid_help_neq : SchHdr.get_tid ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.help; destruct (decide (String.length mn = 6)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_run_neq : SchHdr.yield ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.yield /Helping.run; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_help_neq : SchHdr.yield ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.yield /Helping.help; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (0 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_run_neq : SchHdr.join ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.join /Helping.run; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_help_neq : SchHdr.join ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.join /Helping.help; destruct (decide (String.length mn = 3)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Notation prog_s ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOff.Mod mn jobs)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).
  Notation prog_t ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOn.Mod mn jobs sp)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).

  Definition run_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOff.run jobs x))).
  Definition run_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOn.run mn jobs x))).

  Definition help_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOff.help x))).
  Definition help_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOn.help mn jobs sp x))).

  Definition yield : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.yield x))).
  Definition inner_spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.inner_spawn x))).
  Definition spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.spawn x))).
  Definition join : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.join x))).
  Definition get_tid : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.get_tid x))).

  Lemma no_help_prog fn ctx rs :
    fn ≠ Helping.run mn →
    fn ≠ Helping.help mn →
    prog_s ctx rs fn = prog_t ctx rs fn.
  Proof.
    intros ??.
    rewrite /LMod.prog /=;
    repeat (
      match goal with
      | |- context [dec ?a ?b] => destruct (dec a b); ss; clarify
      end); esplits; eauto.
  Qed.

  Lemma prog_fn fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    (fn = Helping.run mn ∧ prog_s ctx rs fn = Some run_s ∧ prog_t ctx rs fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs fn = Some help_s ∧ prog_t ctx rs fn = Some help_t) ∨
    prog_s ctx rs fn = prog_t ctx rs fn ∧
    ((fn = SchHdr.yield ∧ prog_s ctx rs fn = Some yield) ∨
     (fn = SchHdr.join ∧ prog_s ctx rs fn = Some join) ∨
     (fn = SchHdr._spawn ∧ prog_s ctx rs fn = Some inner_spawn) ∨
     (fn = SchHdr.spawn ∧ prog_s ctx rs fn = Some spawn) ∨
     (fn = SchHdr.get_tid ∧ prog_s ctx rs fn = Some get_tid) ∨
     (Some fn ∉ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))) ∧
     (prog_s ctx rs fn = None ∨
     ∃ itr_ctx img1 msk1 scp1, (prog_s ctx rs fn =
      Some (λ x, ⇓cris (⇓sb(img1, msk1, scp1) (itr_ctx x))) ∧
      (scp1 ## (SchI.scopes ++ HelpingOff.scopes mn)))))).
  Proof.
    intros WF.
    destruct (decide (fn = Helping.run mn)).
    { subst; left.
      rewrite /LMod.prog /=; destruct (dec _ _); last clarify; ss.
    }
    destruct (decide (fn = Helping.help mn)).
    { subst; right; left.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; clarify; ss.
      { rewrite /Helping.help /Helping.run in e; inv e. }
      destruct (dec _ _); clarify; ss.
    }
    right; right. split; first apply no_help_prog; eauto.
    destruct (decide (fn = SchHdr.yield)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.join)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr._spawn)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.spawn)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.get_tid)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; ss; eauto; clarify; ss.
    }
    right.
    rewrite /LMod.prog /=.
    repeat (destruct (dec _ _) as [e|e]; ss; [inv e; by clarify|clear e]).
    rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
    split.
    { set_solver. }
    rewrite alist_find_map_snd.
    destruct (alist_find (Some fn) (Mod.fnsems ctx)) as [[[[img1 msk1] scp1] itr_fn]|] eqn : Hfn.
    { right; ss. esplits; eauto; ss.
      hexploit (Mod.well_scoped_fns ctx (Some fn)); ss.
      rewrite /fnsems_scopes Hfn /=; intros Hin.
      apply elem_of_disjoint; intros x Hinctx%elem_of_list_In%Hin%elem_of_list_In Hinsch.
      hexploit (Mod.wf_scopes); eauto; rewrite /Mod.scopes /=.
      intros Hnodup; eapply (NoDup_app_disjoint _ _ Hnodup x); eauto.
      { eapply elem_of_list_In. rewrite /Mod.scopes /SchI.t /HelpingOn.t; unseal CRIS; ss.
        revert Hinsch; rewrite /HelpingOn.scopes /SchI.scopes; ss.
        set_solver.
      }
      { eapply elem_of_list_In, Hinctx; eauto. }
    }
    left; ss.
  Qed.

  Lemma prog_fn_ctx fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    (Some fn ∉ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t)))) →
    (prog_s ctx rs fn = None ∨
     ∃ itr_ctx img1 msk1 scp1,
      prog_t ctx rs fn = prog_s ctx rs fn ∧
      prog_s ctx rs fn =
        Some (λ x, ⇓cris (⇓sb(img1, msk1, scp1) (itr_ctx x))) ∧
        (scp1 ## (SchI.scopes ++ HelpingOff.scopes mn))).
  Proof.
    intros ? NIN; hexploit (prog_fn fn ctx rs); eauto; intros CASE.
    revert NIN; rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|[-> CASE]]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    i; des; eauto. right; esplits; eauto.
  Qed.

  Lemma prog_s_prog_t fn ctx rs itr :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    prog_s ctx rs fn = Some itr →
    (prog_t ctx rs fn = Some itr ∨
     (fn = Helping.run mn ∧ itr = run_s ∧ prog_t ctx rs fn = Some run_t) ∨
     (fn = Helping.help mn ∧ itr = help_s ∧ prog_t ctx rs fn = Some help_t)).
  Proof.
    intros ? Hs; hexploit (prog_fn fn ctx rs); eauto.
    i; des; clarify; eauto; left; rewrite -H3 //.
  Qed.

  Lemma yield_unfold :
    @Sch.yield crisE _ _ =
    tau;; b <- trigger (Choose (option bool));;
    match b with
    | None => Ret tt
    | Some false => Sch.yield
    | Some true => trigger (Call SchHdr.yield tt↑);;; Sch.yield
    end.
  Proof.
    rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
    repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
    { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. done. }
  Qed.

  Definition reqmap_rel
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (bool * jobID))))
      (reqmap : gmap nat (bool * jobID)) : Prop :=
    NoDup (omap id tl.*2).*1 ∧
    (∀ stid rid jid b,
      (tl.*2 !! stid = Some (Some (rid, (b, jid))) → reqmap !! rid = Some (b, jid))) ∧
    (∀ rid jid, reqmap !! rid = Some (true, jid) →
      ∃ stid, tl.*2 !! stid = Some (Some (rid, (true, jid)))).

  Lemma reqmap_rel_id stid es0 es1 r tl reqmap :
    tl !! stid = Some (es0, r) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, r)]> tl) reqmap.
  Proof.
    intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
    rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
    rewrite ?omap_app ?fmap_app; cbn; destruct r; eauto.
  Qed.

  Lemma reqmap_rel_Some tl reqmap stid rid b jid es :
    tl !! stid = Some (es, Some (rid, (b, jid))) →
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (b, jid).
  Proof.
    rewrite /reqmap_rel; intros Hin [Hnodup [Hrel1 Hrel2]].
    apply (Hrel1 stid rid jid b). rewrite list_lookup_fmap Hin; eauto.
  Qed.

  Lemma reqmap_rel_Some_2 tl reqmap (i_s i_t : itree lmodE Any.t) rid jid :
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (true, jid) →
    ∃ stid i_s i_t, tl !! stid = Some (i_s, i_t, Some (rid, (true, jid))).
  Proof.
    rewrite /reqmap_rel; intros [? [? Hsome]] [stid Hstid]%Hsome; exists stid.
    apply list_lookup_fmap_inv in Hstid as [[[? ?] [[? [? ?]]|]] [? ?]]; ss.
    clarify; esplits; eauto.
  Qed.

  Lemma reqmap_rel_delete_true tl stid rid jid es0 es1 reqmap :
    tl !! stid = Some (es0, Some (rid, (true, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (<[rid := (false, jid)]> reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app ?fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert // in Hstid1. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_true_2 tl stid rid jid es0 es1 reqmap :
    tl !! stid = Some (es0, Some (rid, (true, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, Some (rid, (false, jid)))]> tl) (<[rid := (false, jid)]> reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      revert Hnodup; rewrite ?fmap_app ?omap_app ?fmap_app //; cbn.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert //= in Hstid1; clarify. rewrite lookup_insert //. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_false tl stid rid jid es0 es1 reqmap :
    tl !! stid = Some (es0, Some (rid, (false, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]].
    split.
    { revert Hin; intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid' ??? Hstid'; eapply (Hrel1 stid'); eauto.
      rewrite list_fmap_insert /= in Hstid'.
      apply lookup_lt_Some in Hstid' as Hlen'. rewrite length_insert in Hlen'.
      destruct (decide (stid = stid')); subst.
      { rewrite list_lookup_insert // in Hstid'; ss. }
      rewrite list_lookup_insert_ne // in Hstid'.
    }
    intros ?? [stid' Hlookup]%Hrel2; exists stid'.
    rewrite list_fmap_insert /= list_lookup_insert_ne ?Hlookup //.
    ii; clarify.
    rewrite list_lookup_fmap Hin //= in Hlookup.
  Qed.

  Lemma reqmap_rel_insert_false tl reqmap rid jid :
    rid ∉ (dom reqmap) →
    reqmap_rel tl reqmap →
    reqmap_rel tl (<[rid:=(false, jid)]> reqmap).
  Proof.
    intros Hrid [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ???? Hstid%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify; apply elem_of_dom_2 in Hstid; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    ii; clarify.
  Qed.

  Lemma reqmap_rel_insert_true tl reqmap stid es0 es1 rid jid :
    rid ∉ (dom reqmap) →
    tl !! stid = Some (es0, None) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, Some (rid, (true, jid)))]> tl) (<[rid:=(true, jid)]> reqmap).
  Proof.
    intros Hrid Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { rewrite insert_take_drop //.
      rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
      rewrite cons_app Permutation_app_swap_app.
      eapply take_drop_middle in Hin as Hmid; rewrite -Hmid in Hnodup; clear Hmid.
      revert Hnodup; rewrite ?fmap_app ?omap_app fmap_app; cbn.
      intros ?; apply NoDup_cons; split; eauto.
      rewrite -fmap_app -omap_app -fmap_app.
      intros [[? [? ?]] [? Hrid2]]%elem_of_list_fmap; ss; clarify.
      apply elem_of_list_omap in Hrid2 as [[[? [? ?]] |] [Hrid2 ?]]; ss; clarify.
      apply elem_of_list_fmap in Hrid2 as [[? [[? [? ?]] |]] [? Hrid2]]; ss; clarify.
      apply Hrid, elem_of_dom.
      assert (Hlem : (p, Some (n0, (b0, j0))) ∈ tl).
      { eapply take_drop_middle in Hin as Hmid; rewrite -Hmid; clear Hmid. set_solver. }
      apply elem_of_list_lookup in Hlem as [i Hlem].
      hexploit (Hrel1 i); cycle 1.
      { intros ->; ss. }
      rewrite list_lookup_fmap Hlem //.
    }
    split.
    { intros stid1 ? ? ?; destruct (decide (stid1 = stid)); subst.
      { rewrite list_lookup_fmap list_lookup_insert /=; i; clarify; rewrite lookup_insert //. }
      rewrite list_fmap_insert list_lookup_insert_ne //; intros Hcont%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify.
      apply Hrid, elem_of_dom; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    { ii; clarify. exists stid; rewrite list_fmap_insert list_lookup_insert // length_fmap //. }
    intros ? [??]%Hrel2; exists x; rewrite list_fmap_insert list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in H2; clarify.
  Qed.

  Lemma reqmap_rel_append tl reqmap es :
    reqmap_rel tl reqmap →
    reqmap_rel (tl ++ [(es, None)]) reqmap.
  Proof.
    rewrite /reqmap_rel ?fmap_app ?omap_app ?fmap_app app_nil_r; cbn.
    intros [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ????; rewrite lookup_app_Some; intros [?%Hrel1|[??%list_lookup_singleton_Some]]; eauto.
      des; clarify.
    }
    { intros ?? [stid Hstid]%Hrel2; apply lookup_lt_Some in Hstid as Hlen.
      exists stid; rewrite lookup_app_l //.
    }
  Qed.

  Definition inner_spawn_pend (arg : Any.t) ktr : itree lmodE Any.t :=
    tau;;
    x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (⇓smod(false, sp_none) (
        'arg : SAny.t <- (arg↓)?;;
        'x1 : thpool <- (cgetU SchI.v_ths);;
        'x2 : nat <- (cgetU SchI.v_tid);;
        r <-
          (match x1 !! x2 with
          | Some (stid, _) =>
              cput SchI.v_ths (<[x2 := (stid, Some arg)]> x1);;;
              Sch.terminate
          | None => triggerUB
          end);;
        Ret (r↑))));;
    ktr x.

  Definition join_pend (arg : Any.t) stid ktr : itree lmodE Any.t :=
    tau;;
    x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (⇓smod(false, sp_none) (
        'arg : () <- (arg↓)?;;
        x_3 <- iterC (λ _ : (),
          'x_1 : thpool <- cgetU SchI.v_ths;;
          match x_1 !! stid with
          | Some (_, Some rv) => Ret (inr (Some rv))
          | Some (_, None) =>
              '() : _ <- ccallU SchHdr.yield tt;; Ret (inl ())
          | None => Ret (inr None)
          end
        ) ();;
        Ret (x_3↑))));;
    ktr x.

  Definition helpee_pend_s
      (j : jobID) k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; Helping.trans (jobs j);;; 𝒴;;; Ret ()↑)
    ));;
     (k r).

  Definition helpee_pend_t
      (tid_stid_cur : nat) (j : jobID) k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; HelpingOn.try_run mn jobs tid_stid_cur;;; 𝒴;;; Ret (()↑))
    ));; (k r).

  Inductive help_rel : itree lmodE Any.t → itree lmodE Any.t → option (nat * (bool * jobID)) → Prop :=
  | help_rel_ret ret : help_rel (Ret ret) (Ret ret) None
  | help_rel_eq itr_s itr_t (k_s k_t : Any.t → _) itr img msk scp :
      itr_t = ModTr.trans (SB.sandbox img msk scp itr) >>= k_t →
      itr_s = ModTr.trans (SB.sandbox img msk scp itr) >>= k_s →
      scp ## (SchI.scopes ++ HelpingOff.scopes mn) →
      (∀ ret, itr ≠ Ret ret) →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_loop itr_s itr_t ktr_t ktr_s x :
      itr_t = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
        ktr_t x_) →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
        ktr_s x_) →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_helpee_done tid jid itr_s itr_t x k_s k_t :
      itr_t = helpee_pend_t tid jid k_t (sp SchHdr.yield) x →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
        k_s x_) →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t (Some (tid, (false, jid)))
  | help_rel_helpee_pend tid jid itr_s itr_t k_s k_t x_fsp :
      itr_s = helpee_pend_s jid k_s (sp SchHdr.yield) x_fsp →
      itr_t = helpee_pend_t tid jid k_t (sp SchHdr.yield) x_fsp →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t (Some (tid, (true, jid)))
  | help_rel_call itr_s itr_t ktr_t ktr_s ktr_t1 ktr_s1 ctx rs fn arg :
      Some fn ∈ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))) →
      Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
      prog_t ctx rs fn = Some ktr_t →
      prog_s ctx rs fn = Some ktr_s →
      itr_t = ktr_t arg >>= ktr_t1 →
      itr_s = ktr_s arg >>= ktr_s1 →
      (∀ ret, help_rel (ktr_s1 ret) (ktr_t1 ret) None) →
      help_rel itr_s itr_t None
  | help_rel_inner_spawn itr_s itr_t (arg : Any.t) ktr_s ktr_t :
      itr_t = inner_spawn_pend arg ktr_t →
      itr_s = inner_spawn_pend arg ktr_s →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_join itr_s itr_t (arg : Any.t) ktr_s ktr_t tid :
      itr_t = join_pend arg tid ktr_t →
      itr_s = join_pend arg tid ktr_s →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_terminate itr_s itr_t ktr_s ktr_t :
      itr_s =
        (x <- ⇓cris (⇓sb( false, wmask_and msk wmask_all, SchI.scopes)
          (⇓smod( false, sp_none) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_s x) →
      itr_t =
        (x <- ⇓cris (⇓sb( false, wmask_and msk wmask_all, SchI.scopes)
          (⇓smod( false, sp_none) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_t x) →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None.
End Helping.
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
      [ cong (@SB.sandbox Σ R img imports scopes); _gnorm_itr | red_SB (do 1 _gnorm_itr) ]
  | [ |- @SModTr.trans ?Σ ?sp ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Σ sp R); _gnorm_itr | red_S (do 1 _gnorm_itr) ]
  | [ |- @LModTr.interp_stateE ?E ?T ?itr ?st = _] =>
      etransitivity;
      [ cong (λ i, @LModTr.interp_stateE E T i st); _gnorm_itr | red_LModTr_state (do 1 _gnorm_itr)]
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

Ltac step_r := norm_r; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
Ltac step_l := norm_l; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).

Ltac steps_r :=
  norm_r; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try norm_r)).
Ltac steps_l :=
  norm_l; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try norm_l)).

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
Notation "'⇓sb(' m ')'" := (SB.sandbox m).
Notation "'⇓smod(' sp ',' N ',' stid ')'" := (SModTr.trans sp N stid).

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

  Lemma gsim_tau_src r g RR p_s p_t st_s itr_t prog_s tid_s tp_s k :
    tp_s !! tid_s = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := (⇓cris k)]> tp_s)) st_s)
      itr_t →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof. intros Hi ?. giter_l. s. rewrite Hi; ss. gstep_l. gnorm_l. done. Qed.

  Lemma gsim_tau_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k :
    tp_t !! tid_t = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris k]> tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof. intros Hi ?. giter_r; rewrite /= Hi; ss. gstep_r; gnorm_r. done. Qed.

  Lemma gsim_Choose_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c X k (k2 : Any.t → _) :
    tp_s !! tid_s = Some (x <- ⇓cris (⇓sb(msk_c) (x <- trigger (Choose X);; k x));; k2 x) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := (x <- ⇓cris (⇓sb(msk_c) (k x));; k2 x)]> tp_s)) st_s)
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    rewrite -vis_trigger SBRed.vis; case_match; intros Hi [x Hk]; iter_l; rewrite Hi; ss.
    { step_l. exists x; norm_l. steps_l. ired. done. }
    { step_l. ss. }
  Qed.

  Lemma gsim_Choose_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c X k (k2 : Any.t → _) :
    msk_c _ (subevent _ (Choose X)) = true →
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(msk_c) (x <- trigger (Choose X);; k x));; k2 x) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(msk_c) (k x));; k2 x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    rewrite -vis_trigger SBRed.vis; case_match eqn:Hmsk2; intros Hmsk Hi Hk; ss.
    { iter_r; rewrite Hi; ss. step_r. intros x. steps_r. ired. done. }
    { rewrite Hmsk // in Hmsk2. }
  Qed.

  Lemma gsim_Take_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t X k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k x)]> tp_s)) st_s)
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof. intros Hi ?; giter_l; s. rewrite Hi; ss. gstep_l; i; gstep_l; gnorm_l. ired; done. Qed.

  Lemma gsim_Take_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t X k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := (⇓cris (k x))]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi [x Hk]; ss. giter_r; rewrite /= Hi; ss. gstep_r. exists x. gstep_r. ired. done.
  Qed.

  Lemma gsim_Call_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := bd <- (prog_s fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi Hk.
    giter_l. rewrite /= Hi; ss. gstep_l. ired.
    replace_l; [|apply Hk].
    do 4 f_equal. destruct (prog_s); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Call_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := bd <- (prog_t fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi Hk.
    giter_r. rewrite /= Hi; ss. gstep_r. ired.
    replace_r; [|apply Hk].
    do 4 f_equal. destruct (prog_t); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Spawn_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (bd <- (prog_s fn)?;;
        iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (length tp_s))]> tp_s ++ [bd args])) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof.
    intros Hi Hk.
    giter_l. rewrite /= Hi; ss. gstep_l. ired.
    replace_l; [|apply Hk].
    do 1 f_equal. grind.
  Qed.

  Lemma gsim_Spawn_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (bd <- (prog_t fn)?;;
        iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (length tp_t))]> tp_t ++ [bd args])) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi Hk.
    giter_r. rewrite /= Hi; ss. gstep_r. ired.
    replace_r; [|apply Hk].
    do 1 f_equal. grind.
  Qed.
  (* Lemma gsim_sGet_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c key k (k2 : Any.t → _) r_t :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(msk_c) (x <- trigger (SGet key);; k x));; k2 x) →
    existsb (String.eqb key.1) scp_c →
    (∃ t, alist_find key st_t = Some t ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := (x <- ⇓cris (⇓sb(msk_c) (k t));; k2 x)]> tp_t))
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
  Qed. *)

  Lemma gsim_Assume_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∀ r_s2,
      ✓ r_s2 ∧ (Own r_s2 ⊢ |==> P ∗ Own r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof.
    intros Hi Hk; pose proof Hi as Hlen; eapply lookup_lt_Some in Hlen.
    iter_l; rewrite Hi; ss.
    steps_l. hss. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. intros r_s2.
      steps_l. ired. rewrite list_insert_insert.
    iter_l. rewrite list_lookup_insert //=. step_l. intros Hr_s2.
      steps_l. ired. rewrite list_insert_insert.
    iter_l. rewrite list_lookup_insert //=. step_l.
      steps_l. ired. hss. ired. rewrite list_insert_insert.
    iter_l. rewrite list_lookup_insert //=. step_l.
      steps_l. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_Assume_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∃ r_t2,
      ✓ r_t2 ∧ (Own r_t2 ⊢ |==> P ∗ Own r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof.
    intros Hin [r_t2 [Hr_t2 Hk]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_r; rewrite Hin /=. step_r. steps_r. hss. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. exists r_t2.
      steps_r. rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. unshelve eexists; eauto; ss.
      steps_r. rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. steps_r.
      rewrite list_insert_insert //=. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. steps_r.
      rewrite list_insert_insert //=. ired. eauto.
  Qed.

  Lemma gsim_AssumeRes_src r g RR p_s p_t st_s prog_s tid_s tp_s k r_s r_s2 itr_t :
    tp_s !! tid_s =
      Some (⇓cris (x <- trigger (AssumeRes r_s2);; k x)) →
    (✓ (r_s2 ⋅ r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (Any.pair st_s ((r_s2 ⋅ r_s)↑)))
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      itr_t.
  Proof.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_l; rewrite /= Hin /=. gstep_l; ss. gnorm_l. hss. ired. hss. ired.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      intros Hval. gnorm_l. gstep_l. gnorm_l. rewrite list_insert_insert.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      gnorm_l. ired. hss. ired. rewrite list_insert_insert.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      gnorm_l. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_AssumeRes_tgt r g RR p_s p_t st_t prog_s tid_t tp_t k r_t r_t2 itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (AssumeRes r_t2);; k x)) →
    (✓ (r_t2 ⋅ r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (Any.pair st_t ((r_t2 ⋅ r_t)↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof.
    intros Hin [Hval Hk]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_r; rewrite /= Hin /=. gstep_r; ss. gnorm_r. hss. ired. hss. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gstep_r; ss. exists Hval. gsteps_r. rewrite list_insert_insert. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gsteps_r; ss. rewrite list_insert_insert. ired. hss. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gsteps_r; ss. rewrite list_insert_insert. ired.
    eapply Hk; done.
  Qed.

  (* Lemma gsim_Guarantee_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
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
  Qed. *)

  (* Context (sp : sp_type).

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

  Lemma gsim_jobs_both {retID} r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c img_c' msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) job :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ) (ret : retID), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (k_s ret)));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (k_t ret)));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (x <- Helping.trans job;; k_s x)));; k_s1 x]>
        tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (x <- Helping.trans job;; k_t x)));; k_t1 x]>
        tp_t)) (Any.pair st_t (res↑))).
  Proof.
    intros Hlen_s Hlen_t Hres Hk.
    apply gsim_flag.
    revert Hres; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres.
    ides job.
    {
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
  Qed. *)
End props.

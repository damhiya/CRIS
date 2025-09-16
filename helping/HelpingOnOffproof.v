Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff.

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

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.
  (* sp, module name for the helping module *)
  Context (sp : sp_type) (mn : string).
  Context (Hyield : sp SchHdr.yield = None ∨ ∃ E, sp SchHdr.yield = Some (SchA.yield_spec E)).
  Context `{jobID} (jobs : jobID → itree Helping.pureE unit).
  Context (msk : string → bool). (* mask for the user module *)

  Local Definition mod_on :=  (HelpingOn.t mn jobs sp)  ★ (CFilter.filter msk SchI.t).
  Local Definition mod_off := (HelpingOff.t mn jobs sp) ★ (CFilter.filter msk SchI.t).

  Local Lemma get_tid_run_neq : SchHdr.get_tid ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.run; destruct (decide (String.length mn = 7)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Local Lemma get_tid_help_neq : SchHdr.get_tid ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.help; destruct (decide (String.length mn = 6)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Local Lemma yield_run_neq : SchHdr.yield ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.yield /Helping.run; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Local Lemma yield_help_neq : SchHdr.yield ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.yield /Helping.help; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (0 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Local Lemma join_run_neq : SchHdr.join ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.join /Helping.run; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Local Lemma join_help_neq : SchHdr.join ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.join /Helping.help; destruct (decide (String.length mn = 3)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
  Notation "'⇓sb(' i ',' m ',' s ')'" := (interpV (SB.handle_sandbox i m s)).
  Notation "'⇓smod(' img ',' sp ')'" := (interpV (SModTr.handle img sp)).
  Notation prog_s ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOff.Mod mn jobs)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).
  Notation prog_t ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOn.Mod mn jobs sp)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).

  Local Definition run_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOff.run jobs x))).
  Local Definition run_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOn.run mn jobs x))).

  Local Definition help_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOff.help x))).
  Local Definition help_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(true, sp) (HelpingOn.help mn jobs sp x))).

  Local Definition yield : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.yield x))).
  Local Definition inner_spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.inner_spawn x))).
  Local Definition spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.spawn x))).
  Local Definition join : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.join x))).
  Local Definition get_tid : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.get_tid x))).

  Local Lemma no_help_prog fn ctx rs :
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

  Local Lemma prog_fn fn ctx rs :
    (fn = Helping.run mn ∧ prog_s ctx rs fn = Some run_s ∧ prog_t ctx rs fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs fn = Some help_s ∧ prog_t ctx rs fn = Some help_t) ∨
    prog_s ctx rs fn = prog_t ctx rs fn ∧
    ((fn = SchHdr.yield ∧ prog_s ctx rs fn = Some yield) ∨
     (fn = SchHdr.join ∧ prog_s ctx rs fn = Some join) ∨
     (fn = SchHdr._spawn ∧ prog_s ctx rs fn = Some inner_spawn) ∨
     (fn = SchHdr.spawn ∧ prog_s ctx rs fn = Some spawn) ∨
     (fn = SchHdr.get_tid ∧ prog_s ctx rs fn = Some get_tid) ∨
     Some fn ∉ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t)))).
  Proof.
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
    right. rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss; set_solver.
  Qed.

  Lemma prog_s_prog_t fn ctx rs itr :
    prog_s ctx rs fn = Some itr →
    (prog_t ctx rs fn = Some itr ∨
     (fn = Helping.run mn ∧ itr = run_s ∧ prog_t ctx rs fn = Some run_t) ∨
     (fn = Helping.help mn ∧ itr = help_s ∧ prog_t ctx rs fn = Some help_t)).
  Proof.
    intros Hs; hexploit (prog_fn fn ctx rs); i; des; clarify; eauto; try by (left; rewrite -H2 //).
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

  Definition reqlist_all
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (bool * nat * jobID)))
      : list (bool * nat * jobID) :=
    omap id tl.*2.

  Definition reqmap
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (bool * nat * jobID)))
      : gmap nat jobID :=
    list_to_map
      (omap (λ '(b, rid, jid), if b : bool then Some (rid, jid) else None) (reqlist_all tl)).

  Lemma NoDup_reqlist tl :
    NoDup (reqlist_all tl).*1.*2 →
    NoDup (omap (λ '(b, rid, jid), if b : bool then Some (rid, jid) else None) (reqlist_all tl)).*1.
  Proof.
    induction tl as [|[[??][[[[|]?]?]|]]]; first (ii; ss; econs); eauto.
    { rewrite /reqlist_all fmap_cons; cbn. intros Hnodup; inv Hnodup.
      econs; eauto. intros [[? ?] [? Hin%elem_of_list_omap]]%elem_of_list_fmap_2.
      destruct Hin as [[[[|] ?] ?] [Hin' Hin]]; ss; clarify.
      eapply H4. eapply (elem_of_list_fmap_1 fst) in Hin'; ss.
      eapply (elem_of_list_fmap_1 snd) in Hin'; ss.
    }
    { rewrite /reqlist_all fmap_cons; cbn. intros Hnodup; inv Hnodup.
      eapply IHtl; eauto.
    }
  Qed.

  Definition yield_epliogue (tid_cur : nat) : itree lmodE Any.t :=
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none) (
        x <- cput SchI.SchI.v_tid tid_cur;;
        Ret (x↑)
    ))).

  Definition helpee_pend_s
      (tid_cur : nat) (j : jobID) img_c msk_c scp_c k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; Helping.trans (jobs j);;; 𝒴;;; Ret ()↑)
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  Definition helpee_pend_t
      (tid_cur tid_stid_cur : nat) (j : jobID) img_c msk_c scp_c k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; HelpingOn.try_run mn jobs tid_stid_cur;;; 𝒴;;; Ret (()↑))
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  Inductive help_rel : itree lmodE Any.t → itree lmodE Any.t → option (bool * nat * jobID) → Prop :=
  | help_rel_eq itr_s itr_t itr img msk scp :
      itr_t = itr_s →
      itr_s = ModTr.trans (SB.sandbox img msk scp itr) →
      scp ## (SchI.scopes ++ HelpingOff.scopes mn) →
      help_rel itr_s itr_t None
  | help_rel_helper itr_s itr_t img msk scp x k :
      itr_t = itr_s →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
        tau;; ⇓cris(⇓sb(img, msk, scp) (k x_))) →
      scp ## (SchI.scopes ++ HelpingOff.scopes mn) →
      help_rel itr_s itr_t None
  | help_rel_helpee_done tid_cur tid jid itr_s itr_t img msk scp x k :
      itr_t = helpee_pend_t tid_cur tid jid img msk scp k (sp SchHdr.yield) x →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
        tau;; ⇓cris(⇓sb(img, msk, scp) (k x_))) →
      scp ## (SchI.scopes ++ HelpingOff.scopes mn) →
      help_rel itr_s itr_t (Some (false, tid, jid))
  | help_rel_helpee_pend tid jid itr_s itr_t tid_cur img_c msk_c scp_c k x_fsp :
      itr_s = helpee_pend_s tid_cur jid img_c msk_c scp_c k (sp SchHdr.yield) x_fsp →
      itr_t = helpee_pend_t tid_cur tid jid img_c msk_c scp_c k (sp SchHdr.yield) x_fsp →
      scp_c ## (SchI.scopes ++ HelpingOff.scopes mn) →
      help_rel itr_s itr_t (Some (true, tid, jid))
  | help_rel_call itr_s itr_t ktr_t ktr_s ktr_t1 ktr_s1 ctx rs fn arg :
      prog_t ctx rs fn = Some ktr_t →
      prog_s ctx rs fn = Some ktr_s →
      itr_t = ktr_t arg >>= ktr_t1 →
      itr_s = ktr_s arg >>= ktr_s1 →
      (∀ ret, help_rel (ktr_s1 ret) (ktr_t1 ret) None) →
      help_rel itr_s itr_t None.
(* 
  Definition help_rel
      (itr_s itr_t : itree lmodE Any.t) (no : option (nat * jobID)) : Prop :=
    match no with
    | None =>
        ∃ itr img msk scp,
          (itr_s = itr_t ∧ itr_s = ModTr.trans (SB.sandbox img msk scp itr) ∨
          ∃ x k,
            itr_s = tau;;
              x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
                (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                ⇓smod(true, sp) (Ret x_2;;; 𝒴;;; Ret (()↑))));;
              tau;; ⇓cris(⇓sb(img, msk, scp) (k x_)) ∧
            (itr_t = itr_s ∨
            itr_t = tau;;
              x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
                (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                ⇓smod(true, sp) (Ret x_2;;;
                  𝒴;;; HelpingOn.try_run mn jobs tid_stid_cur;;; Ret (()↑))));;
              tau;; ⇓cris(⇓sb(img, msk, scp) (k x_))))
    | Some (tid, jid) =>
        ∃ tid_cur img_c msk_c scp_c k x_fsp,
          itr_s = helpee_pend_s tid_cur jid img_c msk_c scp_c k (sp SchHdr.yield) x_fsp ∧
          itr_t = helpee_pend_t tid_cur tid jid img_c msk_c scp_c k (sp SchHdr.yield) x_fsp (* pending *)
    end. *)

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
  (* Proof. intros Hi ?. iter_l; rewrite Hi; ss. step_l; norm_l. done. Qed. *)
  Admitted.

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
  (* Proof. intros Hi ?. iter_r; rewrite Hi; ss. step_r; norm_r. done. Qed. *)
  Admitted.

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
  Admitted.
(* 
  Proof.
    intros Hi [x Hk]. iter_l; rewrite Hi; ss. step_l. exists x. norm_l. step_l. norm_l. ired. done.
  Qed. *)

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
  Admitted.
  (* Proof.
    intros Hi Hk. iter_r; rewrite Hi; ss. step_r. intros x. norm_r. step_r. norm_r. ired. eapply Hk.
  Qed. *)

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
  Admitted.
  (* Proof.
    intros Hin Hk. iter_l. rewrite Hin; ss.
    destruct img_c; norm_l; cycle 1.
    { destruct (excluded_middle_informative _) as [?|?]; des; clarify; ss; step_l; ss.
      intros x; step_l; ired. norm_l. eapply Hk; right; eauto.
    }
    step_l. intros x. norm_l. step_l. norm_l. ired.
    eapply Hk; eauto.
  Qed. *)

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
  Admitted.
  (* Proof.
    intros Hi [x [Hx Hk]].
    iter_r; rewrite Hi; ss.
    destruct (orb _ _) eqn : E; ss; simpl_bool; cycle 1.
    { des; clarify; ss. destruct (excluded_middle_informative _); ss.
      exfalso; apply n; eexists; eauto.
    }
    norm_r. step_r. exists x. step_r. norm_r. ired. eapply Hk.
  Qed. *)

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
  Admitted.
  (* Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_r; rewrite Hin; ss.
    rewrite Hkey /=.
    norm_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode Ht /=. ired. eapply Hk.
  Qed. *)

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
  (* Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_l; rewrite Hin; ss.
    rewrite Hkey /=.
    norm_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode Ht /=. ired. eapply Hk.
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Qed. *)
  Admitted.

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
  (* Proof.
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
  Admitted.

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
  Admitted.
  (* Proof.
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
  Qed. *)

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
  Admitted.
  (* Proof.
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
  Qed. *)

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
  Admitted.
  (* Proof.
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
  Qed. *)

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
  Admitted.
  (* Proof.
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
  Qed. *)

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
  Admitted.
  (* Proof.
    intros Hlen_s Hlen_t Hres Hk.
    guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
      guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
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
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { iter_l. rewrite list_lookup_insert //=.
          iter_r. rewrite list_lookup_insert //=.
          norm_l; norm_r.
          guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
          intros ?? ->.
          step_l; step_r. norm_l; norm_r. rewrite ?list_insert_insert. ired.
          zprogress.
          guclo flagC_spec; econs; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
      }
    }
  Unshelve. exact smj_top.
  Qed. *)

  Lemma gsim_Yield_both r g RR p_s p_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) ctx rs
      (ths : list (nat * option SAny.t)) (tid_cur_s tid_cur_t : nat) st_ctx (res : Σ) reqs :
    ✓ res →
    tid_s < length tp_s →
    tid_t < length tp_t →
    gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) k_s));; k_s1 x]>
            tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) k_t));; k_t1 x]>
            tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))) →
    ((∃ ro_s, ths !! tid_cur_s = Some (tid_s, ro_s)) →
      ∃ ro_t, ths !! tid_cur_t = Some (tid_t, ro_t) ∧
      (∀ mtidn_t stidn_t, ths.*1 !! mtidn_t = Some stidn_t →
        ∃ mtidn_s stidn_s, ths.*1 !! mtidn_s = Some stidn_s ∧
          ∀ (res1 : Σ) x, ✓ res1 →
          gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_s ctx rs))
                (stidn_s, <[tid_s := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c, sp) (Ret x_2;;; 𝒴;;; k_s))));; k_s1 x_]> tp_s))
              (Any.pair
                (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_s ↑)) :: st_ctx))
                (res1 ↑)))
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_t ctx rs))
                (stidn_t, <[tid_t := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c, sp) (Ret x_2;;; 𝒴;;; k_t))));; k_t1 x_]> tp_t))
              (Any.pair
                (ModTr.alist_encode
                  ((HelpingOn.v_reqs mn, reqs)
                  :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_t ↑)) :: st_ctx))
                (res1 ↑))))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp)(𝒴;;; k_s)));;
            k_s1 x]> tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c, sp) (𝒴;;; k_t)));;
            k_t1 x]> tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))).
  Admitted.
  (* Proof.
    intros Hres Hlen_s Hlen_t Hk1 Hk2; revert Hk1; rewrite yield_unfold; ired.
    revert res Hres.
    gcofix CIH.
    intros res Hres Hk1.
    replace_r; [rewrite interpV_tau //|].
    eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    rewrite interpV_tau.
    eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    zprogress.
    replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_insert //|].
    intros [[|]|]; cycle 1; rewrite list_insert_insert.
    {
      ired. rewrite interpV_bind interpV_trigger //=; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
      exists (Some false); rewrite list_insert_insert.
      rewrite yield_unfold; ired.
      guclo flagC_spec; econs; [instantiate (1:=p_s)|instantiate (1:=p_t)|].
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      gbase. eapply CIH; eauto.
    }
    {
      clear CIH.
      ired. rewrite interpV_bind interpV_trigger //=; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
      exists (None); rewrite list_insert_insert. ired.
      eapply gpaco7_mon; eauto.
    }
    ired. rewrite interpV_bind interpV_trigger //=; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
    exists (Some true); rewrite list_insert_insert. ired.

    iter_l; rewrite list_lookup_insert //=; step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert.

    rewrite !HoareCall_unfold; ired.
    eapply gsim_HoareCall_prologue_both;
      [rewrite list_lookup_insert //
      |rewrite list_lookup_insert //
      |ss
      |].
    intros res1 [x arg] Hres1.
    rewrite ?list_insert_insert. ired.

    iter_l; rewrite list_lookup_insert //=.
    iter_r; rewrite list_lookup_insert //=.
    destruct (msk_c _); cycle 1; ss.
    { step_l; ss. }
    step_l; step_r; norm_l; norm_r; rewrite {1 3}/LMod.prog /=; destruct (dec _ _) as [e|e]; ss.
    { inv e; exfalso; apply yield_run_neq; eauto. }
    clear e; destruct (dec _ _) as [e|e].
    { ss. inv e; exfalso; apply yield_help_neq; eauto. }
    ss; clear e. norm_l. rewrite list_insert_insert. ss.
    norm_r. rewrite list_insert_insert. ss.

    rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
    eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    rewrite /SchI.yield /cfunU.
    destruct (arg ↓) eqn : Harg; cycle 1.
    { ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    ss. ired. rewrite /cgetU /=. ired.

    replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
    eapply gsim_sGet_tgt;
      [rewrite list_lookup_insert //=| ss | ].
    esplits; eauto. rewrite list_insert_insert.

    replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
    eapply gsim_sGet_src;
      [rewrite list_lookup_insert //=| ss | ].
    esplits; eauto. rewrite list_insert_insert.
    rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert. ired.

    replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
    eapply gsim_sGet_tgt;
      [rewrite list_lookup_insert //=| ss | ].
    esplits; eauto. rewrite list_insert_insert.

    replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
    eapply gsim_sGet_src;
      [rewrite list_lookup_insert //=| ss | ].
    esplits; eauto. rewrite list_insert_insert.
    rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

    destruct (ths !! tid_cur_s) as [[stid_cur_s reto_s]|] eqn : Htid_cur_s; cycle 1.
    { rewrite Htid_cur_s /=.
      ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    rewrite Htid_cur_s //=.
    destruct (decide (stid_cur_s = tid_s)); subst; cycle 1.
    { ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    hexploit Hk2; eauto; clear Hk2; intros [? [Htid_t Hk2]].
    rewrite Htid_t; case_decide; clarify; ired.

    replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_insert //|].
    intros [[mtidn stidn] Hmtidn]; rewrite list_insert_insert; ired; ss.

    replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert // length_insert //|].
    specialize (Hk2 mtidn stidn Hmtidn); destruct Hk2 as [mtidn_s [stidn_s [Htid_s Hk3]]].
    unshelve eexists.
    { exists (mtidn_s, stidn_s); ss; eauto. }
    rewrite list_insert_insert; ired; ss.
    
    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. hss.
    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. ired.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert. hss.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert. ired.
    rewrite ?ModTr.alist_encode_decode /alist_upd /=; destruct (dec _ _); clarify.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. hss.
    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. ired.
    iter_r; rewrite list_lookup_insert //=. step_r; norm_r.
    rewrite list_insert_insert. hss.
    iter_r; rewrite list_lookup_insert //=. step_r; norm_r.
    rewrite list_insert_insert. ired.
    rewrite ?interpV_ret. ired. 
    eapply gpaco7_mon; first eapply Hk3; eauto.
  Qed. *)

  (* Lemma gsim_no_help RR r g p_s p_t rs tl img_c msk_c scp_c (ths : list (nat * option SAny.t))
      (mtid stid : nat) fn args k st_ctx ctx :
    fn ≠ Helping.help mn →
    fn ≠ Helping.run mn →
    tl !! stid =
    Some (⇓cris (⇓sb( img_c, msk_c, scp_c) (x <- trigger (Call fn args);; k x)),
          ⇓cris (⇓sb( img_c, msk_c, scp_c) (x <- trigger (Call fn args);; k x)), None) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs)) (stid, fst ∘ fst <$> tl))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, ths ↑) :: (SchI.v_tid, mtid ↑) :: st_ctx))
          (rs ↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs)) (stid, snd ∘ fst <$> tl))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, (reqmap tl) ↑)
          :: (SchI.v_ths, ths ↑) :: (SchI.v_tid, mtid ↑) :: st_ctx)) rs ↑)).
  Proof.
    intros Hfnhelp Hfnrun Hstid. eapply lookup_lt_Some in Hstid as Hstidlen.
    iter_l; iter_r; rewrite ?list_lookup_fmap Hstid /=.
    destruct (msk_c fn); ss; [|step_l; ss].
    step_l; step_r.
    hexploit (prog_fn fn); eauto; intros [[-> ?]|[[-> ?]|[EQ Hfn]]]; ss. rewrite -EQ; clear EQ.
    destruct Hfn as [[-> ->]|Hfn].
    {
      ss. norm_l; norm_r. rewrite /yield.
      eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
      eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
      rewrite ?list_insert_insert.

      rewrite /SchI.yield /cfunU /=.
      destruct (args ↓) as [arg|] eqn : Hargs; cycle 1.
      { ss. ired. rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }
      destruct arg; clear Hargs; ss. ired.
      rewrite 
    } *)

  Ltac unfold_trans :=
    rewrite /ModTr.trans_ktree /SB.sandbox_body /SB.sandbox
      /ModTr.trans /SModTr.trans_ktree /SModTr.trans /=.

  Theorem helping_onoff_correct :
    ctx_refines (mod_off, emp%I) (mod_on, emp%I).
  Proof.
    rewrite /mod_off /mod_on.
    intros [ctx ctxP] WF; ss; split.
    { inv WF. econs.
      { revert wf_fns. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
      { revert wf_scopes. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
    }
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].

    intro arg; eapply (@gsim_adequacy smj_top smj_top).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    rewrite !alist_find_map_snd.
    set (fnsems := (Mod.fnsems _ ++ _) ++ _).
    destruct (alist_find None fnsems) eqn: FIND; s; cycle 1.
    { s. ired. ginit. step_l. ss. }
    rewrite alist_find_app_o; des_ifs.
    { rewrite alist_find_app_o /HelpingOn.t /SchI.t in Heq; revert Heq; unseal CRIS; intros Heq.
      des_ifs; ss.
    }
    subst fnsems; rewrite alist_find_app_o in FIND; des_ifs.
    { rewrite /HelpingOff.t /SchI.t in Heq0; revert Heq0; unseal CRIS; ss. }
    rewrite FIND /ModTr.trans_ktree; ired.

    destruct f as [[[imgf mskf] scpf] f].
    assert (Hscp : scpf ## (SchI.scopes ++ HelpingOn.scopes mn)).
    { hexploit (Mod.well_scoped_fns ctx None); ss.
      rewrite /fnsems_scopes FIND /=; intros Hin.
      apply elem_of_disjoint; intros x Hinctx%elem_of_list_In%Hin%elem_of_list_In Hinsch.
      hexploit (Mod.wf_scopes WF); rewrite /Mod.scopes /=.
      intros Hnodup; eapply (NoDup_app_disjoint _ _ Hnodup x); eauto.
      { eapply elem_of_list_In. rewrite /Mod.scopes /SchI.t /HelpingOn.t; unseal CRIS; ss.
        revert Hinsch; rewrite /HelpingOn.scopes /SchI.scopes; ss.
        set_solver.
      }
      { eapply elem_of_list_In, Hinctx; eauto. }
    }

    clear Heq Heq0.
    rewrite /SB.sandbox_body /=.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }

    (* Start coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    set (st_src := (_, _) :: _) at 1.
    set (st_tgt := (_, _) :: _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (bool * nat * jobID)))
      (tid_cur stid_cur : nat) (ths : list (nat * option SAny.t)) st_ctx,
        st_src = [(SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, tid_cur↑)] ++ st_ctx ∧
        st_tgt = [(HelpingOn.v_reqs mn, (reqmap tl)↑);
          (SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, tid_cur↑)] ++ st_ctx ∧
        tp_src = (stid_cur, (fst ∘ fst <$> tl)) ∧ tp_tgt = (stid_cur, (snd ∘ fst <$> tl)) ∧
        NoDup (reqlist_all tl).*1.*2 ∧
        ∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) →
          help_rel itr_s itr_t no ∧
          match no with
          | Some _ => ∃ stid_i ro_i, ths !! stid_i = Some (i, ro_i)
          | None => True
          end); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { econs. }
      intros ???? [-> In]%list_lookup_singleton_Some; clarify.
      split; ss.
      eapply help_rel_eq; eauto.
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    clear st_src st_tgt tp_src tp_tgt f imgf mskf scpf FIND arg Hscp.
    revert_until WF.
    gcofix CIH.
    intros rs Hrs ???? [tl [tid_cur [stid_cur [ths [st_ctx [-> [-> [-> [-> [Htl Hlookup]]]]]]]]]].

    destruct ((fst ∘ fst <$> tl) !! stid_cur) as [i|] eqn : Htid; cycle 1.
    { iter_l. rewrite Htid. step_l. norm_l. step_l. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    destruct no as [[[[|] n] j]|].
    { (* Pending helpee *)
      zprogress.
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.
      revert Htid; rewrite /helpee_pend_s /helpee_pend_t; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x Hres1; rewrite ?list_insert_insert.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x. intros res x Hres.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid_cur := (_, _, Some (true, n, j))]> tl); esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap /reqlist_all list_fmap_insert /= list_insert_id //.
          rewrite list_lookup_fmap Htid //=.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite /reqlist_all list_fmap_insert /= list_insert_id // list_lookup_fmap Htid //=. }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend n j); eauto.
              { rewrite /helpee_pend_s /yield_epliogue. grind.
                instantiate (1:=k).
                repeat f_equal.
                { extensionality a; grind. }
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal. extensionality a; grind. }
            }
            esplits; eauto.
          }
        }
      }

      (* tired of waiting *)
      rewrite /HelpingOn.try_run /cgetU; ired.
      replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
      eapply gsim_sGet_tgt; [rewrite list_lookup_insert //| |]; s.
      { rewrite ?length_fmap //. }
      { rewrite String.eqb_refl //. }
      esplits; eauto. { destruct (dec _ _); clarify. }
      rewrite ?list_insert_insert. ired. rewrite ?interpV_ret. ired. hss. ired.

      rewrite /reqmap.
      erewrite (elem_of_list_to_map_1); eauto; cycle 1.
      { eapply NoDup_reqlist; eauto. }
      { eapply elem_of_list_omap; exists (true, n, j); split; ss.
        rewrite /reqlist_all elem_of_list_omap; exists (Some (true, n, j)); split; ss.
        rewrite elem_of_list_lookup; exists stid_cur.
        rewrite list_lookup_fmap Htid //.
      }

      ired. rewrite /cput.
      iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
      rewrite String.eqb_refl /=. step_r. norm_r.
      rewrite list_insert_insert. ired. hss.
      iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
      step_r. norm_r. rewrite list_insert_insert /=. ired.
      rewrite ModTr.alist_encode_decode /alist_upd /=; destruct (dec _ _); ss; clarify.

      eapply gsim_jobs_both; try by rewrite ?length_fmap.
      clear dependent res x. hss.
      intros res Hres.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res. intros res x Hres.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap /reqlist_all ?list_fmap_insert /=.
          eapply map_eq; intros i; destruct (decide (i = n)).
          { subst; rewrite lookup_delete.
            rewrite (not_elem_of_list_to_map_1 (omap _ _)) //.
            intros [[? ?] [EQ Hin%elem_of_list_omap]]%elem_of_list_fmap; ss; clarify.
            destruct Hin as [[[[ | ] ?] ?] [Hin ?]]; clarify.
            eapply elem_of_list_omap in Hin as [[[[? ?] ?]|] [Hin ?]]; ss; clarify.

            revert Htl; rewrite /reqlist_all.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite fmap_app omap_app; cbn.
            rewrite insert_take_drop // ?length_fmap // cons_app Permutation_app_swap in Hin.
            ss; inv Hin.
            rewrite fmap_take fmap_drop cons_app Permutation_app_swap.
            intros Htl%NoDup_fmap_1; ss.
            inv Htl. rewrite -omap_app elem_of_list_fmap in H5; eapply H5.
            exists (true, n0, j0); split; ss.
            eapply elem_of_list_omap; eauto.
          }
          rewrite lookup_delete_ne //.
          destruct (list_to_map _ !! i) eqn : Hi.
          { eapply elem_of_list_to_map_2 in Hi.
            revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite ?fmap_app ?omap_app; cbn.
            rewrite cons_app Permutation_app_swap_app /=.
            rewrite insert_take_drop; [|rewrite length_fmap //].
            move => /elem_of_cons [[]|]; [clarify|rewrite fmap_take fmap_drop].
            intros Hi%elem_of_list_to_map_1; cycle 1.
            { revert Htl. rewrite /reqlist_all.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite ?fmap_app ?omap_app; cbn.
              rewrite cons_app Permutation_app_swap; cbn.
              rewrite -?fmap_app -?omap_app.
              admit.
              (* rewrite cons_app Permutation_app_swap_app.
              rewrite fmap_take fmap_drop; cbn.
              rewrite fmap_app; intros Htl; inv Htl; eauto. *)
            }
            rewrite ?fmap_app ?omap_app; cbn. rewrite Hi. ss.
          }
          symmetry. eapply not_elem_of_list_to_map_1.
          eapply not_elem_of_list_to_map_2 in Hi.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite cons_app Permutation_app_swap_app; cbn.
          rewrite fmap_take fmap_drop fmap_app.
          intros ?%not_elem_of_cons; by des.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite /reqlist_all insert_take_drop // fmap_app omap_app; cbn.
          revert Htl; rewrite /reqlist_all.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite fmap_app omap_app; cbn; rewrite fmap_take fmap_drop.
          rewrite cons_app Permutation_app_swap_app; cbn; intros Hi; inv Hi; eauto.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply help_rel_helper; eauto.
          }
        }
      }

      rewrite ?interpV_ret; ired.
      iter_l; iter_r; rewrite !list_lookup_insert //= ?length_fmap //.
      step_l; step_r; norm_l; norm_r.
      rewrite !list_insert_insert //.

      gbase. eapply (CIH res); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap ?list_fmap_insert /=.
        eapply map_eq; intros i; destruct (decide (i = n)).
        { subst; rewrite lookup_delete.
          rewrite (not_elem_of_list_to_map_1 (omap _ _)).
          { econs. }
          move : Htl; rewrite /reqlist_all.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop // ?fmap_app ?omap_app ?fmap_app; cbn.
          rewrite cons_app Permutation_app_swap_app; cbn; rewrite ?fmap_app.
          intros Htl; inv Htl; eauto.
          admit.
        }
        rewrite lookup_delete_ne //.
        destruct (list_to_map _ !! i) eqn : Hi.
        { eapply elem_of_list_to_map_2 in Hi.
          revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite ?fmap_app ?omap_app; cbn.
          admit.
          (* rewrite cons_app Permutation_app_swap_app /=.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          move => /elem_of_cons [[]|]; [clarify|rewrite fmap_take fmap_drop].
          intros Hi%elem_of_list_to_map_1; cycle 1.
          { revert Htl. erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite ?fmap_app ?omap_app; cbn. rewrite cons_app Permutation_app_swap_app.
            rewrite fmap_take fmap_drop; cbn.
            rewrite fmap_app; intros Htl; inv Htl; eauto.
          }
          rewrite ?fmap_app ?omap_app; cbn. rewrite Hi. ss. *)
        }
        symmetry. eapply not_elem_of_list_to_map_1.
        eapply not_elem_of_list_to_map_2 in Hi.
        admit.
        (* rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite cons_app Permutation_app_swap_app; cbn.
        rewrite fmap_take fmap_drop fmap_app.
        intros ?%not_elem_of_cons; by des. *)
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        admit.
        (* rewrite list_fmap_insert /=.
        revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite cons_app Permutation_app_swap_app; cbn.
        rewrite fmap_take fmap_drop //.
        intros Hin; inv Hin; eauto. *)
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto.
        }
      }
    }

    { (* Done Helpee *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.

      zprogress.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res1 x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res1. intros res2 x2 Hres2.
        gbase. eapply (CIH res2); try by des.

        admit.
        (* eexists (<[stid_cur := (_, _, (Some (false, n, j)))]> tl); ss; esplits; eauto.
        { do 3 f_equal. rewrite /reqmap.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        {
          rewrite list_fmap_insert /=.
          revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite fmap_take fmap_drop //.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_helpee_done; eauto.
            { rewrite /helpee_pend_t; repeat f_equal; grind. extensionalities a; grind. }
            { esplits; eauto. }
          }
        } *)
      }

      rewrite ?interpV_ret; ired.
      rewrite /HelpingOn.try_run /cgetU; ired.

      replace_r; [rewrite interpV_bind interpV_trigger //|].
      eapply gsim_sGet_tgt;
        [rewrite list_lookup_insert //; [repeat f_equal; grind|rewrite length_fmap //]
        | ss; rewrite String.eqb_refl //
        |].
      esplits; eauto.
      { rewrite /alist_find ?eq_rel_dec_correct; des_ifs. }
      rewrite list_insert_insert. hss. ired.

      rewrite /reqmap.
      admit.
      (* rewrite (not_elem_of_list_to_map_1 (omap _ tl.*2)); cycle 1.
      revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
      rewrite insert_take_drop; [|rewrite length_fmap //].
      rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
      rewrite cons_app Permutation_app_swap_app; cbn; rewrite ?fmap_app.
      intros Htl; inv Htl; eauto. rewrite -fmap_take -fmap_drop //.
      erewrite (not_elem_of_list_to_map_1); eauto; cycle 1.
      { intros [? Hin]%elem_of_list_lookup.
        rewrite 
        eapply not_elem_of_list_omap; exists (Some (false, rid, jid)); split; ss.
        rewrite elem_of_list_lookup; exists stid_helpee; rewrite list_lookup_fmap Hhelpee //.
      }
      rewrite /reqmap.
          replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|]. ired.
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //|ss|].
          intros res2 x Hres2. rewrite ?list_insert_insert /=. ired.

          replace_r; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_sGet_tgt;
            [rewrite list_lookup_insert //; [repeat f_equal; grind|rewrite length_fmap //]
            | ss; rewrite String.eqb_refl //
            |].
          esplits; eauto; ss; [destruct (dec _ _); ss|].
          hss. ired. rewrite Hhelpee list_insert_insert. ired.
          rewrite ?interpV_ret /=; ired.

      iter_l; iter_r; rewrite !list_lookup_insert //= ?length_fmap //.
      step_l; step_r; norm_l; norm_r.
      rewrite !list_insert_insert //.

      gbase. eapply (CIH res); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap ?list_fmap_insert /=.
        eapply map_eq; intros i; destruct (decide (i = n)).
        { subst; rewrite lookup_delete.
          rewrite (not_elem_of_list_to_map_1 (omap _ (<[stid_cur:=_]> tl.*2))).
          { econs. }
          revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
          rewrite cons_app Permutation_app_swap_app; cbn; rewrite ?fmap_app.
          intros Htl; inv Htl; eauto. rewrite -fmap_take -fmap_drop //.
        }
        rewrite lookup_delete_ne //.
        destruct (list_to_map _ !! i) eqn : Hi.
        { eapply elem_of_list_to_map_2 in Hi.
          revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite cons_app Permutation_app_swap_app /=.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          move => /elem_of_cons [[]|]; [clarify|rewrite fmap_take fmap_drop].
          intros Hi%elem_of_list_to_map_1; cycle 1.
          { revert Htl. erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite ?fmap_app ?omap_app; cbn. rewrite cons_app Permutation_app_swap_app.
            rewrite fmap_take fmap_drop; cbn.
            rewrite fmap_app; intros Htl; inv Htl; eauto.
          }
          rewrite ?fmap_app ?omap_app; cbn. rewrite Hi. ss.
        }
        symmetry. eapply not_elem_of_list_to_map_1.
        eapply not_elem_of_list_to_map_2 in Hi.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        revert Hi; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite cons_app Permutation_app_swap_app; cbn.
        rewrite fmap_take fmap_drop fmap_app.
        intros ?%not_elem_of_cons; by des.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        rewrite list_fmap_insert /=.
        revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite cons_app Permutation_app_swap_app; cbn.
        rewrite fmap_take fmap_drop //.
        intros Hin; inv Hin; eauto.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto.
        }
      } *)
    }

    (* Non-helpee case *)
    apply lookup_lt_Some in Htid as Hstid_cur_length.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [Hcase _].
    inv Hcase; cycle 1.
    { (* Done helper case *)
      zprogress.
      eapply lookup_lt_Some in Htid as Htidlen.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x1. intros res x1 Hres.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap /reqlist_all list_fmap_insert /= list_insert_id //.
          rewrite list_lookup_fmap Htid //=.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite /reqlist_all list_fmap_insert /= list_insert_id // list_lookup_fmap Htid //=. }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply (help_rel_helper); eauto.
          }
        }
      }

      rewrite ?interpV_ret; ired.
      iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap //.
      step_l; step_r; norm_l; norm_r.
      rewrite ?list_insert_insert.
      gbase. eapply (CIH res); try by des.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. eapply help_rel_eq; eauto. }
      }
    }

    { (* call case *)
      admit.
    }

    rename itr into itr_c.
    rename H4 into Hscp.
    destruct (case_itrH itr_c) as [[v ->]|Hf].
    { (* return case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      norm_l. step_l. norm_r. step_r.
      des_ifs; ss; cycle 1.
      { norm_l. step_l. ss. }
      norm_l. norm_r.
      zstep; rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    }
    destruct Hf as [[f' ->]|Hf].
    { (* tau case *)
      zprogress.
      eapply gsim_tau_src; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      eapply gsim_tau_tgt; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      gbase. eapply CIH; eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Assume *)
      zprogress.
      eapply gsim_Assume_src; [rewrite list_lookup_fmap Htid //=|].
      { grind. }
      intros r_s2 -> Hr_s2.
      eapply gsim_Assume_tgt; [rewrite list_lookup_fmap Htid //=|].
      { grind. }
      exists r_s2; esplits; try by des.
      gbase. eapply (CIH r_s2); try by des.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    destruct Hf as [[res [f' ->]]|Hf].
    { (* AssumeRes *)
      zprogress. ss.
      eapply gsim_AssumeRes_src; [rewrite list_lookup_fmap Htid //=|].
      { f_equal. grind. repeat f_equal; extensionalities a; destruct a; ss. }
      intros Hval.
      eapply gsim_AssumeRes_tgt; [rewrite list_lookup_fmap Htid //=|].
      { f_equal; grind. repeat f_equal. extensionalities a; destruct a; ss. }
      split; first done.

      gbase. eapply (CIH (res ⋅ rs)); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Guarantee *)
      zprogress. ss.
      eapply gsim_Guarantee_tgt; [rewrite list_lookup_fmap Htid //=|].
      { f_equal. grind. }
      intros r2 ?.
      eapply gsim_Guarantee_src; [rewrite list_lookup_fmap Htid //=|].
      { f_equal; grind. }
      esplits; try by des.

      gbase. eapply (CIH r2); try by des.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    destruct Hf as [[R [[fn args|fn args|tid_yield|] [k ->]]]|Hf].
    { (* call case *)
      zprogress.
      rename msk0 into msk_c, img into img_c, scp into scp_c.
      revert Htid; unfold_trans; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      ss; destruct (msk_c fn); cycle 1.
      { norm_l. step_l. ss. }
      ss.
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_call; eauto.
          intros ret; eapply help_rel_eq; eauto.
          ired. unfold_trans. instantiate (1:=tau;; k ret).
          rewrite ?interpV_tau //.
        }
      }
    }
      (* destruct (decide (fn = Helping.run mn)); subst.
      { (* Helping.run *)
        norm_l. norm_r.
        rewrite {1 3}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; [ss|clarify].
        norm_l. norm_r.

        unfold_trans. rewrite /SModTr.trans.

        eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
        eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
        rewrite list_insert_insert.
        (* iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r. *)
        rewrite list_insert_insert.
        rewrite /HelpingOn.run /HelpingOff.run.
        rewrite /SModTr.trans.
        destruct (args↓) as [j|] eqn:Hargs ; cycle 1.
        { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. ss. }
        ss. ired.

        (* call for help *)
        rewrite /cgetU. ired.
        replace_r; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_sGet_tgt; [rewrite list_lookup_insert //| |]; s.
        { rewrite ?length_fmap //. }
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        { des_ifs; destruct (dec _ _); clarify. }
        rewrite list_insert_insert. ired. hss. ired.
        
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        hss. rewrite String.eqb_refl /=. norm_r. step_r. norm_r. hss.
        rewrite ModTr.alist_encode_decode /alist_upd /_alist_upd /=.
        destruct (dec _ _) as [e|]; ss; clear e.
        rewrite list_insert_insert.

        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert.
        ired.

        rewrite /SModTr.trans.
        eapply gsim_Yield_both; eauto.
        { rewrite length_fmap //. }
        { rewrite length_fmap //. }
        { (* Self-help *)
          rewrite /HelpingOn.try_run /cgetU; ired.
          replace_r; [rewrite interpV_bind interpV_trigger //|]. ired.
          eapply gsim_sGet_tgt; [rewrite list_lookup_insert //| |]; s.
          { rewrite ?length_fmap //. }
          { rewrite String.eqb_refl //. }
          esplits; eauto.
          { destruct (dec _ _); clarify. }
          rewrite list_insert_insert. ired. hss. ired. rewrite lookup_insert. ired.

          rewrite /cput.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          rewrite String.eqb_refl /=. step_r. norm_r.
          rewrite list_insert_insert.
          hss. rewrite ModTr.alist_encode_decode /=.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_r. norm_r. ired.
          rewrite list_insert_insert.
          rewrite /alist_upd /_alist_upd eq_rel_dec_correct; des_ifs.
          rewrite delete_insert; cycle 1.
          { apply not_elem_of_dom, is_fresh. }

          eapply gsim_jobs_both; try by rewrite ?length_fmap.
          intros res1 Hres1.

          eapply gsim_Yield_both; eauto.
          { rewrite length_fmap //. }
          { rewrite length_fmap //. }
          { (* immediate return *)
            rewrite ?interpV_ret; ired.
            iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap //.
            step_l; step_r; norm_l; norm_r.
            rewrite ?list_insert_insert.

            gbase. eapply (CIH res1); eauto.
            eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
            { do 3 f_equal.
              rewrite /reqmap /reqlist_all.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
            }
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            {
              revert Htl; rewrite /reqlist_all list_fmap_insert /=.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite insert_take_drop; [|rewrite length_fmap //].
              rewrite ?fmap_app ?omap_app; cbn.
              rewrite fmap_take fmap_drop //.
            }
            { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. split; ss. eapply help_rel_eq; eauto. }
            }
          }

          (* appeal to coinduction *)
          intros [ro_s Htid_cur]; exists ro_s; split; first done.
          intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
          intros res2 x Hres2; ss.

          gbase. eapply (CIH res2); eauto.
          eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
          { do 3 f_equal.
            rewrite /reqmap /reqlist_all.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
          }
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          {
            revert Htl; rewrite /reqlist_all list_fmap_insert /=.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite insert_take_drop; [|rewrite length_fmap //].
            rewrite ?fmap_app ?omap_app; cbn.
            rewrite fmap_take fmap_drop //.
          }
          { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              eapply (help_rel_helper _ _ img_c msk_c scp_c x k); eauto. grind.
            }
          }
        }

        (* Appeal to coinduction *)
        intros [ro_s Htid_cur]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
        intros res2 x Hres2; ss.
        gbase. eapply (CIH res2); eauto.

        set (tid_stid_cur := fresh _).
        eexists (<[stid_cur := (_, _, Some (true, tid_stid_cur, j))]> tl); esplits; eauto.
        { repeat f_equal.
          subst tid_stid_cur; rewrite /reqmap.
          symmetry; apply map_to_list_insert_inv; ss.
          rewrite map_to_list_to_map.
          { rewrite insert_take_drop /=; last done.
            admit.
            (* rewrite fmap_app omap_app; cbn.
            erewrite <-(take_drop_middle tl stid_cur) at 5; eauto.
            rewrite ?fmap_app ?omap_app; cbn.
            rewrite cons_app Permutation_app_swap_app //. *)
          }
          rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
          admit.
          (* rewrite cons_app Permutation_app_swap_app; cbn.
          apply NoDup_cons; split.
          { rewrite dom_list_to_map.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite fmap_app omap_app; cbn.
            intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
          }
          revert Htl.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite fmap_app omap_app; cbn; rewrite ?fmap_app //. *)
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
          admit.
          (* rewrite cons_app Permutation_app_swap_app; cbn.
          apply NoDup_cons; split.
          { rewrite /tid_stid_cur dom_list_to_map.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite fmap_app omap_app; cbn.
            intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
          }
          revert Htl.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite fmap_app omap_app; cbn; rewrite fmap_app //. *)
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend tid_stid_cur j).
              { rewrite /helpee_pend_s /yield_epliogue. grind.
                instantiate (1:=k).
                repeat f_equal; cycle 1.
                { extensionality a; grind. }
                { rewrite /yield_epliogue; repeat f_equal. extensionality a; grind. }
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal.
                { extensionality a; grind. }
                { extensionality a; grind. }
              }
              admit.
            }
            esplits; eauto.
          }
        }
      }

      destruct (decide (fn = Helping.help mn)); subst.
      { (* Helping.help *)
        norm_l. norm_r.
        rewrite {1 3}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [e|e]; [ss|clarify].
        { inv e. }
        destruct (dec _ _) as [e0|?]; [ss|clarify].
        clear e e0.
        norm_l. norm_r.
        rewrite /SModTr.trans_ktree /= /SB.sandbox_body /= /SB.sandbox /ModTr.trans_ktree.
        rewrite /ModTr.trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].
        eapply gsim_tau_tgt;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].

        (* Helper chooses tid *)
        rewrite /HelpingOn.help /HelpingOff.help /SModTr.trans.
        replace_r; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|intros rid].
        rewrite list_insert_insert.

        (* Source-helper goes to yield *)
        rewrite yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].
        replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|exists (Some true)].
        rewrite list_insert_insert. ired.

        (* Handling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        step_l. norm_l. rewrite list_insert_insert.
        rewrite HoareCall_unfold. ired.
        replace_r; [rewrite interpV_bind HoareCall_prologue_sred //|].
        eapply gsim_HoareCall_prologue_both; eauto.
        { rewrite list_lookup_insert // length_fmap //. }
        { rewrite list_lookup_insert // length_fmap //. }
        intros res1 [fsp_yield varg] Hres1; rewrite ?list_insert_insert. ired.

        (* Calling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //]. step_l; norm_l.
        rewrite {1}/LMod.prog /=; destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_run_neq; eauto. }
        clear e.
        destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_help_neq; eauto. }
        norm_l. rewrite list_insert_insert.
        rewrite /SModTr.trans_ktree /= /SB.sandbox_body /= /SB.sandbox /ModTr.trans_ktree.
        rewrite /ModTr.trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].

        (* Yield entrance *)
        rewrite /cfunU /SchI.yield.
        destruct (varg↓) as [[]|] eqn : Hvarg; cycle 1.
        { ired. iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //=].
          destruct (excluded_middle_informative _); ss; step_l; ss.
        }
        ired. rewrite /cgetU. ired.
        rewrite /SModTr.trans interpV_bind interpV_trigger.
        eapply gsim_sGet_src; [rewrite list_lookup_insert //=; [| rewrite length_fmap //=]| | ].
        { repeat f_equal; grind. }
        { ss. }
        esplits; eauto.
        rewrite list_insert_insert. hss. ired. hss. ired.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        rewrite /SModTr.trans interpV_bind interpV_trigger.
        eapply gsim_sGet_src; [rewrite list_lookup_insert //=; [| rewrite length_fmap //=]| | ].
        { repeat f_equal; grind. }
        { ss. }
        esplits; eauto.
        rewrite list_insert_insert. hss. ired. hss. ired.
        destruct (_ !! tid_cur) as [[stid_cur2 ?]|] eqn : Htid_cur; ss; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        case_decide; subst; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ired.

        (* Choose the helpee! *)
        destruct (reqmap tl !! rid) as [jid|] eqn : Hhelpee; cycle 1.
        { (* No Helpee *)
          ired.
          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (tid_cur, stid_cur). rewrite list_lookup_fmap Htid_cur //=. }
          rewrite list_insert_insert. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert.

          (* No helping here *)
          rewrite /HelpingOn.try_run /cgetU; ired.
          replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|]. ired.
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //|ss|].
          intros res2 x Hres2. rewrite ?list_insert_insert /=. ired.

          replace_r; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_sGet_tgt;
            [rewrite list_lookup_insert //; [repeat f_equal; grind|rewrite length_fmap //]
            | ss; rewrite String.eqb_refl //
            |].
          esplits; eauto; ss; [destruct (dec _ _); ss|].
          hss. ired. rewrite Hhelpee list_insert_insert. ired.
          rewrite ?interpV_ret /=; ired.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists (Some true); rewrite list_insert_insert].
          ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite list_insert_insert.

          rewrite HoareCall_unfold; ired.
          replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
          eapply gsim_HoareCall_prologue_HoareFun_epilogue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss|].
          clear dependent res2 x. intros res2 ret Hres2.
          rewrite ?list_insert_insert. ired. 

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite {1}/LMod.prog /=.
          destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
          clear e e'.
          destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
          norm_l. rewrite list_insert_insert.

          rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite /SchI.yield /cfunU.
          destruct (ret ↓) as [[]|] eqn : Hret; cycle 1.
          { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_fmap //].
            ss; destruct (excluded_middle_informative _); step_l; ss.
          }
          ired. clear Hret.

          rewrite /cgetU; ired; rewrite interpV_bind interpV_vis; ired.
          eapply gsim_sGet_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss|esplits; eauto].
          rewrite list_insert_insert; ired.
          rewrite ?interpV_ret; ired; hss; ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert; ired.

          rewrite /cgetU; ired; rewrite interpV_bind interpV_vis; ired.
          eapply gsim_sGet_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss|esplits; eauto].
          rewrite list_insert_insert; ired.
          rewrite ?interpV_ret; ired; hss; ired.
          rewrite Htid_cur; case_decide as H'; clarify; ired; clear H'.

          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (tid_cur, stid_cur); ss; rewrite list_lookup_fmap Htid_cur //=. }
          rewrite list_insert_insert. ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. hss. ired. rewrite ModTr.alist_encode_decode.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          rewrite /alist_upd /=; destruct (dec _ _); ss; destruct (dec _ _); ss; clarify.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          rewrite ?interpV_ret; ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.

          replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
          eapply gsim_HoareCall_epilogue_both;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss
            |].
          clear dependent res1 res2.
          intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
          rewrite ?interpV_ret. ired.
          iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_r; norm_r. rewrite list_insert_insert.
          
          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists None; rewrite list_insert_insert].
          ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.

          gbase. eapply (CIH res1); eauto.
          eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
          { do 3 f_equal.
            rewrite /reqmap.
            erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
          }
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          {
            rewrite list_fmap_insert /=.
            revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
            rewrite insert_take_drop; [|rewrite length_fmap //].
            rewrite ?fmap_app ?omap_app; cbn.
            rewrite fmap_take fmap_drop //.
          }
          { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              eapply help_rel_eq; eauto.
            }
          }
          Unshelve. all: try exact smj_bot; eauto.
        }
        
        (* Going to helpee *)
        rewrite /reqmap in Hhelpee; eapply elem_of_list_to_map_2 in Hhelpee.
        eapply elem_of_list_omap in Hhelpee as [[[? ?]|] [Hhelpee ?]]; ss; clarify.
        eapply elem_of_list_fmap_2 in Hhelpee as [[[? ?] [[? ?]|]] [EQ Hhelpee]]; ss.
        symmetry in EQ; ss; clarify.
        rewrite elem_of_list_lookup in Hhelpee; destruct Hhelpee as [stid_helpee Hhelpee].
        eapply Hlookup in Hhelpee as Hhelpee'.
        destruct Hhelpee' as [Hhelpee' [mtid_helpee Hthshelpee]].
        inv Hhelpee'; des; clarify.
        eapply lookup_lt_Some in Hhelpee as Hhelpeelen.
        assert (Hneq : stid_helpee ≠ stid_cur) by (ii; clarify).

        ired.
        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_fmap //
          |unshelve eexists].
        { exists (mtid_helpee, stid_helpee). rewrite /= list_lookup_fmap Hthshelpee //. }
        rewrite list_insert_insert; ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

        iter_l. rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_fmap Hhelpee /=.
        step_l; norm_l.

        replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|].
        eapply gsim_HoareCall_epilogue_HoareFun_prologue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap; repeat f_equal; grind
          |ss
          |].
        clear dependent res1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.

        rewrite {1}yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //|rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired.

        (* target proceed for helping *)
        rewrite /HelpingOn.try_run /cgetU; ired.
        replace_r; [rewrite interpV_bind interpV_vis //|]; ired.
        eapply gsim_sGet_tgt; [rewrite list_lookup_insert // length_fmap //| ss |].
        { rewrite String.eqb_refl //. }
        esplits; ss; [destruct (dec _ _); ss; clarify|].
        rewrite list_insert_insert. ired. rewrite ?interpV_ret; ired. hss. ired.
        rewrite /reqmap.
        erewrite (elem_of_list_to_map_1); eauto; cycle 1.
        { eapply elem_of_list_omap; exists (Some (true, rid, jid)); split; ss.
          rewrite elem_of_list_lookup; exists stid_helpee; rewrite list_lookup_fmap Hhelpee //.
        }

        ired. rewrite /cput.
        iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        rewrite String.eqb_refl /=. step_r. norm_r.
        rewrite list_insert_insert. ired. hss.
        iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        step_r. norm_r. rewrite list_insert_insert /=. ired.
        rewrite ModTr.alist_encode_decode /alist_upd /=; destruct (dec _ _); ss; clarify.
        destruct (dec _ _); ss; clarify. hss.

        eapply gsim_jobs_both;
          [rewrite length_insert length_fmap //
          |rewrite length_fmap //
          |ss
          |].
        clear dependent res1; intros res1 Hres1.

        rewrite yield_unfold; ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists (Some true); rewrite list_insert_insert].
        ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite list_insert_insert.

        rewrite HoareCall_unfold; ired.
        replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
        eapply gsim_HoareCall_prologue_HoareFun_epilogue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss|].
        clear dependent res1. intros res1 ret Hres1.
        rewrite ?list_insert_insert. ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite {1}/LMod.prog /=.
        destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
        clear e e'.
        destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
        norm_l. rewrite list_insert_insert.

        rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite /SchI.yield /cfunU.
        destruct (ret ↓) as [[]|] eqn : Hret; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_insert length_fmap //].
          ss; destruct (excluded_middle_informative _); step_l; ss.
        }
        ired. clear Hret.

        rewrite /cgetU; ired; rewrite interpV_bind interpV_vis; ired.
        eapply gsim_sGet_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss|esplits; eauto].
        rewrite list_insert_insert; ired.
        rewrite ?interpV_ret; ired; hss; ired.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert; ired.

        rewrite /cgetU; ired; rewrite interpV_bind interpV_vis; ired.
        eapply gsim_sGet_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss|esplits; eauto].
        rewrite list_insert_insert; ired.
        rewrite ?interpV_ret; ired; hss; ired.
        rewrite Hthshelpee; case_decide as H'; ss; clear H'. ired.

        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_insert length_fmap //
          |unshelve eexists].
        { exists (tid_cur, stid_cur); ss; rewrite list_lookup_fmap Htid_cur //=. }
        rewrite list_insert_insert. ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. hss. ired. rewrite ModTr.alist_encode_decode.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        rewrite /alist_upd /=; destruct (dec _ _); ss; clarify.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        rewrite ?interpV_ret; ired.
        iter_l; rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_l; norm_l.
        rewrite list_insert_commute //.
        rewrite list_insert_insert.
        rewrite list_insert_commute //.

        replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
        eapply gsim_HoareCall_epilogue_both;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss
          |].
        clear dependent res1 x1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
        rewrite ?interpV_ret. ired.
        iter_r; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        step_r; norm_r. rewrite list_insert_insert.
          
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert.

        gbase. eapply (CIH res1); eauto.
        set (i_cur := ⇓cris(_)).
        set (i_helpee := tau;; _).
        eexists (<[stid_cur := (i_cur, i_cur, None)]>
          (<[stid_helpee := (i_helpee, _, Some (false, rid, jid))]> tl)).
        esplits; eauto.
        {
          do 3 f_equal.
          rewrite /reqmap ?list_fmap_insert /=.
          rewrite list_insert_commute //.
          rewrite (list_insert_id _ stid_cur); cycle 1.
          { rewrite list_lookup_fmap Htid //=. }
          eapply map_eq; intros i; destruct (decide (i = rid)).
          { subst; rewrite lookup_delete.
            rewrite (not_elem_of_list_to_map_1 (omap _ (<[stid_helpee:=_]> tl.*2))).
            { econs. }
            revert Htl; erewrite <-(take_drop_middle tl stid_helpee) at 1; eauto.
            rewrite insert_take_drop; [|rewrite length_fmap //].
            rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
            rewrite cons_app Permutation_app_swap_app; cbn; rewrite ?fmap_app.
            intros Htl; inv Htl; eauto. rewrite -fmap_take -fmap_drop //.
          }
          rewrite lookup_delete_ne //.
          destruct (list_to_map _ !! i) eqn : Hi.
          { eapply elem_of_list_to_map_2 in Hi.
            revert Hi; erewrite <-(take_drop_middle tl stid_helpee) at 1; eauto.
            rewrite ?fmap_app ?omap_app; cbn.
            rewrite cons_app Permutation_app_swap_app /=.
            rewrite insert_take_drop; [|rewrite length_fmap //].
            move => /elem_of_cons [[]|]; [clarify|rewrite fmap_take fmap_drop].
            intros Hi%elem_of_list_to_map_1; cycle 1.
            { revert Htl. erewrite <-(take_drop_middle tl stid_helpee) at 1; eauto.
              rewrite ?fmap_app ?omap_app; cbn. rewrite cons_app Permutation_app_swap_app.
              rewrite fmap_take fmap_drop; cbn.
              rewrite fmap_app; intros Htl; inv Htl; eauto.
            }
            rewrite ?fmap_app ?omap_app; cbn. rewrite Hi. ss.
          }
          symmetry. eapply not_elem_of_list_to_map_1.
          eapply not_elem_of_list_to_map_2 in Hi.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          revert Hi; erewrite <-(take_drop_middle tl stid_helpee) at 1; eauto.
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite cons_app Permutation_app_swap_app; cbn.
          rewrite fmap_take fmap_drop fmap_app.
          intros ?%not_elem_of_cons; by des.
        }
        { rewrite ?list_fmap_insert //=. }
        { rewrite ?list_fmap_insert //=. do 2 f_equal. rewrite list_insert_id //.
          rewrite list_lookup_fmap Hhelpee //.
        }
        { ss. rewrite ?list_fmap_insert /= list_insert_id //; cycle 1.
          { rewrite list_lookup_insert_ne // list_lookup_fmap Htid //=. }
          revert Htl; erewrite <-(take_drop_middle tl stid_helpee) at 1; eauto.
          rewrite insert_take_drop ?fmap_app; [|rewrite length_fmap //].
          rewrite ?omap_app; cbn; rewrite cons_app Permutation_app_swap_app; cbn.
          rewrite fmap_take fmap_drop fmap_app.
          intros ?%NoDup_cons; by des.
        }
        { intros i; destruct (decide (i = stid_cur)).
          { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify.
            { split; ss. eapply help_rel_eq; eauto. }
            { rewrite length_insert //. }
          }
          destruct (decide (i = stid_helpee)).
          { subst; intros ??? Hin; rewrite list_lookup_insert_ne // list_lookup_insert // in Hin.
            clarify; split; ss.
            eapply help_rel_helpee_done; eauto.
            esplits; eauto.
          }
          intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
        }
      }
      { (* Other calls *)
        rewrite no_help_prog //; destruct (LMod.prog _ fn) as [bd|] eqn : Hfn; cycle 1.
        { s. step_l; ss. }
        ired.
        norm_l; norm_r.
        gbase. eapply (CIH); eauto.
        eexists (<[stid_cur := (_, _, None)]> tl). esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        {
          rewrite list_fmap_insert /=.
          revert Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite fmap_take fmap_drop //.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            rewrite /ModTr.trans /SB.sandbox. grind.
            eapply help_rel_eq; eauto.
            admit.
          }
        }
      }
      Unshelve. all: eauto.
    } *)
    { (* Spawn case *)
      zprogress.
      rename img into img_c, msk0 into msk_c, scp into scp_c.
      revert Htid; rewrite /ModTr.trans /SB.sandbox; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      destruct (msk_c fn); ss; cycle 1.
      { step_l; ss. }
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r. ired.
      gbase. eapply (CIH rs); try by des.
      eexists ((<[stid_cur := (_, _, None)]> tl) ++ [(fn_s args, fn_t args, None)]); ss.
      esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite !fmap_app omap_app; cbn; rewrite !omap_app; cbn; rewrite app_nil_r.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite ?fmap_app list_fmap_insert //=. }
      { rewrite ?fmap_app list_fmap_insert //=. }
      {
        rewrite /reqlist_all ?fmap_app omap_app fmap_app app_nil_r; cbn.
        rewrite !list_fmap_insert /=.
        revert Htl; rewrite /reqlist_all /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = length tl)); subst.
        { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
          rewrite Nat.sub_diag /=; intros Heq; inv Heq.
          split; ss.
          eapply help_rel_call; eauto.
          { instantiate (1:=λ a, Ret a); ired; refl. }
          { instantiate (1:=λ a, Ret a); ired; refl. }
          intros res; eapply help_rel_eq; eauto.
          instantiate (1:=Ret res); unfold_trans; rewrite ?interpV_ret //.
        }
        destruct (decide (i = stid_cur)); subst.
        { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
          intros EQ; clarify.
          split; ss.
          eapply help_rel_eq; eauto.
          rewrite ?length_fmap //.
        }
        rewrite -insert_app_l // list_lookup_insert_ne //.
        intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
        apply Hlookup; eauto.
      }
    }

    { (* Yield case *)
      zprogress.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. ired. refl.
        }
      }
    }

    { (* GetTid case *)
      zprogress.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gbase. eapply CIH; eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. ired. refl.
        }
      }
    }

    destruct Hf as [[R [s [f' ->]]]|[R [e [f' ->]]]].
    { (* sput sget *)
      destruct s as [k v|k].
      { (* sput *)
        zprogress.
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode.
        iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap //.
        step_l; step_r; norm_l; norm_r. ired.
        rewrite ?list_insert_insert.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap /reqlist_all.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        {
          revert Htl; rewrite /reqlist_all list_fmap_insert /=.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite fmap_take fmap_drop //.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            eapply help_rel_eq; eauto.
          }
        }
      }
      { (* sget *)
        zprogress.
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode. ired.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.

        gbase. eapply (CIH rs); eauto.
        eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
        { do 3 f_equal.
          rewrite /reqmap /reqlist_all.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        {
          revert Htl; rewrite /reqlist_all list_fmap_insert /=.
          erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; [|rewrite length_fmap //].
          rewrite ?fmap_app ?omap_app; cbn.
          rewrite fmap_take fmap_drop //.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            eapply help_rel_eq; eauto.
          }
        }
      }
    }

    destruct e as [X | X | fn args].
    { (* Choose case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      zprogress.
      eapply gsim_Choose_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x].
      eapply gsim_Choose_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x].
      gbase. apply (CIH rs); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    { (* Take case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      zprogress.
      eapply gsim_Take_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x ?].
      eapply gsim_Take_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x; split; ss].
      gbase. apply (CIH rs); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto. rewrite bind_ret_r //.
        }
      }
    }
    { (* IO case *)
      zprogress.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      norm_l; norm_r. guclo gsim_indC_spec. econs; intros ?? ->. instantiate (2:=smj_top).
      norm_l. norm_r. step_l. step_r. norm_l; norm_r. ired.
      gbase. apply (CIH rs); eauto.
      eexists (<[stid_cur := (_, _, None)]> tl); ss; esplits; eauto.
      { do 3 f_equal.
        rewrite /reqmap /reqlist_all.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app //.
      }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      {
        revert Htl; rewrite /reqlist_all list_fmap_insert /=.
        erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
        rewrite insert_take_drop; [|rewrite length_fmap //].
        rewrite ?fmap_app ?omap_app; cbn.
        rewrite fmap_take fmap_drop //.
      }
      { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_eq; eauto.
        }
      }
    }
  Admitted.
End Helping.

Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import SchHeader SchI.
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
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.
  Context (sp : sp_type) (mn : string). (* sp, module name for the helping module *)
  Context {jobID : Type} (jobs : jobID → itree Helping.pureE unit).
  (* Context (sp_s : sp_type) (sp_u : spl_type). *)
  Context (msk : string → bool). (* mask for the user module *)

  Local Definition mod_on :=  (HelpingOn.t mn jobs sp)  ★ (CFilter.filter msk (SchI.t)).
  Local Definition mod_off := (HelpingOff.t mn jobs sp) ★ (CFilter.filter msk (SchI.t)).

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

  Lemma yield_unfold :
    @Sch.yield crisE _ _ =
    tau;; b <- trigger (Choose (option bool));;
    match b with
    | None => Ret tt
    | Some false => Sch.yield
    | Some true => trigger (Call SchHdr.yield tt↑);;; Sch.yield
    end.
  Proof.
    rewrite {1}/Sch.yield; unseal "Sch"; rewrite unfold_iterC.
    repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
    { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal "Sch"; ss. }
    { ired. rewrite /Sch.yield; unseal "Sch"; ss. }
    { ired. done. }
  Qed.

  Definition to_reqlist
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * jobID * option bool)))
      : list (nat * (jobID * HelpingOn.progress)) :=
    (omap (λ n,
                match n with
                | Some (tid, jid, None) => Some (tid, (jid, HelpingOn.Pend))
                | Some (tid, jid, Some _) => Some (tid, (jid, HelpingOn.InProgress))
                | None => None
                end) tl.*2).

  Definition to_reqmap tl : gmap nat (jobID * HelpingOn.progress) := list_to_map (to_reqlist tl).

  Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
  Notation "'⇓sb(' i ',' m ',' s ')'" := (interpV (SB.handle_sandbox i m s)).
  Notation "'⇓smod(' sp ')'" := (interpV (SModTr.handle sp)).

  Definition yield_epliogue (tid_cur : nat) : itree lmodE Any.t :=
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(sp_none) (
        x <- cput SchI.SchI.v_tid tid_cur;;
        Ret (x↑)
    ))).
  (* Definition yield_epliogue (tid_cur : nat) (x : meta (SchAS.yield_spec ⊤ 1)): itree lmodE Any.t :=
    ⇓cris (⇓sb(true, wmask_and msk wmask_all, SchA.scopes) (
      r <- ⇓smod(sp_s) (
        cput SchI.SchI.v_tid tid_cur;;;
        r <- SchA.check_internal;;
        Ret (r↑)
      );;
      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (postcond (SchAS.yield_spec ⊤ 1) x r ret));;;
      Ret ret
    )). *)

  Definition helpee_pend_s
      (tid_cur : nat) (j : jobID) img_c msk_c scp_c k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    x <- yield_epliogue tid_cur;; tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp x;;;
      ⇓smod(sp) (𝒴;;; Helping.trans (jobs j);;; Ret ()↑)
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  Definition loop_t (stid_cur : nat) : () → itree crisE (() + Any.t) :=
    λ _ : (),
      'x_ : HelpingOn.jobmap <- cgetU (HelpingOn.v_reqs mn);;
      match x_ !! stid_cur with
      | Some y =>
          let (_, y0) := (y : jobID * HelpingOn.progress) in
          match y0 with
          | HelpingOn.Pend => Ret (inr () ↑)
          | HelpingOn.InProgress => Ret (inl ())
          end
      | None => Ret (inr () ↑)
      end.

  Definition helpee_pend_t
      (tid_cur tid_stid_cur : nat) (j : jobID) img_c msk_c scp_c k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    x <- yield_epliogue tid_cur;; tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp x;;;
      ⇓smod(sp) (
        𝒴;;; x <- loop_t tid_stid_cur ();;
        match x with
        | inl l => tau;; ITree.iter (λ _ : (), x <- 𝒴;; loop_t tid_stid_cur x) l
        | inr r => Ret r
        end;;;
        HelpingOn.try_run mn jobs tid_stid_cur)
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  Definition help_rel
      (itr_s itr_t : itree lmodE Any.t) (no : option (nat * jobID * option bool)) : Prop :=
    match no with
    | None =>
        ∃ itr img msk scp,
          itr_s = itr_t ∧ itr_s = ModTr.trans (SB.sandbox img msk scp itr)
    | Some (tid, jid, None) =>
        ∃ tid_cur img_c msk_c scp_c k fsp x_fsp,
          itr_s = helpee_pend_s tid_cur jid img_c msk_c scp_c k fsp x_fsp ∧
          itr_t = helpee_pend_t tid_cur tid jid img_c msk_c scp_c k fsp x_fsp (* pending *)
    | Some (tid, jid, Some b) =>
        if b : bool
        then itr_s = Ret tt↑ ∧ itr_t = Ret tt↑ (* helpee *)
        else itr_s = Ret tt↑ ∧ itr_t = Ret tt↑ (* helper *)
    end.

  Theorem helping_onoff_correct :
      (* (SchInSp : sp_incl (SchAS.sp sp_u E q) sp_s) : *)
    ctx_refines (mod_off, emp%I) (mod_on, emp%I).
  Proof.
    rewrite /mod_off /mod_on.
    intros [ctx ctxP] WF; ss; split.
    { inv WF.
      econs.
      { revert wf_fns. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
      { revert wf_scopes. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
    }
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].

    intro arg; eapply (@gsim_adequacy smj_top smj_top).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    rewrite !alist_find_map_snd.
    set (fnsems := (Mod.fnsems _ ++ _) ++ _).
    destruct (alist_find None fnsems) eqn: FIND; s; cycle 1.
    { s. ired. ginit. gstep. econs. econs. ss. }
    rewrite alist_find_app_o; des_ifs.
    { rewrite alist_find_app_o /HelpingOn.t /SchI.t in Heq; revert Heq; unseal CRIS; intros Heq.
      des_ifs; ss.
    }
    subst fnsems; rewrite alist_find_app_o in FIND; des_ifs.
    { rewrite /HelpingOff.t /SchI.t in Heq0; revert Heq0; unseal CRIS; ss. }
    rewrite FIND /ModTr.trans_ktree; ired.

    destruct f as [[[imgf mskf] scpf] f].

    clear Heq Heq0.
    rewrite /SB.sandbox_body /=.

    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }

    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    set (st_src := (_, _) :: _) at 1.
    set (st_tgt := (_, _) :: _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * jobID * option bool)))
      (tid_cur stid_cur : nat) (ths : list (nat * option SAny.t)) (b_sch : bool) st_ctx,
        st_src = [(SchI.SchI.v_ths, ths↑);
          (SchI.SchI.v_tid, tid_cur↑); (SchI.SchI.v_tids, (map fst ths)↑)] ++ st_ctx ∧
        st_tgt = [(HelpingOn.v_reqs mn, (to_reqmap tl)↑); (SchI.SchI.v_ths, ths↑);
          (SchI.SchI.v_tid, tid_cur↑); (SchI.SchI.v_tids, (map fst ths)↑)] ++ st_ctx ∧
        tp_src = (stid_cur, (fst ∘ fst) <$> tl) ∧ tp_tgt = (stid_cur, (snd ∘ fst) <$> tl) ∧
        List.NoDup (to_reqlist tl).*1 ∧
        ∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) → help_rel itr_s itr_t no); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { econs; ss; econs. }
      intros ???? [-> In]%list_lookup_singleton_Some; clarify.
      r. esplits; eauto.
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    clear st_src st_tgt tp_src tp_tgt f imgf mskf scpf FIND arg.
    (* generalize f. *)
    revert_until WF.
    gcofix CIH.
    intros rs Hrs ???? [tl [tid_cur [stid_cur [ths [b_sch [st_ctx [-> [-> [-> [-> [Htl Hlookup]]]]]]]]]]].

    iter_l; destruct (_ !! _) as [i|] eqn : Htid; cycle 1.
    { step_l. norm_l. step_l. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    iter_r. rewrite list_lookup_fmap Htid /=.
    destruct no as [|]; cycle 1.
    { apply lookup_lt_Some in Htid as Htid_cur.
      pose proof Htid as Htid'. apply Hlookup in Htid' as [itr_c [img_c [msk_c [scp_c [-> ->]]]]].
      destruct (case_itrH itr_c) as [[v ->]|Hf]; ss.
      {
        norm_l. step_l. norm_r. step_r.
        des_ifs; ss; cycle 1.
        { norm_l. step_l. ss. }
        norm_l. norm_r.
        zstep; rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
      }
      destruct Hf as [[f' ->]|Hf].
      { zprogress. norm_l. norm_r. step_l; step_r.
        norm_l. norm_r.
        gbase. eapply CIH; eauto.
        eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
        { erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; last ss.
          rewrite /to_reqmap /to_reqlist /= ?fmap_app ?omap_app /=. refl.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite insert_take_drop //= /to_reqlist fmap_app fmap_cons omap_app /=.
          move: Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite /to_reqlist fmap_app omap_app //=.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. }
        }
      }
      destruct Hf as [[P [f' ->]]|Hf].
      { destruct img_c; cycle 1.
        { norm_l. step_l. ss. }
        zprogress.
        norm_l; norm_r.
        step_l. step_r. norm_l; norm_r. hss.
        iter_l. rewrite list_lookup_insert /=. hss. norm_l. step_l.
        intros res; norm_l. step_l. norm_l.
        rewrite list_insert_insert. 2:{ rewrite length_fmap //. }
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_l. intros Hres. norm_l. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. hss.
        norm_l. step_l. norm_l. ired.
        rewrite list_insert_insert.

        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. hss. norm_r. step_r.
        exists res; norm_r. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_r. unshelve eexists; eauto. norm_r. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. hss.
        norm_r. step_r. norm_r. ired.
        rewrite list_insert_insert.
        gbase. eapply (CIH res); eauto.
        eexists (<[stid_cur := (_, _, None)]> tl); esplits; eauto.
        { erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite insert_take_drop; last ss.
          rewrite /to_reqmap /to_reqlist /= ?fmap_app ?omap_app /=. refl.
        }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { rewrite insert_take_drop //= /to_reqlist fmap_app fmap_cons omap_app /=.
          move: Htl; erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
          rewrite /to_reqlist fmap_app omap_app //=.
        }
        { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. }
        }
      }
      destruct Hf as [[res [f' ->]]|Hf].
      { admit. (* AssumeRes *) }
      destruct Hf as [[P [f' ->]]|Hf].
      { admit. (* Guarantee *) }
      destruct Hf as [[R [[fn args|fn args|tid_yield] [k ->]]]|Hf].
      {
        ss; destruct (msk_c fn); cycle 1.
        { norm_l. step_l. ss. }
        ss. zprogress.

        step_l. step_r.
        destruct (decide (fn = Helping.run mn)); subst.
        { (* Helping.run *)
          norm_l. norm_r.
          rewrite {1 3}/LMod.prog ?alist_find_map_snd /=.
          destruct (dec _ _) as [?|e]; [ss|clarify].
          norm_l. norm_r.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.
          rewrite /HelpingOn.run /HelpingOff.run.
          destruct (args↓) as [j|] eqn:Hargs ; cycle 1.
          { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. rewrite list_insert_insert.
            rewrite Hargs /=.
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            norm_l; step_l; ss.
          }
          ss.
          rewrite /ModTr.trans_ktree /SB.sandbox_body /= Hargs.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          rewrite list_insert_insert.
          step_l. norm_l. ired.

          (* call for help *)
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          rewrite String.eqb_refl /=. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode.
          rewrite list_insert_insert.
          ss. destruct (dec _ _) as [e|]; ss; clear e.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          hss. rewrite String.eqb_refl /=. norm_r. step_r. norm_r. hss.
          rewrite ModTr.alist_encode_decode /alist_upd /_alist_upd /=.
          destruct (dec _ _) as [e|]; ss; clear e.
          rewrite list_insert_insert.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.
          ired.

          fold (loop_t (fresh (dom (to_reqmap tl))) ()).
          set (loop := λ _ : (), _) at 4.
          assert (Heq : loop = loop_t (fresh (dom (to_reqmap tl)))); ss.
          rewrite Heq; clear Heq loop.
          rewrite (bisim_is_eq (unfold_iter _ _)).
          ired.

          gcofix CIH2.

          rewrite {2}yield_unfold.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          norm_r. step_r.
          intros [b|]; cycle 1.
          { (* Loop exit *)
            clear CIH2.
            norm_r. step_r. norm_r.
            rewrite list_insert_insert.
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            rewrite String.eqb_refl /=. step_r. norm_r. hss.
            rewrite ?ModTr.alist_encode_decode.
            rewrite list_insert_insert.
            rewrite /alist_find eq_rel_dec_correct; des_ifs; ss.
            ired. hss. ired. rewrite lookup_insert. ired.
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            rewrite String.eqb_refl /=. step_r. norm_r.
            rewrite list_insert_insert.
            hss. rewrite ModTr.alist_encode_decode /=.
            destruct (dec _ _); ss.
            ired. hss. ired. rewrite lookup_insert delete_insert.
            2:{ rewrite -not_elem_of_dom; eapply is_fresh. }

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            rewrite String.eqb_refl /=. step_r. norm_r. hss.
            rewrite list_insert_insert.
            
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. ired. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert.
            rewrite /alist_upd /_alist_upd eq_rel_dec_correct; des_ifs.

            rewrite yield_unfold.
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists None. step_l. norm_l.
            rewrite list_insert_insert.
            ired.
            gbase.
            admit.
            (* same tid doing same jobs *)
          }
          destruct b; cycle 1.
          { zprogress. norm_r. step_r. norm_r. ired. rewrite list_insert_insert.
            rewrite {1}yield_unfold.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists (Some false). step_l. norm_l. ired.
            rewrite list_insert_insert.
            gbase.
            eapply CIH2.
          }

          clear CIH2.
          step_r. norm_r. rewrite list_insert_insert.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_r. norm_r.
          rewrite list_insert_insert.

          rewrite {1}yield_unfold.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_l. norm_l. rewrite list_insert_insert.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_l. exists (Some true). norm_l. step_l. norm_l. rewrite list_insert_insert.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_l. norm_l. rewrite list_insert_insert.

          rewrite HoareCall_unfold. ired.
          rewrite /HoareCall_prologue; unseal "Help".

          destruct (sp SchHdr.yield) as [yield_spec|].
          {
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. intros x. norm_r. step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. intros arg. norm_r. step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert. hss. ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. intros rs_2. norm_r. step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. intros Hrs_2. norm_r. step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert. hss. ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists x. norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists arg. norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. hss. ired. hss. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists rs_2. norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. unshelve eexists; eauto. norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. hss. ired. hss. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l.
            rewrite {1 3}/LMod.prog /=.

            destruct (dec _ _); [exfalso; hexploit yield_run_neq; ii; clarify|].
            destruct (dec _ _); [exfalso; hexploit yield_help_neq; ii; clarify|ss].
            norm_l. norm_r.
            rewrite /ModTr.trans_ktree /SB.sandbox_body /ModTr.trans /SB.sandbox /=.
            rewrite ?list_insert_insert. ired.

            (* enter SchI yield - tgt *)
            rewrite /SchI.yield /SchI.SchI.trigger_Yield.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite ?list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite ?list_insert_insert.

            rewrite /cfunU. destruct (arg ↓) eqn : Harg; cycle 1.
            { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              destruct (sumbool_to_bool _); ss; step_l; ss.
            }
            ss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.
            ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            intros [tid_nxt Htid_nxt]. norm_r. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.
            ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            hss. rewrite ModTr.alist_encode_decode /=. ired. hss. ired.
            destruct (nth_error _ _) as [stid_next|] eqn : Hnth; cycle 1.
            { exfalso; eapply nth_error_Some in Htid_nxt; done. }
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. ired.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode /=.
            ired. hss. ired.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists (exist _ tid_nxt Htid_nxt). norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert. ired. hss. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode /=. ired. hss. ired.
            rewrite list_insert_insert. rewrite Hnth /=. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert. ired.

            gbase. eapply (CIH rs_2); eauto.
            set (tid_stid_cur := fresh _).
            eset (tl2 := <[stid_cur := (_, _, Some (tid_stid_cur, j, None))]> tl).
            assert (Htl2 : NoDup (to_reqlist tl2).*1).
            { rewrite /tl2.
              rewrite insert_take_drop // /to_reqlist fmap_app fmap_cons /=.
              rewrite omap_app /=.
              rewrite cons_app Permutation_app_swap_app /=; econs.
              { subst tid_stid_cur; rewrite /to_reqmap /to_reqlist.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; simpl omap.
                rewrite -omap_app -fmap_app.
                apply not_elem_of_list_to_map, not_elem_of_dom, is_fresh.
              }
              { revert Htl.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite /to_reqlist.
                rewrite fmap_app omap_app /= -NoDup_ListNoDup //.
              }
            }
            eexists tl2; esplits; eauto.
            { repeat f_equal.
              subst tl2.
              rewrite /to_reqmap /to_reqlist.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite insert_take_drop; last ss.
              rewrite /to_reqmap /to_reqlist /= !fmap_app !omap_app /=.
              fold (to_reqlist (take stid_cur tl)).
              fold (fmap snd (drop (S stid_cur) tl)).
              set (f := λ _, _). fold (omap f (drop (S stid_cur) tl).*2).
              rewrite /HelpingOn.jobmap; symmetry; apply map_to_list_insert_inv.
              rewrite map_to_list_to_map.
              { rewrite cons_app Permutation_app_swap_app //=. }
              revert Htl2.
              rewrite insert_take_drop // {1}/to_reqlist fmap_app omap_app //=.
            }
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { rewrite -NoDup_ListNoDup //. }
            { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
                { rewrite /helpee_pend_s. grind. repeat f_equal.
                  { rewrite /yield_epliogue; grind. extensionality a; grind. }
                  { instantiate (1:=k). extensionality a; grind. }
                }
                { rewrite /helpee_pend_t. grind. repeat f_equal.
                  { extensionality a; grind. }
                  { extensionality a; grind. }
                }
              }
            }
          }
          { (* no sp *)
            ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l.
            rewrite {1 3}/LMod.prog /=.

            destruct (dec _ _); [exfalso; hexploit yield_run_neq; ii; clarify|].
            destruct (dec _ _); [exfalso; hexploit yield_help_neq; ii; clarify|ss].
            norm_l. norm_r.
            rewrite /ModTr.trans_ktree /SB.sandbox_body /ModTr.trans /SB.sandbox /=.
            rewrite ?list_insert_insert. ired.

            rewrite /SchI.SchI.yield /cfunN /cfunU. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. hss. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert. ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            intros [tid_nxt Htid_nxt]. norm_r. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.
            ired. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            hss. rewrite ModTr.alist_encode_decode /=. ired. hss. ired.
            destruct (nth_error _ _) as [stid_next|] eqn : Hnth; cycle 1.
            { exfalso; eapply nth_error_Some in Htid_nxt; done. }
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. ired.
            rewrite list_insert_insert.
            
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert. ired. hss. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. exists (exist _ tid_nxt Htid_nxt). norm_l. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode /=. ired. hss. ired.
            rewrite list_insert_insert. rewrite /cgetU.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. rewrite list_insert_insert. ired. hss.
            rewrite ModTr.alist_encode_decode /=. ired. hss. ired. rewrite Hnth. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert. ired.

            gbase. eapply (CIH rs); eauto.
            set (tid_stid_cur := fresh _).
            eset (tl2 := <[stid_cur := (_, _, Some (tid_stid_cur, j, None))]> tl).
            assert (Htl2 : NoDup (to_reqlist tl2).*1).
            { rewrite /tl2.
              rewrite insert_take_drop // /to_reqlist fmap_app fmap_cons /=.
              rewrite omap_app /=.
              rewrite cons_app Permutation_app_swap_app /=; econs.
              { subst tid_stid_cur; rewrite /to_reqmap /to_reqlist.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; simpl omap.
                rewrite -omap_app -fmap_app.
                apply not_elem_of_list_to_map, not_elem_of_dom, is_fresh.
              }
              { revert Htl.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite /to_reqlist.
                rewrite fmap_app omap_app /= -NoDup_ListNoDup //.
              }
            }
            eexists tl2; esplits; eauto.
            { repeat f_equal.
              subst tl2.
              rewrite /to_reqmap /to_reqlist.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite insert_take_drop; last ss.
              rewrite /to_reqmap /to_reqlist /= !fmap_app !omap_app /=.
              fold (to_reqlist (take stid_cur tl)).
              fold (fmap snd (drop (S stid_cur) tl)).
              set (f := λ _, _). fold (omap f (drop (S stid_cur) tl).*2).
              rewrite /HelpingOn.jobmap; symmetry; apply map_to_list_insert_inv.
              rewrite map_to_list_to_map.
              { rewrite cons_app Permutation_app_swap_app //=. }
              revert Htl2.
              rewrite insert_take_drop // {1}/to_reqlist fmap_app omap_app //=.
            }
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { rewrite -NoDup_ListNoDup //. }
            { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
                { rewrite /helpee_pend_s. grind. repeat f_equal.
                  { extensionality a; grind. }
                  { instantiate (1:=k). extensionality a; grind. }
                }
                { rewrite /helpee_pend_t. grind. repeat f_equal.
                  { extensionality a; grind. }
                  { extensionality a; grind. }
                }
              }
            }
          }
        }

        destruct (decide (fn = Helping.help mn)) as [->|Hfn].
        { (* Helping *)
          rewrite {1 3}/LMod.prog /=.
          destruct (dec _ _); [exfalso; ii; clarify|].
          destruct (dec _ _); ss.
          norm_l; norm_r.
          rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /=.
          rewrite /HelpingOn.help /HelpingOff.help.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          step_r. intros tid_helpee. norm_r. step_r. norm_r.
          rewrite list_insert_insert. ired.

          destruct ((to_reqmap tl) !! tid_helpee) as [[jid_helpee [|]] |] eqn : Hhelpee; ss.
          { (* Found one to help *)
            rewrite {1}yield_unfold.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l.
            exists (Some true). norm_l. step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert.

            rewrite HoareCall_unfold. ired.
            rewrite /HoareCall_prologue; unseal "Help"; destruct (sp SchHdr.yield) as [yield_spec|].
            { 
              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. intros x. norm_r. step_r. norm_r.
              rewrite list_insert_insert.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. intros arg. norm_r. step_r. norm_r.
              rewrite list_insert_insert.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. norm_r.
              rewrite list_insert_insert. hss. ired. hss. ired.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. intros rs_2. norm_r. step_r. norm_r.
              rewrite list_insert_insert.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. intros Hrs_2. norm_r. step_r. norm_r.
              rewrite list_insert_insert.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. norm_r.
              rewrite list_insert_insert. hss. ired. hss. ired.

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. norm_r.
              rewrite list_insert_insert. ired.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. exists x. norm_l. step_l. norm_l.
              rewrite list_insert_insert.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. exists arg. norm_l. step_l. norm_l.
              rewrite list_insert_insert.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite list_insert_insert. hss. ired. hss. ired.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. exists rs_2. norm_l. step_l. norm_l.
              rewrite list_insert_insert.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. unshelve eexists; eauto. norm_l. step_l. norm_l.
              rewrite list_insert_insert.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite list_insert_insert. hss. ired. hss. ired.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite list_insert_insert. ired.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite {1}/LMod.prog /=.
              destruct (dec _ _); [exfalso; hexploit yield_run_neq; ii; clarify|].
              destruct (dec _ _); [exfalso; hexploit yield_help_neq; ii; clarify|ss].
              norm_l.
              rewrite list_insert_insert.
              rewrite /ModTr.trans_ktree /SB.sandbox_body /ModTr.trans /SB.sandbox /=.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite list_insert_insert. ired.

              (* Source yield only *)
              rewrite /SchI.yield /cfunU /SchI.SchI.trigger_Yield.
              destruct (arg ↓); cycle 1.
              { ss. iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                destruct (sumbool_to_bool _); ss; step_l; ss.
              }
              ss. norm_l. ired.

              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l. rewrite list_insert_insert. ired. hss.
              rewrite ModTr.alist_encode_decode /=. ired. hss. ired.
            }
            admit.
          }
        admit.
      }

      { (* Spawn case *)
        ss.
        admit.
      }

      { (* Yield case *)
        admit.
      }

      destruct Hf as [[R [s [f' ->]]]|[R [e [f' ->]]]].
      { (* sput sget *)
        admit.
      }

      destruct e; admit.
    }

    destruct p as [[tid jid] [[|]|]].
    { (* Helpee *)
      apply lookup_lt_Some in Htid as Htid_cur.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [-> ->]; ss.
      admit.
    }
    { (* Helper *)
      admit.
    }
    { (* Looping Helpee *)
      admit.
    }
    Unshelve. exact smj_top.
  Admitted.



    destruct Hf as [[P [f' ->]]|Hf].
    {
      (* destruct imgf; [|ziter_l; zstep_l]. *)
      zprogress.

      iter_l. step_l. norm_l.
      iter_l. hss. hss. norm_l. step_l. intros res; norm_l. step_l. norm_l.
      iter_l. step_l. intros Hres. norm_l. step_l. norm_l.
      iter_l. step_l. norm_l.
      iter_l. hss. norm_l. step_l. norm_l. ired.

      iter_r. step_r. norm_r.
      iter_r. hss. hss. norm_r. step_r. exists res. step_r. norm_r.
      iter_r. step_r. unshelve eexists; eauto. norm_r. step_r. norm_r.
      iter_r. step_r. norm_r.
      iter_r. hss. norm_r. step_r. norm_r. ired.

      gbase. eapply (CIH res); des; eauto.
      esplits; eauto.
    }
    destruct Hf as [[res [f' ->]]|Hf].
    { 
      (* rewrite !SBRed.bind ?SBRed.AssumeRes. *)
      zprogress.
      iter_l. step_l. norm_l.
      iter_l. hss. hss. norm_l. step_l. intros Hval. norm_l. step_l. norm_l.
      iter_l. step_l. norm_l.
      iter_l. hss. norm_l. step_l. norm_l. ired.

      iter_r. step_r. norm_r.
      iter_r. hss. hss. step_r. exists Hval. norm_r. step_r. norm_r.
      iter_r. step_r. norm_r.
      iter_r. hss. norm_r. step_r. norm_r.
      ired. gbase. eapply (CIH (res ⋅ rs)); des; eauto.
      esplits; eauto.
    }
    destruct Hf as [[P [f' ->]]|Hf].
    {
      (* rewrite !SBRed.bind !SBRed.Guarantee. *)
      zprogress.
      iter_r. step_r. norm_r.
      iter_r. hss. hss. step_r. intros x. norm_r. step_r. norm_r.
      iter_r. step_r. intros Hx. norm_r. step_r. norm_r.
      iter_r. step_r. norm_r.
      iter_r. hss. step_r. norm_r.

      iter_l. step_l. norm_l.
      iter_l. hss. hss. norm_l. step_l. exists x. step_l. norm_l.
      iter_l. step_l. unshelve eexists; eauto. step_l. norm_l.
      iter_l. step_l. norm_l.
      iter_l. hss. step_l. norm_l.
      ired.
      gbase. eapply (CIH x); des; eauto.
      esplits; eauto.
    }
    destruct Hf as [[R [[fn args|fn args|tid_yield] [k ->]]]|Hf].
    { 
      (* rewrite !SBRed.bind !SBRed.call. *)
      (* destruct (mskf fn) eqn : Hmask; [|iter_l; step_l; ss]. *)
      zprogress.

      iter_l. step_l. iter_r. step_r.
      rewrite /HelpingOff.t /SchA.t /HelpingOn.t /=; unseal CRIS; ss.
      destruct (decide (fn = Helping.run mn)); subst.
      { norm_l. norm_r.
        rewrite {1 3}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; [ss|clarify].
        norm_l. norm_r.

        replace_tp_r.
        { instantiate (1:=(0, [x <- _;; after_call k x])).
          repeat f_equal. rewrite /after_call; extensionalities i; repeat f_equal; grind.
        }
        replace_tp_l.
        { instantiate (1:=(0, [x <- _;; after_call k x])).
          repeat f_equal. rewrite /after_call; extensionalities i; repeat f_equal; grind.
        }

        iter_r. step_r. norm_r.
        rewrite /HelpingOn.run /HelpingOff.run.
        destruct (args↓) as [j|] eqn:Hargs ; cycle 1.
        { iter_l. step_l. norm_l. iter_l. rewrite Hargs /=. norm_l; step_l; ss. }
        ss.
        rewrite /ModTr.trans_ktree /SB.sandbox_body /= Hargs.

        iter_l. step_l. norm_l. ired.
        (* rewrite {1 2}yield_unfold. *)
        (* rewrite /Sch.yield; unseal "Sch". *)

        iter_r. rewrite String.eqb_refl /=. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode.
        ss. destruct (dec _ _) as [e|]; ss; clear e.
        iter_r. hss. rewrite String.eqb_refl /=. norm_r. step_r. norm_r. hss.
        iter_r. step_r. norm_r.
        iter_r. step_r. norm_r.

        set (loop := λ _ : (), _) at 4.
        rewrite (bisim_is_eq (unfold_iter _ _)).
        ired.
        (* rewrite {12}unfold_iterC. *)
        (* iter_r. step_r. norm_r. ired.
        iter_l. step_l. norm_l. *)

        gcofix CIH2.

        rewrite {2}yield_unfold.
        iter_r. step_r. norm_r.
        iter_r. step_r. intros [b|]; cycle 1.
        { clear CIH2.
          step_r. norm_r. iter_r.
          rewrite String.eqb_refl /=. step_r. norm_r. hss.
          rewrite ?ModTr.alist_encode_decode.
          erewrite (alist_upd_find); cycle 1.
          { ss; destruct (dec _ _); ss. }
          ss. grind. hss. grind.
          rewrite lookup_insert /=.
          iter_r. rewrite String.eqb_refl /=. step_r. norm_r.
          hss. rewrite ModTr.alist_encode_decode /=.
          erewrite (alist_upd_find); cycle 1.
          { ss; destruct (dec _ _); ss. }
          ss. grind. hss. grind.
          rewrite delete_insert.
          2:{ rewrite -not_elem_of_dom; eapply is_fresh. }
          rewrite lookup_insert //=.
          iter_r. rewrite String.eqb_refl /=. step_r. norm_r.
          hss. iter_r. step_r. norm_r. grind. rewrite ModTr.alist_encode_decode.
          rewrite alist_shadow alist_find_upd //=; cycle 1.
          { destruct (dec _ _); ss. }

          rewrite yield_unfold.
          iter_l. step_l. norm_l.
          iter_l. step_l. exists None. step_l. norm_l.
          ired.
          gbase.
          set (f1 := (0, _)). pattern f1. eapply eq_ind_r.
          { eapply (CIH rs Hrs); esplits; eauto. }
          { subst f1; f_equal; f_equal.
            rewrite /ModTr.trans.
            instantiate (1:= ITree.bind _ (λ x, tau;; _ x)).
            rewrite (@interpV_bind _ _ _ Any.t ModTr.handle_crisE); f_equal.
            extensionality x.
            rewrite interpV_tau; do 2 f_equal.
            (* rewrite ?bind_ret_l //. *)
          }
        }
        destruct b; cycle 1.
        { zprogress. norm_r. step_r. norm_r. ired.
          rewrite {1}yield_unfold.
          (* iter_r. step_r. norm_r. *)

          iter_l. step_l. norm_l.
          iter_l. step_l. exists (Some false). step_l. norm_l. ired.
          gbase.
          revert CIH2. rewrite /iterC.
          set (f1 := (0, _)) at 2. set (f3 := (0, _)) at 3. assert (f1 = f3).
          { subst f1 f3. f_equal. }
          rewrite H0. clear f1 H0.
          eauto.
        }

        clear CIH2.
        step_r. norm_r.
        iter_r. step_r. norm_r.

        rewrite {1}yield_unfold.
        iter_l. step_l. norm_l.
        iter_l. norm_l. step_l. exists (Some true). norm_l. step_l. norm_l.
        iter_l. step_l. norm_l.
        rewrite ModTr.alist_encode_decode /alist_upd /_alist_upd; ss; destruct (dec _ _); ss.

        rewrite HoareCall_unfold. ired.
        rewrite /HoareCall_prologue; unseal "Help".

        destruct (sp SchHdr.yield) as [yield_spec|].
        { iter_r. step_r. intros x. norm_r. step_r. norm_r.
          iter_r. step_r. intros arg. norm_r. step_r. norm_r.
          iter_r. step_r. norm_r. hss.
          iter_r. hss. step_r. intros rs_2. norm_r. step_r. norm_r.
          iter_r. step_r. intros Hrs_2. norm_r. step_r. norm_r.
          iter_r. step_r. norm_r. iter_r. hss. step_r. norm_r. ired.

          iter_l. step_l. exists x. norm_l. step_l. norm_l.
          iter_l. step_l. exists arg. norm_l. step_l. norm_l.
          iter_l. step_l. norm_l. hss.
          iter_l. hss. step_l. exists rs_2. norm_l. step_l. norm_l.
          iter_l. step_l. unshelve eexists; eauto. norm_l. step_l. norm_l.
          iter_l. step_l. norm_l. iter_l. hss. step_l. norm_l. ired.

          iter_r. step_r. iter_l. step_l.
          rewrite {1 3}/LMod.prog /=.

          destruct (dec _ _); [exfalso; hexploit yield_run_neq; ii; clarify|].
          destruct (dec _ _); [exfalso; hexploit yield_help_neq; ii; clarify|ss].
          norm_l. norm_r.
          iter_l. step_l. intros tid. norm_l. step_l. norm_l.
          iter_l. step_l. intros arg_y. norm_l. step_l. norm_l.
          iter_l. step_l. norm_l. hss.
          iter_l. hss. norm_l. step_l. intros rs_3. norm_l. step_l. norm_l.
          iter_l. step_l. intros Hrs_3. norm_l. step_l. norm_l.

          iter_r. step_r. exists tid. norm_r. step_r. norm_r.
          iter_r. step_r. exists arg_y. norm_r. step_r. norm_r.
          iter_r. step_r. norm_r. hss.
          iter_r. hss. step_r. exists rs_3. norm_r. step_r. norm_r.
          iter_r. step_r. unshelve eexists; eauto. norm_r. step_r. norm_r.
          iter_r. step_r. norm_r. iter_r. hss. step_r. norm_r. ired.
          rewrite /SchI.SchI.yield.
          iter_r. destruct (arg_y ↓) eqn : Harg_y; cycle 1.
          { ss. step_r; ss. }
          ss. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode /=.
          ired. hss. iter_r. step_r. intros [tid_next Htid_next]. norm_r. step_r. norm_r.
          iter_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode /=.
          rewrite /alist_upd /_alist_upd /=. iter_r. step_r. norm_r.
          rewrite /SchI.SchI.trigger_Yield.
          iter_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode /=. ired. hss.
          iter_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode /=. ired. hss.
          ired. destruct (nth_error _ _) as [stid_next|] eqn : Hnth; cycle 1.
          { exfalso; eapply nth_error_Some in Htid_next; done. }
          iter_r. step_r. norm_r. ired.

          iter_l. step_l. norm_l.
          ired. hss. ired. iter_l. step_l. norm_l.
          rewrite /cfunN. hss. iter_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode /=.
          ired. hss. ired.
          iter_l. step_l.
          exists (exist _ tid_next Htid_next). norm_l. step_l. norm_l.
          rewrite /SchA.trigger_Yield /SchI.SchI.trigger_Yield.
          iter_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode.
          iter_l. step_l. norm_l.
          iter_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode.
          rewrite /alist_upd /_alist_upd /=. ired. hss.
          iter_l. step_l. norm_l. hss. rewrite ModTr.alist_encode_decode /=. ired. hss.
          ired. rewrite Hnth. ired.
          iter_l. step_l. norm_l.
          iter_l. step_l. norm_l.
          iter_r. step_r. norm_r.
          ired.

          Definition yield_epliogue (tid_cur tid : nat) : itree crisE Any.t :=
            cput SchI.SchI.v_tid tid_cur;;;
            x <- SchA.check_internal;;
            ret <- trigger (Choose Any.t);;
            trigger (Guarantee (postcond (SchAS.yield_spec ⊤ 1) tid (()↑) ret));;;
            Ret ret.

          replace_tp_r.
          { instantiate (1:=
              (_,
              [ret <- interpV ModTr.handle_crisE
                (interpV (SB.handle_sandbox true _ SchA.scopes)
                  (interpV (SModTr.handle sp_s) (yield_epliogue tid_cur tid)));;
               ret <-interpV ModTr.handle_crisE
                (interpV (SB.handle_sandbox true wmask_all (HelpingOn.scopes mn))
                  (interpV (SModTr.handle sp)
                    (tau;; HoareCall_epilogue (Some yield_spec) x ret;;;
                     𝒴;;;
                     cond <- loop ();;
                     match cond with
                     | inl l => tau;; ITree.iter (λ _ : (), x <- 𝒴;; loop x) l
                     | inr r1 => Ret r1
                     end;;;
                     HelpingOn.try_run mn jobs (fresh (dom tidmap))
                    )));;
                after_call k ret
              ])). do 2 f_equal. f_equal.
            { do 2 f_equal.
              rewrite /yield_epliogue; ired.
              rewrite ?interpV_bind; ired. grind.
              rewrite interpV_ret; ired.
              rewrite interpV_trigger /=; ired; grind.
              rewrite interpV_bind interpV_trigger /=. ired. destruct x0, x3. f_equal.
              rewrite interpV_ret; extensionalities a; destruct a; ired. done.
            }
            { extensionalities ret. ired.
              rewrite ?interpV_tau. do 2 f_equal.
              rewrite interpV_bind; ired. rewrite interpV_bind. ired.
              rewrite (interpV_bind (SModTr.handle sp) (HoareCall_epilogue _ _ _)).
              etransitivity; last (rewrite interpV_bind; refl).
              etransitivity; last (rewrite interpV_bind; refl). do 2 f_equal.
              rewrite bind_bind. f_equal.

              { do 2 f_equal. rewrite /HoareCall_epilogue; unseal "Help".
                rewrite ?interpV_bind ?interpV_vis; ired; grind.
                rewrite interpV_ret; ired.
                rewrite interpV_bind interpV_vis interpV_ret; grind.
                rewrite interpV_ret; grind.
              }
              extensionalities a. grind.
            }
          }
        }
      }
    }
  Admitted.
End Helping.

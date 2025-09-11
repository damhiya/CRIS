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
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !schG}.
  Context (sp : sp_type) (mn : string). (* sp, module name for the helping module *)
  Context {jobID : Type} (jobs : jobID → itree Helping.pureE unit).
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

  Local Lemma no_help_prog fn ctx rs :
    fn ≠ Helping.run mn →
    fn ≠ Helping.help mn →
    LMod.prog (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOff.Mod mn jobs) ★
        CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★
        ctx) rs)
        fn =
    LMod.prog (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOn.Mod mn jobs sp) ★
        CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★
        ctx) rs)
        fn.
  Proof.
    intros ??.
    rewrite /LMod.prog /=; 
    repeat (
      match goal with
      | |- context [dec ?a ?b] => destruct (dec a b); ss; clarify
      end); esplits; eauto.
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

  (* Definition to_reqlist
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * jobID * option bool)))
      : list (nat * jobID) :=
    (omap (λ n,
      match n with
      | Some (tid, jid, None) => Some (tid, (jid, HelpingOn.Pend))
      | Some (tid, jid, Some _) => Some (tid, (jid, HelpingOn.InProgress))
      | None => None
      end) tl.*2). *)

  Definition reqmap
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * jobID)))
      : gmap nat jobID :=
    list_to_map (omap id tl.*2).

  Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
  Notation "'⇓sb(' i ',' m ',' s ')'" := (interpV (SB.handle_sandbox i m s)).
  Notation "'⇓smod(' img ',' sp ')'" := (interpV (SModTr.handle img sp)).

  Definition yield_epliogue (tid_cur : nat) : itree lmodE Any.t :=
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none) (
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
    (* x <- yield_epliogue tid_cur;; *)
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; Helping.trans (jobs j);;; Ret ()↑)
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  (* Definition loop_t (stid_cur : nat) : () → itree crisE (() + Any.t) :=
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
      end. *)

  Definition helpee_pend_t
      (tid_cur tid_stid_cur : nat) (j : jobID) img_c msk_c scp_c k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(true, sp) (𝒴;;; HelpingOn.try_run mn jobs tid_stid_cur)
    ));; tau;;
    ⇓cris (⇓sb(img_c, msk_c, scp_c) (k r)).

  Definition help_rel
      (itr_s itr_t : itree lmodE Any.t) (no : option (nat * jobID)) : Prop :=
    match no with
    | None =>
        ∃ itr img msk scp,
          itr_s = itr_t ∧ itr_s = ModTr.trans (SB.sandbox img msk scp itr)
    | Some (tid, jid) =>
        ∃ tid_cur img_c msk_c scp_c k fsp x_fsp,
          itr_s = helpee_pend_s tid_cur jid img_c msk_c scp_c k fsp x_fsp ∧
          itr_t = helpee_pend_t tid_cur tid jid img_c msk_c scp_c k fsp x_fsp (* pending *)
    end.

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
  Proof. intros H1 ?. iter_l; rewrite H1; ss. step_l; norm_l. done. Qed.

  Lemma gsim_tau_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k2 : Any.t → _) :
    tp_t !! tid_t = Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (tau;; k));; k2 x) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x<- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k2 x]> tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof. intros H1 ?. iter_r; rewrite H1; ss. step_r; norm_r. done. Qed.

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
    intros H1 [x Hk]. iter_l; rewrite H1; ss. step_l. exists x. norm_l. step_l. norm_l. ired. done.
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
    intros H1 Hk. iter_r; rewrite H1; ss. step_r. intros x. norm_r. step_r. norm_r. ired. eapply Hk.
  Qed.

  (* Lemma gsim_Choose_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
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
    intros H1 [x Hk]. iter_l; rewrite H1; ss. step_l. exists x. norm_l. step_l. norm_l. ired. done.
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
  Proof.
    intros Hin Hkey [t [Ht Hk]].
    iter_r; rewrite Hin; ss.
    rewrite Hkey /=.
    norm_r. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode Ht /=. ired. eapply Hk.
  Qed.

  (* No k2s here *)
  Lemma gsim_Assume_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k P r_s :
    tp_s !! tid_s = Some (⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Assume P);;; k))) →
    (∀ r_s2,
      img_c = true →
      ✓ r_s2 ∧ (Own r_s2 ⊢ |==> P ∗ Own r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (⇓sb(img_c, msk_c, scp_c) k)]> tp_s)) (Any.pair st_s (r_s2↑)))
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
      img_c msk_c scp_c k P r_t :
    tp_t !! tid_t = Some (⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Assume P);;; k))) →
    (∃ r_t2,
      img_c = true ∧
      ✓ r_t2 ∧ (Own r_t2 ⊢ |==> P ∗ Own r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (⇓sb(img_c, msk_c, scp_c) k)]> tp_t)) (Any.pair st_t (r_t2↑)))) →
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
      img_c msk_c scp_c k r_s r_s2 :
    tp_s !! tid_s = Some (⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (AssumeRes r_s2);;; k))) →
    (✓ (r_s2 ⋅ r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (⇓sb(img_c, msk_c, scp_c) k)]> tp_s))
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
      img_c msk_c scp_c k r_t r_t2 :
    tp_t !! tid_t = Some (⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (AssumeRes r_t2);;; k))) →
    (✓ (r_t2 ⋅ r_t) ∧
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (⇓sb(img_c, msk_c, scp_c) k)]> tp_t))
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

    clear Heq Heq0.
    rewrite /SB.sandbox_body /=.

    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }

    (* Starting coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    set (st_src := (_, _) :: _) at 1.
    set (st_tgt := (_, _) :: _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * jobID)))
      (tid_cur stid_cur : nat) (ths : list (nat * option SAny.t)) st_ctx,
        st_src = [(SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, tid_cur↑)] ++ st_ctx ∧
        st_tgt = [(HelpingOn.v_reqs mn, (reqmap tl)↑);
          (SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, tid_cur↑)] ++ st_ctx ∧
        tp_src = (stid_cur, (fst ∘ fst) <$> tl) ∧ tp_tgt = (stid_cur, (snd ∘ fst) <$> tl) ∧
        NoDup (omap id tl.*2).*1 ∧
        ∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) → help_rel itr_s itr_t no); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { econs. }
      intros ???? [-> In]%list_lookup_singleton_Some; clarify.
      r. esplits; eauto.
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    clear st_src st_tgt tp_src tp_tgt f imgf mskf scpf FIND arg.
    revert_until WF.
    gcofix CIH.
    intros rs Hrs ???? [tl [tid_cur [stid_cur [ths [st_ctx [-> [-> [-> [-> [Htl Hlookup]]]]]]]]]].

    destruct ((fst ∘ fst <$> tl) !! stid_cur) as [i|] eqn : Htid; cycle 1.
    { iter_l. rewrite Htid. step_l. norm_l. step_l. ss. }
    (* iter_l; iter_r; rewrite Htid /=. *)
    (* iter_l; destruct (_ !! _) as [i|] eqn : Htid; cycle 1.
    { step_l. norm_l. step_l. ss. } *)

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    (* iter_r. *)
    (* rewrite list_lookup_fmap Htid /=. *)
    destruct no as [|]; cycle 1.
    { apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'. apply Hlookup in Htid' as [itr_c [img_c [msk_c [scp_c [-> ->]]]]].
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
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. rewrite bind_ret_r //. }
        }
      }
      destruct Hf as [[P [f' ->]]|Hf].
      { (* Assume *)
        zprogress.
        eapply gsim_Assume_src; [rewrite list_lookup_fmap Htid //|].
        intros r_s2 -> Hr_s2.
        eapply gsim_Assume_tgt; [rewrite list_lookup_fmap Htid //|].
        exists r_s2; esplits; try by des.
        gbase. eapply (CIH r_s2); try by des.
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
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. }
        }
      }
      destruct Hf as [[res [f' ->]]|Hf].
      { (* AssumeRes *)
        zprogress. ss.
        eapply gsim_AssumeRes_src; [rewrite list_lookup_fmap Htid //=|].
        { repeat f_equal; extensionalities a; destruct a; ss. }
        intros Hval.
        eapply gsim_AssumeRes_tgt; [rewrite list_lookup_fmap Htid //=|].
        { repeat f_equal; extensionalities a; destruct a; ss. }
        split; first done.

        gbase. eapply (CIH (res ⋅ rs)); eauto.
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
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. }
        }
      }
      destruct Hf as [[P [f' ->]]|Hf].
      { (* Guarantee *)
        zprogress.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
        norm_l; norm_r.

        step_r. step_r. ired. norm_r. hss. ired. hss. ired.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_r.
        intros res; norm_r. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_r. intros Hres; eauto. norm_r. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. hss.
        norm_r. step_r. norm_r. ired.
        rewrite list_insert_insert.

        norm_l.
        iter_l. rewrite list_lookup_insert /=. hss. norm_l. step_l.
        exists res; norm_l. step_l. norm_l.
        rewrite list_insert_insert. 2:{ rewrite length_fmap //. }
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_l. unshelve eexists; eauto. norm_l. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. hss.
        norm_l. step_l. norm_l. ired.
        rewrite list_insert_insert.

        gbase. eapply (CIH res); eauto.
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
          { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto. }
        }
      }
      destruct Hf as [[R [[fn args|fn args|tid_yield|] [k ->]]]|Hf].
      { (* call case *)
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
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
          rewrite /SModTr.trans.
          destruct (args↓) as [j|] eqn:Hargs ; cycle 1.
          { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. rewrite list_insert_insert.
            rewrite Hargs /=.
            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            norm_l; step_l; ss.
          }
          ss.
          rewrite /ModTr.trans_ktree /SB.sandbox_body /= Hargs. ired.

          rewrite /SB.sandbox /ModTr.trans.
          eapply gsim_tau_src; [rewrite list_lookup_insert; [grind|rewrite ?length_fmap //]|]; s.
          rewrite list_insert_insert.

          (* call for help *)
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          rewrite String.eqb_refl /=. step_r. norm_r. hss. rewrite ModTr.alist_encode_decode.
          rewrite list_insert_insert.
          ss. destruct (dec _ _) as [e|]; ss; clear e. ired. hss. ired.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          hss. rewrite String.eqb_refl /=. norm_r. step_r. norm_r. hss.
          rewrite ModTr.alist_encode_decode /alist_upd /_alist_upd /=.
          destruct (dec _ _) as [e|]; ss; clear e.
          rewrite list_insert_insert.

          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert.
          ired.

          gcofix CIH2.

          rewrite {2}yield_unfold.
          ired. rewrite interpV_tau.
          eapply gsim_tau_tgt; [rewrite list_lookup_insert; [grind|rewrite ?length_fmap //]|]; s.
          rewrite list_insert_insert.

          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_tgt; [rewrite list_lookup_insert; [grind|rewrite ?length_fmap //]|]; s.

          intros [b|]; rewrite list_insert_insert; cycle 1.
          { (* Loop exit *)
            clear CIH2.

            ired.
            rewrite /HelpingOn.try_run /cgetU. ired.
            rewrite interpV_bind interpV_trigger /=. ired.
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

            rewrite yield_unfold.
            rewrite /SModTr.trans; ired.
            rewrite interpV_tau.
            eapply gsim_tau_src; [rewrite list_lookup_insert; [grind|rewrite ?length_fmap //]|]; s.
            rewrite list_insert_insert.

            rewrite interpV_bind interpV_trigger /=. ired.
            eapply gsim_Choose_src; [rewrite list_lookup_insert; [grind|rewrite ?length_fmap //]|]; s.
            exists None.
            rewrite list_insert_insert.
            ired.

            (* TODO : Make a jobs lemma here *)

            clear e Heq.
            assert (Htid' : ∃ ip, (tl !! stid_cur = Some (ip, None))) by (eexists; eauto).
            clear Htid. generalize (jobs j); clear dependent j.
            destruct Htid' as [? Htid].
            revert rs Hrs.
            gcofix CIH2.
            intros rs Hrs job; ides job.
            { clear CIH2. rewrite /Helping.trans.
              rewrite ?(bisim_is_eq (translate_ret _ _)).
              gbase. eapply (CIH rs); eauto.
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
                { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
                  rewrite ?interpV_bind ?interpV_ret; grind.
                  rewrite /ModTr.trans /SB.sandbox; instantiate (1:=tau;; k ()↑).
                  rewrite ?interpV_tau; grind.
                }
              }
            }
            { zprogress.
              rewrite /Helping.trans ?(bisim_is_eq (translate_tau _ _)).
              iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_l. norm_l.
              rewrite list_insert_insert.
              fold (Helping.trans t).

              iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              step_r. norm_r.
              rewrite list_insert_insert.

              gbase. eapply CIH2; eauto.
            }
            { destruct e as [e|e].
              { destruct e as [P | res | P].
                {
                  zprogress.
                  rewrite /Helping.trans !(bisim_is_eq (translate_vis _ _ _ _)).
                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. intros Pres. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. intros HPres. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. exists Pres. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. unshelve eexists; eauto. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  gbase. eapply (CIH2 Pres); eauto.
                }
                {
                  zprogress.
                  rewrite /Helping.trans !(bisim_is_eq (translate_vis _ _ _ _)).
                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. intros Pres. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. exists Pres. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  gbase. eapply (CIH2 (res ⋅ rs)); eauto.
                }
                {
                  zprogress.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. intros Pres. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. intros HPres; eauto. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. norm_r.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  rewrite /Helping.trans !(bisim_is_eq (translate_vis _ _ _ _)).
                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. hss. ired. hss.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. exists Pres. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. unshelve eexists; eauto. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. hss. ired.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. norm_l.
                  rewrite list_insert_insert. ired. fold (Helping.trans (k0 ())).

                  gbase. eapply (CIH2 Pres); eauto.
                }
              }
              {
                destruct e as [X | X | ].
                {
                  zprogress.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. intros ?. step_r. norm_r.
                  rewrite list_insert_insert.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. unshelve eexists; eauto. step_l; norm_l.
                  rewrite list_insert_insert. hss. ired. hss.

                  gbase. eapply CIH2; eauto.
                }
                {
                  zprogress.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_l. intros ?. step_l. norm_l.
                  rewrite list_insert_insert.

                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  step_r. unshelve eexists; eauto. step_r; norm_r.
                  rewrite list_insert_insert. hss. ired. hss.

                  gbase. eapply CIH2; eauto.
                }
                {
                  zprogress.

                  iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
                  norm_l; norm_r.
                  zstep. step_l; step_r; norm_l; norm_r. subst.

                  gbase. eapply CIH2; eauto.
                }
              }
            }
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

          destruct (sp SchHdr.yield) as [[yield_spec|yield_spec]|]; cycle 1.
          { iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. intros x. ss.
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
            des_ifs_safe; clear Heq. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.
            rewrite /SModTr.NativeGetTid.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. rewrite list_insert_insert.
            hss. rewrite ModTr.alist_encode_decode. ss.
            des_ifs_safe; clear Heq; ss. ired. hss. ired.

            (* TODO : stard dealing with GetTids - it would be better to come up with a
              fully working help_rel now *)

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l. hss. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert. ss.
            des_ifs_safe; clear Heq. ss. ired. hss.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.
            rewrite /SModTr.NativeGetTid.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.
            hss. rewrite ModTr.alist_encode_decode. ss. ired.
            des_ifs_safe; clear Heq. ss. ired. hss. ired.

            destruct (ths !! tid_cur) as [[stid_cur' ?]|] eqn : Htid_cur'; cycle 1.
            { rewrite ?Htid_cur'. iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              destruct (sumbool_to_bool _); ss; step_l; ss.
            }
            rewrite ?Htid_cur'; case_decide; cycle 1.
            { rewrite ?Htid_cur'. iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              destruct (sumbool_to_bool _); ss; step_l; ss.
            }
            subst stid_cur'.
            
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            intros [[tid_nxt stid_nxt] Htid_nxt]. norm_r. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l.
            exists (exist _ (tid_nxt, stid_nxt) Htid_nxt). norm_l. step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.
            rewrite /SModTr.NativeYield.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.
            rewrite /SModTr.NativeYield.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.
            rewrite /alist_upd /_alist_upd; des_ifs; clear Heq0 Heq1 Heq.
            rewrite ?interpV_ret; ired.

            gbase. eapply (CIH rs); eauto.
            set (tid_stid_cur := fresh _).
            eset (tl2 := <[stid_cur := (_, _, Some (tid_stid_cur, j))]> tl).
            eexists (<[stid_cur := (_, _, Some (tid_stid_cur, j))]> tl); esplits; eauto.
            { repeat f_equal.
              subst tid_stid_cur; rewrite /reqmap.
              symmetry; apply map_to_list_insert_inv; ss.
              rewrite map_to_list_to_map.
              { rewrite insert_take_drop /=; last done.
                rewrite fmap_app omap_app; cbn.
                erewrite <-(take_drop_middle tl stid_cur) at 5; eauto.
                rewrite ?fmap_app ?omap_app; cbn.
                rewrite cons_app Permutation_app_swap_app //.
              }
              rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
              rewrite cons_app Permutation_app_swap_app; cbn.
              apply NoDup_cons; split.
              { rewrite dom_list_to_map.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; cbn.
                intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
              }
              revert Htl.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite fmap_app omap_app; cbn; rewrite fmap_app //.
            }
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
              rewrite cons_app Permutation_app_swap_app; cbn.
              apply NoDup_cons; split.
              { rewrite /tid_stid_cur dom_list_to_map.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; cbn.
                intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
              }
              revert Htl.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite fmap_app omap_app; cbn; rewrite fmap_app //.
            }
            { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
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
              }
            }
          }
          { (* exists sp *)
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
            rewrite /SchI.yield /cfunU.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. ired.

            destruct (arg ↓) as [arg'|]; cycle 1.
            { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              des_if; step_l; ss.
            }

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. hss. rewrite ModTr.alist_encode_decode.
            rewrite list_insert_insert. ired. hss. ired.
            des_ifs_safe; clear Heq. hss. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.
            rewrite /SModTr.NativeGetTid.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r.
            rewrite list_insert_insert.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_r. norm_r. rewrite list_insert_insert.
            hss. rewrite ModTr.alist_encode_decode. ss.
            des_ifs_safe; clear Heq; ss. ired. hss. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode. ired.
            des_ifs_safe; clear Heq. ss. ired. hss.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.
            rewrite /SModTr.NativeGetTid.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
            step_l. norm_l.
            rewrite list_insert_insert.
            hss. rewrite ModTr.alist_encode_decode. ss. ired.
            des_ifs_safe; clear Heq. ss. ired. hss. ired.

            destruct (ths !! tid_cur) as [[stid_cur' ?]|] eqn : Htid_cur'; cycle 1.
            { rewrite ?Htid_cur'. iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              destruct (sumbool_to_bool _); ss; step_l; ss.
            }
            rewrite ?Htid_cur'; case_decide; cycle 1.
            { rewrite ?Htid_cur'. iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //].
              destruct (sumbool_to_bool _); ss; step_l; ss.
            }
            subst stid_cur'.
            
            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r.
            intros [[tid_nxt stid_nxt] Htid_nxt]. norm_r. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l.
            exists (exist _ (tid_nxt, stid_nxt) Htid_nxt). norm_l. step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.
            rewrite /SModTr.NativeYield.

            iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. hss. rewrite ModTr.alist_encode_decode /=.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.
            rewrite /SModTr.NativeYield.

            iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
            rewrite list_insert_insert. ired.
            rewrite /alist_upd /_alist_upd; des_ifs; clear Heq0 Heq1 Heq.
            rewrite ?interpV_ret; ired.

            gbase. eapply (CIH rs_2); eauto.
            set (tid_stid_cur := fresh _).
            eset (tl2 := <[stid_cur := (_, _, Some (tid_stid_cur, j))]> tl).
            eexists (<[stid_cur := (_, _, Some (tid_stid_cur, j))]> tl); esplits; eauto.
            { repeat f_equal.
              subst tid_stid_cur; rewrite /reqmap.
              symmetry; apply map_to_list_insert_inv; ss.
              rewrite map_to_list_to_map.
              { rewrite insert_take_drop /=; last done.
                rewrite fmap_app omap_app; cbn.
                erewrite <-(take_drop_middle tl stid_cur) at 5; eauto.
                rewrite ?fmap_app ?omap_app; cbn.
                rewrite cons_app Permutation_app_swap_app //.
              }
              rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
              rewrite cons_app Permutation_app_swap_app; cbn.
              apply NoDup_cons; split.
              { rewrite dom_list_to_map.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; cbn.
                intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
              }
              revert Htl.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite fmap_app omap_app; cbn; rewrite fmap_app //.
            }
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { rewrite insert_take_drop /=; last done; rewrite ?fmap_app ?omap_app; cbn.
              rewrite cons_app Permutation_app_swap_app; cbn.
              apply NoDup_cons; split.
              { rewrite /tid_stid_cur dom_list_to_map.
                erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
                rewrite fmap_app omap_app; cbn.
                intros Hin; eapply elem_of_list_to_set, is_fresh in Hin; ss.
              }
              revert Htl.
              erewrite <-(take_drop_middle tl stid_cur) at 1; eauto.
              rewrite fmap_app omap_app; cbn; rewrite fmap_app //.
            }
            { intros i; destruct (decide (i = stid_cur)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
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
              }
            }
          }
        }
        { (* Helping.help *)
          destruct (decide (fn = Helping.help mn)); subst.
          { (* Helping.help *)
            admit.
          }
          {
            rewrite no_help_prog //; destruct (LMod.prog _ fn) as [bd|]; cycle 1.
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
              { rewrite list_lookup_insert; ii; clarify; r; esplits; eauto.
                rewrite /ModTr.trans.
                admit.
              }
            }
          }
        }
      }
      { (* Spawn case *)
        ss.
        admit.
      }

      { (* Yield case *)
        admit.
      }

      { (* GetTid case *)
        admit.
      }

      destruct Hf as [[R [s [f' ->]]]|[R [e [f' ->]]]].
      { (* sput sget *)
        admit.
      }

      (* Take Choose IO case *)
      destruct e; admit.
    }

    (* Helpee case *)
    destruct p as [tid jid].
    apply lookup_lt_Some in Htid as Htid_cur.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [? [? [? [? [? [? [? [-> ->]]]]]]]]; ss.
    admit.
  Admitted.
      {

      }
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

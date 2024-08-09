Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import EventsRed Events.
Require Import IRed.
Require Import STS Behavior.
Require Import PCM IPM.
Require Import Skeleton Mod.


Set Implicit Arguments.

Section MID.
  
  Context {Σ: GRA.t}.

  Definition mput E `{stateE -< E} `{coreE -< E} (mr: Σ): itree E unit :=
    st <- trigger sGet;; '(mp, _) <- ((Any.split st)?);;
    trigger (sPut (Any.pair mp mr↑))
  .

  Definition mget E `{stateE -< E} `{coreE -< E}: itree E Σ :=
    st <- trigger sGet;; '(_, mr) <- ((Any.split st)?);;
    mr↓?
  .

  Definition pupdate E `{stateE -< E} `{coreE -< E} {X} (run: Any.t -> Any.t * X) : itree E X :=
    trigger (SUpdate (fun st => 
      match (Any.split st) with
      | Some (x, mr) => ((Any.pair (fst (run x)) mr), snd (run x))
      | None => run tt↑
      end
    ))
  .

  (* separate compilation path for module-state initialization. *)
  Definition assume_init {E} `{takeE -< E} (P: Prop): itree E unit := 
    trigger (Events.take P) ;;; Ret tt.

  Definition handle_init_cond P: stateT (Σ) (itree takeE) unit :=
  fun fr => (* skipped 'mget' from 'handle_Assume' *)
    r <- trigger (Events.take Σ);;
    assume_init (URA.wf (r ⋅ fr ));;;
    assume_init (Own r ⊢ P);;; 
    Ret (r ⋅ fr, tt).

  Definition cond_to_st (P: iProp): itree takeE Σ :=
    '(r, _) <- handle_init_cond P ε;; Ret r.        
  
  (* mid to tgt code *)
  Definition handle_stateE_tgt: stateE ~> itree modE :=
      (fun _ e =>
         match e with
         | SUpdate run => pupdate run
        end).

  Definition handle_Assume P: stateT (Σ) (itree modE) unit :=
    fun fr =>
      r <- trigger (Take Σ);;
      mr <- mget;; 
      assume (URA.wf (r ⋅ fr ⋅ mr));;;
      assume(Own r ⊢ P);;; 
      Ret (r ⋅ fr, tt).

  Definition handle_Guarantee P: stateT (Σ) (itree modE) unit :=
    fun fr =>
      '(r, fr', mr') <- trigger (Choose (Σ * Σ * Σ));;
      mr <- mget;;
      guarantee(Own (fr ⋅ mr) ⊢ #=> Own (r ⋅ fr' ⋅ mr'));;;
      guarantee(Own r ⊢ P);;;
      mput mr';;;
      Ret (fr', tt).

  Definition handle_agE_tgt: agE ~> stateT (Σ) (itree modE) :=
    fun _ e fr =>
      match e with
      | Assume P => handle_Assume P fr
      | Guarantee P => handle_Guarantee P fr
      end.    

  Definition interp_hp : itree hmodE ~> stateT Σ (itree modE) :=
      interp_state 
        (case_ (bif:=sum1) (handle_agE_tgt)
        (case_ (bif:=sum1) ((fun T X fr => '(fr', _) <- (handle_Guarantee (True%I) fr);; x <- trigger X;; Ret (fr', x)): _ ~> stateT Σ (itree modE)) 
        (case_ (bif:=sum1) ((fun T X fr => x <- handle_stateE_tgt X;; Ret (fr, x)): _ ~> stateT Σ (itree modE)) 
                           ((fun T X fr => x <- trigger X;; Ret (fr, x)): _ ~> stateT Σ (itree modE))))).

  Definition hp_fun_tail := (fun '(fr, x) => handle_Guarantee (True%I) fr ;;; Ret (x: Any.t)).

  Definition interp_hp_body (i: itree hmodE Any.t) (fr: Σ) : itree modE Any.t :=
    interp_hp i fr >>= hp_fun_tail.

  Definition interp_hp_fun (f: Any.t -> itree hmodE Any.t) : Any.t -> itree modE Any.t :=
    fun x => interp_hp_body (f x) ε.

End MID.

Section RED.
  (* itree reduction lemmas *)
  Context `{Σ: GRA.t}.

  Lemma interp_hp_bind
        (R S: Type)
        (s : itree hmodE R) (k : R -> itree hmodE S)
        fmr
    :
      interp_hp (s >>= k) fmr
      =
      st <- interp_hp s fmr;; interp_hp (k st.2) st.1.
  Proof.
    unfold interp_hp in *. eapply interp_state_bind.
  Qed.

  Lemma interp_hp_body_bind
        R (s : itree hmodE R) (k : R -> itree hmodE Any.t) fmr
    :
      interp_hp_body (s >>= k) fmr
      =
      '(fr,r) <- interp_hp s fmr;; interp_hp_body (k r) fr.
  Proof.
    unfold interp_hp_body. rewrite interp_hp_bind. grind. destruct x. eauto.
  Qed.


  Lemma interp_hp_tau
        (U: Type)
        (t : itree _ U)
        fmr
    :
      interp_hp (tau;; t) fmr
      =
      tau;; (interp_hp t fmr).
  Proof.
    unfold interp_hp in *. eapply interp_state_tau.
  Qed.

  Lemma interp_hp_ret
        (U: Type)
        (t: U)
        fmr
    :
      interp_hp (Ret t) fmr
      =
      Ret (fmr, t).
  Proof.
    unfold interp_hp in *. eapply interp_state_ret.
  Qed.

  Lemma interp_hp_call
        (R: Type)
        (i: callE R)
        fr
    :
      interp_hp (trigger i) fr
      =
      '(fr', _) <- handle_Guarantee (True%I:iProp) fr;; r <- trigger i;; tau;; Ret (fr', r).
  Proof.
    unfold interp_hp in *. grind.
  Qed.

  Lemma interp_hp_triggers
        (R: Type)
        (i: stateE R)
        fmr
    :
      interp_hp (trigger i) fmr
      =
      r <- handle_stateE_tgt i;; tau;; Ret (fmr, r).
  Proof.
    unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
  Qed.

  Lemma interp_hp_triggere
        (R: Type)
        (i: coreE R)
        fmr
    :
      interp_hp (trigger i) fmr
      =
      r <- trigger i;; tau;; Ret (fmr, r).
  Proof.
    unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
  Qed.

  Lemma interp_hp_triggerUB
        (R: Type)
        fmr
    :
      interp_hp (triggerUB) fmr
      =
      triggerUB (A:=Σ*R).
  Proof.
    unfold interp_hp, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
  Qed.

  Lemma interp_hp_triggerNB
        (R: Type)
        fmr
    :
      interp_hp (triggerNB) fmr
      =
      triggerNB (A:=Σ*R).
  Proof.
    unfold interp_hp, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
  Qed.

  Lemma interp_hp_unwrapU 
        (R: Type)
        (i: option R)
        fmr
    :
      interp_hp (@unwrapU hmodE _ _ i) fmr
      =
      r <- (unwrapU i);; Ret (fmr, r).
  Proof.
    unfold interp_hp, unwrapU in *. des_ifs.
    { etrans.
      { eapply interp_hp_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_hp_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma interp_hp_unwrapN
        (R: Type)
        (i: option R)
        fmr
    :
      interp_hp (@unwrapN hmodE _ _ i) fmr
      =
      r <- (unwrapN i);; Ret (fmr, r).
  Proof.
    unfold interp_hp, unwrapN in *. des_ifs.
    { etrans.
      { eapply interp_hp_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_hp_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma interp_hp_Assume
        P
        fmr
    :
      interp_hp (trigger (Assume P)) fmr
      =
      x <- handle_Assume P fmr ;; tau;; Ret x.
  Proof.
    unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
  Qed.

  Lemma interp_hp_Guarantee
        P
        fmr
    :
      interp_hp (trigger (Guarantee P)) fmr
      =
      x <- handle_Guarantee P fmr ;; tau;; Ret x.
  Proof.
    unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
  Qed.

  Lemma interp_hp_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
        fmr
    :
      interp_hp itr0 fmr
      =
      interp_hp itr1 fmr.
  Proof. subst; et. Qed.

  (* TODO: Same lemmas for other interps ( not defined yet. ) *)

  Global Program Instance interp_hp_rdb: red_database (mk_box (@interp_hp)) :=
    mk_rdb
      1
      (mk_box interp_hp_bind)
      (mk_box interp_hp_tau)
      (mk_box interp_hp_ret)
      (mk_box interp_hp_call)
      (mk_box interp_hp_triggere)
      (mk_box interp_hp_triggers)
      (mk_box interp_hp_triggers)
      (mk_box interp_hp_triggerUB)
      (mk_box interp_hp_triggerNB)
      (mk_box interp_hp_unwrapU)
      (mk_box interp_hp_unwrapN)
      (mk_box interp_hp_Assume)
      (mk_box interp_hp_Guarantee)
      (mk_box interp_hp_ext).
  
End RED.


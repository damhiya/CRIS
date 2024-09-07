Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import Events.
Require Import IRed.
Require Import STS Behavior.
Require Import PCM IPM.
Require Import Skeleton Mod.


Set Implicit Arguments.

Section MID.
  
  Context {Σ: GRA.t}.

  (* Consider moving into Any lib. *)
  (* Any.encode & Any.decode *)
  (* local states: [(k0, st0); (k1, st1); ... ] *)
  
  Fixpoint _alist_encode (st_list: alist key Any.t): Any.t :=
    match st_list with
    | [] => tt↑
    | (k,v) ::tl => 
      Any.pair (Any.pair k↑ v) (_alist_encode tl)
    end.

  Definition alist_encode st_list :=
    Any.pair (List.length st_list)↑ (_alist_encode st_list).

  Fixpoint _alist_decode (data: Any.t) (n: nat) : alist key Any.t :=
    match n with
    | S n' =>
        match Any.split data with
        | Some (kv, data') =>
            match Any.split kv with
            | Some (ka, v) =>
                match ka↓ with
                | Some k => (k,v) :: _alist_decode data' n'
                | None => []
                end
            | None => []
            end
        | None => []
        end
    | 0 => []
    end.

  Definition alist_decode st :=
    match Any.split st with
    | Some (na, data) =>
        match na↓ with
        | Some n => _alist_decode data n
        | None => []
        end
    | None => []
    end.

  Lemma alist_encode_decode st:
    alist_decode (alist_encode st) = st.
  Proof.
    unfold alist_encode, alist_decode.
    rewrite Any.pair_split; rewrite Any.upcast_downcast; eauto.
    induction st; s; eauto.
    destruct a.
    s; rewrite !Any.pair_split; rewrite Any.upcast_downcast; eauto.
    rewrite IHst. eauto.
  Qed.

  Definition mput_res E `{stateE -< E} `{coreE -< E} (mr: Σ): itree E unit :=
    st <- trigger sGet;; '(mp, _) <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑))
  .

  Definition mget_res E `{stateE -< E} `{coreE -< E}: itree E Σ :=
    st <- trigger sGet;; '(_, mr) <- (Any.split st)?;;
    mr↓?
  .

  Definition mput_kv E `{stateE -< E} `{coreE -< E} (k: key) (v: Any.t) : itree E unit :=
    st <- trigger sGet;; '(mp, mr) <- (Any.split st)?;;
    trigger (sPut (Any.pair (alist_encode (alist_upd k v (alist_decode mp))) mr))
  .

  Definition mget_kv E `{stateE -< E} `{coreE -< E} (k: key) : itree E Any.t :=
    st <- trigger sGet;; '(mp, _) <- (Any.split st)?;;
    Ret (or_else (alist_find k (alist_decode mp)) tt↑)
  .

  (* mid to tgt code *)  
  Definition handle_pgE_tgt : pgE ~> itree modE :=
      (fun _ e =>
         match e with
         | SPut k v => mput_kv k v
         | SGet k => mget_kv k
        end).

  Definition handle_Assume P: stateT (Σ) (itree modE) unit :=
    fun fr =>
      r <- trigger (Take Σ);;
      mr <- mget_res;; 
      assume (URA.wf (r ⋅ fr ⋅ mr));;;
      assume(Own r ⊢ P);;; 
      Ret (r ⋅ fr, tt).

  Definition handle_Guarantee P: stateT (Σ) (itree modE) unit :=
    fun fr =>
      '(r, fr', mr') <- trigger (Choose (Σ * Σ * Σ));;
      mr <- mget_res;;
      guarantee(Own (fr ⋅ mr) ⊢ #=> Own (r ⋅ fr' ⋅ mr'));;;
      guarantee(Own r ⊢ P);;;
      mput_res mr';;;
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
        (case_ (bif:=sum1) ((fun T e fr => x <- trigger e;; Ret (fr,x)): _ ~> stateT Σ (itree modE))
        (case_ (bif:=sum1) ((fun T e fr => '(fr', _) <- (handle_Guarantee (True%I) fr);; x <- trigger e;; Ret (fr', x)): _ ~> stateT Σ (itree modE)) 
        (case_ (bif:=sum1) ((fun T e fr => x <- handle_pgE_tgt e;; Ret (fr, x)): _ ~> stateT Σ (itree modE)) 
                           ((fun T e fr => x <- trigger e;; Ret (fr, x)): _ ~> stateT Σ (itree modE)))))).

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

  Lemma interp_hp_sch
        (R: Type)
        (i: schE R)
        fmr
    :
      interp_hp (trigger i) fmr
      =
      r <- trigger i;; tau;; Ret (fmr, r).
  Proof.
    unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
  Qed.
  
  Lemma interp_hp_triggers
        (R: Type)
        (i: pgE R)
        fmr
    :
      interp_hp (trigger i) fmr
      =
      r <- handle_pgE_tgt i;; tau;; Ret (fmr, r).
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
    unfold interp_hp, triggerUB in *.
    erewrite (bisimulation_is_eq _ _ (unfold_interp_state _ _ _)).
    cbn. grind.
  Qed.

  Lemma interp_hp_triggerNB
        (R: Type)
        fmr
    :
      interp_hp (triggerNB) fmr
      =
      triggerNB (A:=Σ*R).
  Proof.
    unfold interp_hp, triggerNB in *.
    erewrite (bisimulation_is_eq _ _ (unfold_interp_state _ _ _)).
    cbn. grind.
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
      (mk_box interp_hp_sch)      
      (mk_box interp_hp_triggere)
      (mk_box interp_hp_triggers)
      (mk_box interp_hp_triggerUB)
      (mk_box interp_hp_triggerNB)
      (mk_box interp_hp_unwrapU)
      (mk_box interp_hp_unwrapN)
      (mk_box interp_hp_Assume)
      (mk_box interp_hp_Guarantee)
      (mk_box interp_hp_ext).
  
End RED.


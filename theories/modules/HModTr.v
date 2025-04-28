Require Import Common.
Require Import Mod.

Set Implicit Arguments.

Module HModTr.
Section MID.

  Context {Σ : GRA}.

  (* Consider moving into Any lib. *)
  (* Any.encode & Any.decode *)
  (* local states : [(k0, st0); (k1, st1); ... ] *)
  Fixpoint _alist_encode (st_list : alist key Any.t) : Any.t :=
    match st_list with
    | [] => tt↑
    | (k,v) ::tl =>
      Any.pair (Any.pair k↑ v) (_alist_encode tl)
    end.

  Definition alist_encode st_list :=
    Any.pair (List.length st_list)↑ (_alist_encode st_list).

  Fixpoint _alist_decode (data : Any.t) (n : nat) : alist key Any.t :=
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

  Lemma alist_encode_decode st :
    alist_decode (alist_encode st) = st.
  Proof using.
    unfold alist_encode, alist_decode.
    rewrite Any.pair_split; rewrite Any.upcast_downcast; eauto.
    induction st; s; eauto.
    destruct a.
    s; rewrite !Any.pair_split; rewrite Any.upcast_downcast; eauto.
    rewrite IHst. eauto.
  Qed.

  Definition put_res `{stateE -< E} `{coreE -< E} (mr : Σ) : itree E unit :=
    st <- trigger sGet;; '(mp, _) :_ <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑)).

  Definition get_res `{stateE -< E} `{coreE -< E} : itree E Σ :=
    st <- trigger sGet;; '(_, mr) : _ <- (Any.split st)?;;
    mr↓?.

  Definition mput_kv E `{stateE -< E} `{coreE -< E} (k: key) (v: Any.t) : itree E unit :=
    st <- trigger sGet;;
    or_else (
        do '(mp, mr) <- Any.split st;
        Some (trigger (sPut (Any.pair (alist_encode (alist_upd k v (alist_decode mp))) mr)))
      )
      (Ret tt)
  .

  Definition mget_kv E `{stateE -< E} `{coreE -< E} (k: key) : itree E Any.t :=
    st <- trigger sGet;;
    or_else (
        do '(mp, _) <- Any.split st;
        Some (Ret (or_else (alist_find k (alist_decode mp)) tt↑))
      )
      (Ret tt↑)
  .

  (* mid to tgt code *)
  Definition handle_pgE : pgE ~> itree modE :=
    fun _ e =>
      match e with
      | SPut k v => mput_kv k v
      | SGet k => mget_kv k
      end.

  Definition handle_Assume (P : iProp Σ) : itree modE unit :=
    mr <- get_res;;
    mr' <- trigger (Take Σ);;
    assume (✓ mr' ∧ (Own mr' ==∗ P ∗ Own mr));;;
    put_res mr'.

  Definition handle_Guarantee (P : iProp Σ) : itree modE unit :=
    mr <- get_res;;
    mr' <- trigger (Choose Σ);;
    guarantee (✓ mr' ∧ (Own mr ==∗ P ∗ Own mr'));;;
    put_res mr'.

  Definition handle_agE : agE ~> itree modE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | Guarantee P => handle_Guarantee P
      end.

  Definition trans : itree hmodE ~> itree modE.
  Proof using.
    intros T; eapply interp; intros Te e.
    destruct e as [|[|[|[|]]]].
    { apply (handle_agE a). }
    { exact (trigger (inl1 s)). }
    { exact (trigger (inr1 (inl1 c))). }
    { exact (handle_pgE p). }
    { exact (trigger (inr1 (inr1 (inr1 c)))). }
  Defined.

  Definition trans_ktree (f : Any.t -> itree hmodE Any.t) : Any.t -> itree modE Any.t :=
    λ x, trans (f x).

  (**** Sandboxing ****)
  Definition handle_sandbox scopes : ∀ T, hmodE T -> (itree hmodE T + {X: Type & hmodE X * (X -> itree hmodE T)})%type :=
    λ T e, inr
      match e with
      | inr1 (inr1 (inr1 (inl1 (SPut (s, _) _)))) =>
          if existsb (String.eqb s) scopes
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inr1 (inr1 (inr1 (inl1 (SGet (s, _))))) =>
          if existsb (String.eqb s) scopes
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | _ => existT _ (e, fun v => Ret v)
      end.
  
  Definition sandbox {T} scopes (itr : itree hmodE T) :=
    interpV (handle_sandbox scopes) itr.

  Definition sandbox_body (kb : list string * (Any.t → itree hmodE Any.t)) :=
    λ arg, sandbox kb.1 (kb.2 arg).

End MID.
End HModTr.

Module HRed.
Section RED.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree hmodE R) (k : R -> itree hmodE S) :
    HModTr.trans (s >>= k) = st <- HModTr.trans s;; HModTr.trans (k st).
  Proof using. rewrite /HModTr.trans interp_bind //. Qed.

  Lemma tau (R : Type) (t : itree _ R) :
    HModTr.trans (tau;; t) = tau;; (HModTr.trans t).
  Proof using. rewrite /HModTr.trans interp_tau //. Qed.

  Lemma ret (R : Type) (t : R) :
    HModTr.trans (Ret t) = Ret t.
  Proof using. rewrite /HModTr.trans interp_ret //. Qed.

  Lemma call (R : Type) (c : callE R) :
    HModTr.trans (trigger c) = r <- trigger c;; tau;; Ret r.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma spawn fn arg :
    HModTr.trans (trigger (Spawn fn arg)) = r <- trigger (Spawn fn arg);; tau;; Ret r.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma yield tid :
    HModTr.trans (trigger (Yield tid)) = r <- trigger (Yield tid);; tau;; Ret r.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma pg (R : Type) (i : pgE R) :
    HModTr.trans (trigger i) = r <- HModTr.handle_pgE i;; tau;; Ret r.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma core (R : Type) (i : coreE R) :
    HModTr.trans (trigger i) = r <- trigger i;; tau;; Ret r.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma triggerUB (R : Type) :
    HModTr.trans (triggerUB) = triggerUB (A:=R).
  Proof using.
    rewrite /HModTr.trans /triggerUB interp_bind interp_trigger; grind.
  Qed.

  Lemma triggerNB (R : Type) :
    HModTr.trans (triggerNB) = triggerNB (A:=R).
  Proof using.
    rewrite /HModTr.trans /triggerNB interp_bind interp_trigger; grind.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
    HModTr.trans (@unwrapU hmodE _ _ i) = r <- (unwrapU i);; Ret r.
  Proof using.
    rewrite /HModTr.trans /unwrapU; des_ifs; grind; eauto using triggerUB.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    HModTr.trans (@unwrapN hmodE _ _ i) = r <- (unwrapN i);; Ret r.
  Proof using.
    rewrite /HModTr.trans /unwrapN; des_ifs; grind; eauto using triggerNB.
  Qed.

  Lemma Assume P :
    HModTr.trans (trigger (Assume P)) = x <- HModTr.handle_Assume P;; tau;; Ret x.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma Guarantee P :
    HModTr.trans (trigger (Guarantee P)) = x <- HModTr.handle_Guarantee P;; tau;; Ret x.
  Proof using. rewrite /HModTr.trans interp_trigger //. Qed.

  Lemma ext R (itr0 itr1 : itree _ R) (EQ : itr0 = itr1) :
    HModTr.trans itr0 = HModTr.trans itr1.
  Proof using. subst; et. Qed.

  (* TODO : Same lemmas for other interps ( not defined yet. ) *)

  Global Program Instance rdb : red_database (mk_box (@HModTr.trans)) :=
    mk_rdb
      0
      (mk_box bind)
      (mk_box tau)
      (mk_box ret)
      (mk_box call)
      (* (mk_box spawn) *)
      (mk_box yield)
      (* (mk_box tid) *)
      (mk_box core)
      (mk_box pg)
      (mk_box triggerUB)
      (mk_box triggerNB)
      (mk_box unwrapU)
      (mk_box unwrapN)
      (mk_box Assume)
      (mk_box Guarantee)
      (mk_box ext).

End RED.
End HRed.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind A B scopes (itr : itree hmodE A) (ktr : A → itree hmodE B) :
    HModTr.sandbox scopes (itr >>= ktr)
    = a <- (HModTr.sandbox scopes itr);; (HModTr.sandbox scopes (ktr a)).
  Proof using. unfold HModTr.sandbox. rewrite interpV_bind; eauto. Qed.

  Lemma tau A scopes (itr : itree hmodE A) :
    HModTr.sandbox scopes (tau;; itr) = tau;; (HModTr.sandbox scopes itr).
  Proof using. unfold HModTr.sandbox. rewrite interpV_tau; eauto. Qed.

  Lemma ret A (a : A) scopes :
    HModTr.sandbox scopes (Ret a) = Ret a.
  Proof using. unfold HModTr.sandbox. rewrite interpV_ret; eauto. Qed.

  Lemma vis_core {X R} (e : coreE X) scopes (k : X -> itree hmodE R) :
    HModTr.sandbox scopes (vis e k) = vis e (fun x => HModTr.sandbox scopes (k x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_ag {X R} scopes (e : agE X) (ktr : X -> itree hmodE R) :
    HModTr.sandbox scopes (vis e ktr) = vis e (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_sch {X R} scopes (e : schE X) (ktr : X -> itree hmodE R) :
    HModTr.sandbox scopes (vis e ktr) = vis e (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_call {X R} scopes (e : callE X) (ktr : X -> itree hmodE R) :
    HModTr.sandbox scopes (vis e ktr) = vis e (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_put {R} scopes k v (ktr : () -> itree hmodE R) :
    HModTr.sandbox scopes (vis (SPut k v) ktr) =
      if existsb (String.eqb k.1) scopes
      then vis (SPut k v) (fun x => HModTr.sandbox scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_get {R} k scopes (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox scopes (vis (SGet k) ktr) =
      if existsb (String.eqb k.1) scopes
      then vis (SGet k) (fun x => HModTr.sandbox scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Definition putSB {R} scopes k v (itr : itree hmodE R) : itree hmodE R :=
    HModTr.sandbox scopes (trigger (SPut k v));;; itr.

  Definition getSB {R} scopes k (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    HModTr.sandbox scopes (trigger (SGet k)) >>= ktr.

  Lemma SPut_putSB {R} scopes k v (ktr : () -> itree hmodE R) :
    HModTr.sandbox scopes (vis (SPut k v) ktr) = putSB scopes k v (HModTr.sandbox scopes (ktr tt)).
  Proof using.
    destruct k. unfold putSB, trigger. rewrite !vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities x. destruct x.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma putSB_SPut {R} scopes k v (itr : itree hmodE R) :
    putSB scopes k v itr = HModTr.sandbox scopes (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed.

  Lemma putSB_bind {T U} scopes k v (itr : itree hmodE T) (ktr : T -> itree hmodE U) :
    putSB scopes k v itr >>= ktr = putSB scopes k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma SGet_getSB {R} scopes k (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox scopes (vis (SGet k) ktr) = getSB scopes k (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    destruct k. unfold getSB, trigger. rewrite !vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma getSB_SGet {R} scopes k (ktr : Any.t -> itree hmodE R) :
    getSB scopes k ktr = x <- HModTr.sandbox scopes (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma getSB_bind {T U} scopes k (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    getSB scopes k ktr1 >>= ktr2 = getSB scopes k (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma assumeK {R} scopes P (itr : itree hmodE R) :
    HModTr.sandbox scopes (assumeK P itr) = assumeK P (HModTr.sandbox scopes itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma guaranteeK {R} scopes P (itr : itree hmodE R) :
    HModTr.sandbox scopes (guaranteeK P itr) = guaranteeK P (HModTr.sandbox scopes itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma unwrapUK {X R} scopes x (ktr : X -> itree hmodE R) :
    HModTr.sandbox scopes (unwrapUK x ktr) = unwrapUK x (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} scopes x (ktr : X -> itree hmodE R) :
    HModTr.sandbox scopes (unwrapNK x ktr) = unwrapNK x (fun x => HModTr.sandbox scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call {A} (e : callE A) scopes :
    HModTr.sandbox scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_call.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma put scopes k v :
    HModTr.sandbox scopes (trigger (SPut k v)) =
      if existsb (String.eqb k.1) scopes
      then trigger (SPut k v)
      else triggerUB.
  Proof using.
    rewrite vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma get scopes k :
    HModTr.sandbox scopes (trigger (SGet k)) =
      if existsb (String.eqb k.1) scopes
      then trigger (SGet k)
      else triggerUB.
  Proof using.
    rewrite vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma core T scopes (e : coreE T) :
    HModTr.sandbox scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_core.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma ag {A} (e : agE A) scopes :
    HModTr.sandbox scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_ag.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma sch {A} (e : schE A) scopes :
    HModTr.sandbox scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_sch.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma unwrapU R scopes (r : option R) :
    HModTr.sandbox scopes (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - unfold triggerUB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R scopes (r : option R) :
    HModTr.sandbox scopes (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - unfold triggerNB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm scopes P :
    HModTr.sandbox scopes (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind core ret. eauto.
  Qed.

  Lemma guar scopes P :
    HModTr.sandbox scopes (guarantee P) = guarantee P.
  Proof using.
    unfold guarantee. rewrite bind core ret. eauto.
  Qed.

End SBRed. End SBRed.

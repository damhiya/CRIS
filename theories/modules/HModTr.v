Require Import Common.
Require Import Mod.

Set Implicit Arguments.

Section WMask.

  Definition wmask_all : string->bool := fun _ => true.

  Definition wmask_list (fns: list string) : string->bool :=
    fun f => (existsb (String.eqb f) fns).

  Definition wmask_or (msk1 msk2: string->bool) :=
    fun fn => msk1 fn || msk2 fn.

  Definition wmask_and (msk1 msk2: string->bool) :=
    fun fn => msk1 fn && msk2 fn.

  Definition wmask_sub (msk1 msk2: string→bool) :=
    ∀ fn, msk1 fn → msk2 fn.

End WMask.

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

  Definition put_res (mr : Σ) : itree modE unit :=
    st <- trigger sGet;; '(mp, _) :_ <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑)).

  Definition get_res {R} (k: Σ → itree modE R) : itreeV modE R :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      '(_, mr) : _ <- (Any.split st)?;;
      r <- mr↓?;; k r)).

  Definition mput_kv (k: key) (v: Any.t) : itreeV modE unit :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      or_else (
        do '(mp, mr) <- Any.split st;
        Some (trigger (sPut (Any.pair (alist_encode (alist_upd k v (alist_decode mp))) mr)))
      )
      ( Ret tt )))
  .

  Definition mget_kv (k: key) : itreeV modE Any.t :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      or_else (
        do '(mp, _) <- Any.split st;
        Some (Ret (or_else (alist_find k (alist_decode mp)) tt↑))
      )
      ( Ret tt↑ )))
  .

  (* mid to tgt code *)
  Definition handle_pgE : pgE ~> itreeV modE :=
    fun _ e =>
      match e with
      | SPut k v => mput_kv k v
      | SGet k => mget_kv k
      end.

  Definition handle_Assume (P : iProp Σ) : itreeV modE unit :=
    get_res (fun mr =>
    mr' <- trigger (Take Σ);;
    assume (✓ mr' ∧ (Own mr' ==∗ P ∗ Own mr));;;
    put_res mr').

  Definition handle_Guarantee (P : iProp Σ) : itreeV modE unit :=
    get_res (fun mr =>
    mr' <- trigger (Choose Σ);;
    guarantee (✓ mr' ∧ (Own mr ==∗ P ∗ Own mr'));;;
    put_res mr').

  Definition handle_agE : agE ~> itreeV modE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | Guarantee P => handle_Guarantee P
      end.

  Definition handle_hmodE : hmodE ~> itreeV modE :=
    λ T e,
      match e with
      | inl1 ag => handle_agE ag
      | inr1 (inl1 c) => inr (existT T (subevent _ c, fun r => Ret r))
      | inr1 (inr1 (inl1 pg)) => handle_pgE pg
      | inr1 (inr1 (inr1 c)) => inr (existT T (subevent _ c, fun r => Ret r))
      end.

  Definition trans : itree hmodE ~> itree modE :=
    interpV handle_hmodE.

  Definition trans_ktree (f : Any.t -> itree hmodE Any.t) : Any.t -> itree modE Any.t :=
    λ x, trans (f x).

  (**** Sandboxing ****)
  Definition handle_sandbox (mask: string->bool) scopes : ∀ T, hmodE T -> (itree hmodE T + {X: Type & hmodE X * (X -> itree hmodE T)})%type :=
    λ T e, inr
      match e with
      | inr1 (inr1 (inl1 (SPut (s, _) _))) =>
          if existsb (String.eqb s) scopes
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inr1 (inr1 (inl1 (SGet (s, _)))) =>
          if existsb (String.eqb s) scopes
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inr1 (inl1 (Call f _)) =>
          if mask f
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inr1 (inl1 (Spawn f _)) =>
          if mask f
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | _ => existT _ (e, fun v => Ret v)
      end.

  Definition sandbox {T} mask scopes (itr : itree hmodE T) :=
    interpV (handle_sandbox mask scopes) itr.

  Definition sandbox_body (kb : (string->bool) * list string * (Any.t → itree hmodE Any.t)) :=
    λ arg, sandbox kb.1.1 kb.1.2 (kb.2 arg).

End MID.
End HModTr.

Module HRed.
Section RED.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree hmodE R) (k : R -> itree hmodE S) :
    HModTr.trans (s >>= k) = st <- HModTr.trans s;; HModTr.trans (k st).
  Proof using. rewrite /HModTr.trans interpV_bind //. Qed.

  Lemma tau (R : Type) (t : itree _ R) :
    HModTr.trans (tau;; t) = tau;; (HModTr.trans t).
  Proof using. rewrite /HModTr.trans interpV_tau //. Qed.

  Lemma ret (R : Type) (t : R) :
    HModTr.trans (Ret t) = Ret t.
  Proof using. rewrite /HModTr.trans interpV_ret //. Qed.

  Lemma call (R : Type) (c : callE R) :
    HModTr.trans (trigger c) = trigger c.
  Proof using. rewrite /HModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma spawn fn arg :
    HModTr.trans (trigger (Spawn fn arg)) = trigger (Spawn fn arg).
  Proof using. rewrite /HModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma yield tid :
    HModTr.trans (trigger (Yield tid)) = trigger (Yield tid).
  Proof using. rewrite /HModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma pg (R : Type) (i : pgE R) :
    HModTr.trans (trigger i) = itreeV_itree (HModTr.handle_pgE i).
  Proof using. rewrite /HModTr.trans interpV_trigger //. Qed.

  Lemma core (R : Type) (i : coreE R) :
    HModTr.trans (trigger i) = trigger i.
  Proof using. rewrite /HModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma triggerUB (R : Type) :
    HModTr.trans (triggerUB) = triggerUB (A:=R).
  Proof using.
    rewrite /HModTr.trans /triggerUB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma triggerNB (R : Type) :
    HModTr.trans (triggerNB) = triggerNB (A:=R).
  Proof using.
    rewrite /HModTr.trans /triggerNB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
    HModTr.trans (@unwrapU hmodE _ _ i) = unwrapU i.
  Proof using.
    rewrite /HModTr.trans /unwrapU; des_ifs; s; try rewrite interpV_ret; eauto using triggerUB.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    HModTr.trans (@unwrapN hmodE _ _ i) = unwrapN i.
  Proof using.
    rewrite /HModTr.trans /unwrapN; des_ifs; s; try rewrite interpV_ret; eauto using triggerNB.
  Qed.

  Lemma Assume P :
    HModTr.trans (trigger (Assume P)) = itreeV_itree (HModTr.handle_Assume P).
  Proof using. rewrite /HModTr.trans interpV_trigger //. Qed.

  Lemma Guarantee P :
    HModTr.trans (trigger (Guarantee P)) = itreeV_itree (HModTr.handle_Guarantee P).
  Proof using. rewrite /HModTr.trans interpV_trigger //. Qed.

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

  Lemma bind A B mask scopes (itr : itree hmodE A) (ktr : A → itree hmodE B) :
    HModTr.sandbox mask scopes (itr >>= ktr)
    = a <- (HModTr.sandbox mask scopes itr);; (HModTr.sandbox mask scopes (ktr a)).
  Proof using. unfold HModTr.sandbox. rewrite interpV_bind; eauto. Qed.

  Lemma tau A mask scopes (itr : itree hmodE A) :
    HModTr.sandbox mask scopes (tau;; itr) = tau;; (HModTr.sandbox mask scopes itr).
  Proof using. unfold HModTr.sandbox. rewrite interpV_tau; eauto. Qed.

  Lemma ret A (a : A) mask scopes :
    HModTr.sandbox mask scopes (Ret a) = Ret a.
  Proof using. unfold HModTr.sandbox. rewrite interpV_ret; eauto. Qed.

  Lemma vis_core {X R} (e : coreE X) mask scopes (k : X -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis e k) = vis e (fun x => HModTr.sandbox mask scopes (k x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_ag {X R} mask scopes (e : agE X) (ktr : X -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis e ktr) = vis e (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_yield {R} mask scopes tid (ktr : () -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (Yield tid) ktr) = vis (Yield tid) (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
               
  Lemma vis_spawn {R} mask scopes f a (ktr : nat -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (Spawn f a) ktr) =
      if mask f
      then vis (Spawn f a) (fun x => HModTr.sandbox mask scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_call {R} mask scopes f a (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (Call f a) ktr) =
      if mask f
      then vis (Call f a) (fun x => HModTr.sandbox mask scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_put {R} mask scopes k v (ktr : () -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (SPut k v) ktr) =
      if existsb (String.eqb k.1) scopes
      then vis (SPut k v) (fun x => HModTr.sandbox mask scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_get {R} k mask scopes (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (SGet k) ktr) =
      if existsb (String.eqb k.1) scopes
      then vis (SGet k) (fun x => HModTr.sandbox mask scopes (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold HModTr.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Definition putSB {R} mask scopes k v (itr : itree hmodE R) : itree hmodE R :=
    HModTr.sandbox mask scopes (trigger (SPut k v));;; itr.

  Definition getSB {R} mask scopes k (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    HModTr.sandbox mask scopes (trigger (SGet k)) >>= ktr.

  Lemma SPut_putSB {R} mask scopes k v (ktr : () -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (SPut k v) ktr) = putSB mask scopes k v (HModTr.sandbox mask scopes (ktr tt)).
  Proof using.
    destruct k. unfold putSB, trigger. rewrite !vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities x. destruct x.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma putSB_SPut {R} mask scopes k v (itr : itree hmodE R) :
    putSB mask scopes k v itr = HModTr.sandbox mask scopes (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed.

  Lemma putSB_bind {T U} mask scopes k v (itr : itree hmodE T) (ktr : T -> itree hmodE U) :
    putSB mask scopes k v itr >>= ktr = putSB mask scopes k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma SGet_getSB {R} mask scopes k (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (SGet k) ktr) = getSB mask scopes k (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    destruct k. unfold getSB, trigger. rewrite !vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma getSB_SGet {R} mask scopes k (ktr : Any.t -> itree hmodE R) :
    getSB mask scopes k ktr = x <- HModTr.sandbox mask scopes (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma getSB_bind {T U} mask scopes k (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    getSB mask scopes k ktr1 >>= ktr2 = getSB mask scopes k (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition callSB {R} mask scopes f a (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    HModTr.sandbox mask scopes (trigger (Call f a)) >>= ktr.

  Lemma Call_callSB {R} mask scopes f a (ktr : Any.t -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (Call f a) ktr) = callSB mask scopes f a (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    unfold callSB, trigger. rewrite !vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma callSB_Call {R} mask scopes f a (ktr : Any.t -> itree hmodE R) :
    callSB mask scopes f a ktr = x <- HModTr.sandbox mask scopes (trigger (Call f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma callSB_bind {T U} mask scopes f a (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    callSB mask scopes f a ktr1 >>= ktr2 = callSB mask scopes f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold callSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition spawnSB {R} mask scopes f a (ktr : _ -> itree hmodE R) : itree hmodE R :=
    HModTr.sandbox mask scopes (trigger (Spawn f a)) >>= ktr.

  Lemma Spawn_spawnSB {R} mask scopes f a (ktr : _ -> itree hmodE R) :
    HModTr.sandbox mask scopes (vis (Spawn f a) ktr) = spawnSB mask scopes f a (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    unfold spawnSB, trigger. rewrite !vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma spawnSB_Spawn {R} mask scopes f a (ktr : _ -> itree hmodE R) :
    spawnSB mask scopes f a ktr = x <- HModTr.sandbox mask scopes (trigger (Spawn f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma spawnSB_bind {T U} mask scopes f a (ktr1 : _ -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    spawnSB mask scopes f a ktr1 >>= ktr2 = spawnSB mask scopes f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold spawnSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma assumeK {R} mask scopes P (itr : itree hmodE R) :
    HModTr.sandbox mask scopes (assumeK P itr) = assumeK P (HModTr.sandbox mask scopes itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma guaranteeK {R} mask scopes P (itr : itree hmodE R) :
    HModTr.sandbox mask scopes (guaranteeK P itr) = guaranteeK P (HModTr.sandbox mask scopes itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma unwrapUK {X R} mask scopes x (ktr : X -> itree hmodE R) :
    HModTr.sandbox mask scopes (unwrapUK x ktr) = unwrapUK x (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} mask scopes x (ktr : X -> itree hmodE R) :
    HModTr.sandbox mask scopes (unwrapNK x ktr) = unwrapNK x (fun x => HModTr.sandbox mask scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call f a mask scopes :
    HModTr.sandbox mask scopes (trigger (Call f a)) =
      if mask f
      then trigger (Call f a)
      else triggerUB.
  Proof using.
    rewrite vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma put mask scopes k v :
    HModTr.sandbox mask scopes (trigger (SPut k v)) =
      if existsb (String.eqb k.1) scopes
      then trigger (SPut k v)
      else triggerUB.
  Proof using.
    rewrite vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma get mask scopes k :
    HModTr.sandbox mask scopes (trigger (SGet k)) =
      if existsb (String.eqb k.1) scopes
      then trigger (SGet k)
      else triggerUB.
  Proof using.
    rewrite vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma core T mask scopes (e : coreE T) :
    HModTr.sandbox mask scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_core.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma ag {A} (e : agE A) mask scopes :
    HModTr.sandbox mask scopes (trigger e) = trigger e.
  Proof using.
    rewrite vis_ag.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma yield mask scopes tid:
    HModTr.sandbox mask scopes (trigger (Yield tid)) = trigger (Yield tid).
  Proof using.
    rewrite vis_yield.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma spawn f a mask scopes :
    HModTr.sandbox mask scopes (trigger (Spawn f a)) =
      if mask f
      then trigger (Spawn f a)
      else triggerUB.
  Proof using.
    rewrite vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.
  
  Lemma unwrapU R mask scopes (r : option R) :
    HModTr.sandbox mask scopes (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - unfold triggerUB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R mask scopes (r : option R) :
    HModTr.sandbox mask scopes (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - unfold triggerNB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm mask scopes P :
    HModTr.sandbox mask scopes (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind core ret. eauto.
  Qed.

  Lemma guar mask scopes P :
    HModTr.sandbox mask scopes (guarantee P) = guarantee P.
  Proof using.
    unfold guarantee. rewrite bind core ret. eauto.
  Qed.

End SBRed. End SBRed.

Section Properties.

  Context `{Σ: GRA}.

  Lemma sandbox_sandbox {R} (t: itree hmodE R) (msk msk':_→bool) sc sc'
    (INCL: incl sc sc')
    (SUB: wmask_sub msk msk')
    :
    HModTr.sandbox msk' sc' (HModTr.sandbox msk sc t) = HModTr.sandbox msk sc t.
  Proof using.
    eapply bisim_is_eq.
    eapply gpaco2_init with (clo:=eqitC _ _ _); eauto with paco.
    revert R t sc sc' INCL. gcofix CIH. i.
    rewrite (bisim_is_eq (itree_eta t)). destruct (observe t).
    { rewrite !SBRed.ret. eapply Reflexive_eqit_gen. et. }
    { rewrite !SBRed.tau. gstep. econs. gbase. et. }

    rewrite -bind_trigger !SBRed.bind.
    destruct e; [ |destruct p;
                   [destruct c|destruct s; [destruct p|]]].
    + rewrite !SBRed.ag. gstep. rewrite !bind_trigger. econs.
      i. gbase. et.
    + rewrite !SBRed.call. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite !SBRed.bind !SBRed.core. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.call. des_ifs; cycle 1.
      { eapply SUB in Heq. rewrite Heq0 in Heq. ss. }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.spawn. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite !SBRed.bind !SBRed.core. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.spawn. des_ifs; cycle 1.
      { eapply SUB in Heq. rewrite Heq0 in Heq. ss. }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.yield.
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.put. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite !SBRed.bind !SBRed.core. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.put. des_ifs; cycle 1.
      { exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        apply INCL in Heq.
        hexploit (proj2 (existsb_exists (String.eqb k0.1) sc')).
        { esplits; et. apply String.eqb_eq. et. }
        i. rewrite H in Heq0. ss.
      }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.get. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite !SBRed.bind !SBRed.core. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.get. des_ifs; cycle 1.
      { exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        apply INCL in Heq.
        hexploit (proj2 (existsb_exists (String.eqb k0.1) sc')).
        { esplits; et. apply String.eqb_eq. et. }
        i. rewrite H in Heq0. ss.
      }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.core.
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
  Qed.
End Properties.

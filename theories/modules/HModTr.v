Require Import Common.
Require Import FSpec Mod.

Set Implicit Arguments.

Module HModTr.
Section MID.

  Context `{Σ : GRA}.

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

  Definition handle_AssumePrecise (P : iProp Σ) : itreeV modE unit :=
    get_res (fun mr =>
    pr <- trigger (Choose Σ);;
    mr' <- trigger (Choose Σ);;
    guarantee (Own mr ==∗ □ ((Own pr ==∗ P) ∗ (P ==∗ Own pr)) ∗ Own mr');;;
    assume (✓ (pr ⋅ mr'));;;
    put_res (pr ⋅ mr')).

  Definition handle_Guarantee (P : iProp Σ) : itreeV modE unit :=
    get_res (fun mr =>
    mr' <- trigger (Choose Σ);;
    guarantee (✓ mr' ∧ (Own mr ==∗ P ∗ Own mr'));;;
    put_res mr').

  Definition handle_agE : agE ~> itreeV modE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | AssumePrecise P => handle_AssumePrecise P
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

  Definition trans_ktree (f : Any.t → itree hmodE Any.t) : Any.t → itree modE Any.t :=
    λ x, trans (f x).

End MID.
End HModTr.

Module HRed.
Section RED.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree hmodE R) (k : R → itree hmodE S) :
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

  Lemma AssumePrecise P :
    HModTr.trans (trigger (AssumePrecise P)) = itreeV_itree (HModTr.handle_AssumePrecise P).
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

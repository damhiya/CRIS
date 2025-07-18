Require Import Common.
Require Import FSpec LMod.

Set Implicit Arguments.

Module ModTr.
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

  Definition put_res (mr : Σ) : itree lmodE unit :=
    st <- trigger sGet;; '(mp, _) :_ <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑)).

  Definition get_res {R} (k: Σ → itree lmodE R) : itreeV lmodE R :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      '(_, mr) : _ <- (Any.split st)?;;
      r <- mr↓?;; k r)).

  Definition mput_kv (k: key) (v: Any.t) : itreeV lmodE unit :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      or_else (
        do '(mp, mr) <- Any.split st;
        Some (trigger (sPut (Any.pair (alist_encode (alist_upd k v (alist_decode mp))) mr)))
      )
      ( Ret tt )))
  .

  Definition mget_kv (k: key) : itreeV lmodE Any.t :=
    inr (existT Any.t (subevent _ sGet, fun st =>
      or_else (
        do '(mp, _) <- Any.split st;
        Some (Ret (or_else (alist_find k (alist_decode mp)) tt↑))
      )
      ( Ret tt↑ )))
  .

  (* mid to tgt code *)
  Definition handle_pgE : pgE ~> itreeV lmodE :=
    fun _ e =>
      match e with
      | SPut k v => mput_kv k v
      | SGet k => mget_kv k
      end.

  Definition handle_Assume (P : iProp Σ) : itreeV lmodE unit :=
    get_res (fun mr =>
    mr' <- trigger (Take Σ);;
    assume (✓ mr' ∧ (Own mr' ==∗ P ∗ Own mr));;;
    put_res mr').

  Definition handle_AssumePrecise (P : iProp Σ) : itreeV lmodE unit :=
    get_res (fun mr =>
    pr <- trigger (Choose Σ);;
    mr' <- trigger (Choose Σ);;
    guarantee (Own mr ==∗ □ ((Own pr ==∗ P) ∗ (P ==∗ Own pr)) ∗ Own mr');;;
    assume (✓ (pr ⋅ mr'));;;
    put_res (pr ⋅ mr')).

  Definition handle_Guarantee (P : iProp Σ) : itreeV lmodE unit :=
    get_res (fun mr =>
    mr' <- trigger (Choose Σ);;
    guarantee (✓ mr' ∧ (Own mr ==∗ P ∗ Own mr'));;;
    put_res mr').

  Definition handle_agE : agE ~> itreeV lmodE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | AssumePrecise P => handle_AssumePrecise P
      | Guarantee P => handle_Guarantee P
      end.

  Definition handle_crisE : crisE ~> itreeV lmodE :=
    λ T e,
      match e with
      | inl1 ag => handle_agE ag
      | inr1 (inl1 c) => inr (existT T (subevent _ c, fun r => Ret r))
      | inr1 (inr1 (inl1 pg)) => handle_pgE pg
      | inr1 (inr1 (inr1 c)) => inr (existT T (subevent _ c, fun r => Ret r))
      end.

  Definition trans : itree crisE ~> itree lmodE :=
    interpV handle_crisE.

  Definition trans_ktree (f : Any.t → itree crisE Any.t) : Any.t → itree lmodE Any.t :=
    λ x, trans (f x).

End MID.
End ModTr.

Module Red.
Section RED.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    ModTr.trans (s >>= k) = st <- ModTr.trans s;; ModTr.trans (k st).
  Proof using. rewrite /ModTr.trans interpV_bind //. Qed.

  Lemma tau (R : Type) (t : itree _ R) :
    ModTr.trans (tau;; t) = tau;; (ModTr.trans t).
  Proof using. rewrite /ModTr.trans interpV_tau //. Qed.

  Lemma ret (R : Type) (t : R) :
    ModTr.trans (Ret t) = Ret t.
  Proof using. rewrite /ModTr.trans interpV_ret //. Qed.

  Lemma call (R : Type) (c : callE R) :
    ModTr.trans (trigger c) = trigger c.
  Proof using. rewrite /ModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma spawn fn arg :
    ModTr.trans (trigger (Spawn fn arg)) = trigger (Spawn fn arg).
  Proof using. rewrite /ModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma yield tid :
    ModTr.trans (trigger (Yield tid)) = trigger (Yield tid).
  Proof using. rewrite /ModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma pg (R : Type) (i : pgE R) :
    ModTr.trans (trigger i) = itreeV_itree (ModTr.handle_pgE i).
  Proof using. rewrite /ModTr.trans interpV_trigger //. Qed.

  Lemma core (R : Type) (i : coreE R) :
    ModTr.trans (trigger i) = trigger i.
  Proof using. rewrite /ModTr.trans interpV_trigger. s. ired. et. Qed.

  Lemma triggerUB (R : Type) :
    ModTr.trans (triggerUB) = triggerUB (A:=R).
  Proof using.
    rewrite /ModTr.trans /triggerUB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma triggerNB (R : Type) :
    ModTr.trans (triggerNB) = triggerNB (A:=R).
  Proof using.
    rewrite /ModTr.trans /triggerNB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
    ModTr.trans (@unwrapU crisE _ _ i) = unwrapU i.
  Proof using.
    rewrite /ModTr.trans /unwrapU; des_ifs; s; try rewrite interpV_ret; eauto using triggerUB.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    ModTr.trans (@unwrapN crisE _ _ i) = unwrapN i.
  Proof using.
    rewrite /ModTr.trans /unwrapN; des_ifs; s; try rewrite interpV_ret; eauto using triggerNB.
  Qed.

  Lemma Assume P :
    ModTr.trans (trigger (Assume P)) = itreeV_itree (ModTr.handle_Assume P).
  Proof using. rewrite /ModTr.trans interpV_trigger //. Qed.

  Lemma AssumePrecise P :
    ModTr.trans (trigger (AssumePrecise P)) = itreeV_itree (ModTr.handle_AssumePrecise P).
  Proof using. rewrite /ModTr.trans interpV_trigger //. Qed.
  
  Lemma Guarantee P :
    ModTr.trans (trigger (Guarantee P)) = itreeV_itree (ModTr.handle_Guarantee P).
  Proof using. rewrite /ModTr.trans interpV_trigger //. Qed.

  Lemma ext R (itr0 itr1 : itree _ R) (EQ : itr0 = itr1) :
    ModTr.trans itr0 = ModTr.trans itr1.
  Proof using. subst; et. Qed.

  (* TODO : Same lemmas for other interps ( not defined yet. ) *)

  Global Program Instance rdb : red_database (mk_box (@ModTr.trans)) :=
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
End Red.

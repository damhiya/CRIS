Require Import Common FSpec LMod.

Module ModTr. Section MID.
  Context `{Σ : GRA}.

  (* Consider moving into Any lib. *)
  Fixpoint _state_encode (st_list : list (key * option Any.t)) : Any.t :=
    match st_list with
    | [] => tt↑
    | (k, Some v) :: tl => Any.pair (Any.pair k↑ v) (_state_encode tl)
    | (k, None) :: tl => _state_encode tl
    end.

  (* Definition alist_encode st_list :=
    Any.pair (List.length st_list)↑ (_alist_encode st_list). *)

  (* Encode states into Any.t for state interpretation *)
  Definition state_encode (st : gmap key (option Any.t)) : Any.t :=
    Any.pair (size st)↑ (_state_encode (map_to_list st)).

  Fixpoint _state_decode (data : Any.t) (n : nat) : gmap key (option Any.t) :=
    match n with
    | S n' =>
        match Any.split data with
        | Some (kv, data') =>
            match Any.split kv with
            | Some (ka, v) =>
                match ka↓ with
                | Some k => <[k := Some v]> (_state_decode data' n')
                | None => ∅
                end
            | None => ∅
            end
        | None => ∅
        end
    | 0 => ∅
    end.

  Definition state_decode (st : Any.t) : gmap key (option Any.t) :=
    match Any.split st with
    | Some (na, data) =>
        match na↓ with
        | Some n => _state_decode data n
        | None => ∅
        end
    | None => ∅
    end.

  Lemma state_encode_decode (st : gmap key (option Any.t)) :
    map_Forall (λ _ v, is_Some v) st →
    state_decode (state_encode st) = st.
  Proof using.
    rewrite /state_decode /state_encode Any.pair_split Any.upcast_downcast.
    rewrite -{3 4}(list_to_map_to_list st) map_Forall_to_list map_size_list_to_map; cycle 1.
    { apply NoDup_fst_map_to_list. }
    generalize (map_to_list st) as st'; clear st.
    induction 1 as [|[k [v|]] tl Hs Hwf]; ss; [|inv Hs].
    rewrite ?Any.pair_split Any.upcast_downcast IHHwf //.
  Qed.

  Definition put_res (mr : Σ) : itree lmodE unit :=
    st <- trigger sGet;;
    '(mp, _) :_ <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑)).

  Definition get_res {R} (k : Σ → itree lmodE R) : itreeV lmodE R :=
    inr (existT Any.t (subevent _ sGet, λ st,
      '(_, mr) : _ <- (Any.split st)?;;
      r <- mr↓?;; k r)).

  Definition mput_kv (k : key) (v : Any.t) : itreeV lmodE unit :=
    inr (existT Any.t (subevent _ sGet, λ st,
      default (Ret tt) (
        do '(mp, mr) <- Any.split st;
        Some (trigger (sPut (Any.pair (state_encode (<[k := Some v]> (state_decode mp))) mr)))
      ))).

  Definition mget_kv (k : key) : itreeV lmodE Any.t :=
    inr (existT Any.t (subevent _ sGet, λ st,
      default (Ret tt↑) (
        do '(mp, _) <- Any.split st;
        Some (Ret (default tt↑ (mjoin (state_decode mp !! k))))
      ))).

  (* mid to tgt code *)
  Definition handle_pgE : pgE ~> itreeV lmodE :=
    λ _ e,
      match e with
      | SPut k v => mput_kv k v
      | SGet k => mget_kv k
      end.

  Definition handle_Assume (P : iProp Σ) : itreeV lmodE unit :=
    get_res (λ mr,
      mr' <- trigger (Take Σ);;
      assume (✓ mr' ∧ (Own mr' ⊢ |==> P ∗ Own mr));;;
      put_res mr').

  Definition handle_AssumeRes (r : Σ) : itreeV lmodE unit :=
    get_res (λ mr,
      assume (✓ (r ⋅ mr));;;
      put_res (r ⋅ mr)).

  Definition handle_Guarantee (P : iProp Σ) : itreeV lmodE unit :=
    get_res (λ mr,
      mr' <- trigger (Choose Σ);;
      guarantee (✓ mr' ∧ (Own mr ⊢ |==> P ∗ Own mr'));;;
      put_res mr').

  Definition handle_agE : agE ~> itreeV lmodE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | AssumeRes P => handle_AssumeRes P
      | Guarantee P => handle_Guarantee P
      end.

  Definition handle_crisE : crisE ~> itreeV lmodE :=
    λ T e,
      match e with
      | inl1 ag => handle_agE _ ag
      | inr1 (inl1 c) => inr (existT T (subevent _ c, λ r, Ret r))
      | inr1 (inr1 (inl1 pg)) => handle_pgE _ pg
      | inr1 (inr1 (inr1 c)) => inr (existT T (subevent _ c, λ r, Ret r))
      end.

  Definition trans : itree crisE ~> itree lmodE :=
    interpV handle_crisE.

  Definition trans_fnsem (f : Any.t → itree crisE Any.t) : Any.t → itree lmodE Any.t :=
    λ x, trans _ (f x).
End MID. End ModTr.
Arguments ModTr.trans {Σ} [T].

Module Red. Section RED.
  Import ModTr.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans (s >>= k) = st <- trans s;; trans (k st).
  Proof using. rewrite /trans interpV_bind //. Qed.

  Lemma tau (R : Type) (t : itree _ R) :
    trans (tau;; t) = tau;; (trans t).
  Proof using. rewrite /trans interpV_tau //. Qed.

  Lemma ret (R : Type) (t : R) :
    trans (Ret t) = Ret t.
  Proof using. rewrite /trans interpV_ret //. Qed.

  Lemma call (R : Type) (c : callE R) :
    trans (trigger c) = trigger c.
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma spawn fn arg :
    trans (trigger (Spawn fn arg)) = trigger (Spawn fn arg).
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma yield tid :
    trans (trigger (Yield tid)) = trigger (Yield tid).
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma pg (R : Type) (i : pgE R) :
    trans (trigger i) = itreeV_itree (handle_pgE _ i).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma core (R : Type) (i : coreE R) :
    trans (trigger i) = trigger i.
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma triggerUB (R : Type) :
    trans (triggerUB) = triggerUB (A:=R).
  Proof using.
    rewrite /trans /triggerUB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma triggerNB (R : Type) :
    trans (triggerNB) = triggerNB (A:=R).
  Proof using.
    rewrite /trans /triggerNB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
    trans (@unwrapU crisE _ _ i) = unwrapU i.
  Proof using.
    rewrite /trans /unwrapU; des_ifs; s; try rewrite interpV_ret; eauto using triggerUB.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    trans (@unwrapN crisE _ _ i) = unwrapN i.
  Proof using.
    rewrite /trans /unwrapN; des_ifs; s; try rewrite interpV_ret; eauto using triggerNB.
  Qed.

  Lemma Assume P :
    trans (trigger (Assume P)) = itreeV_itree (handle_Assume P).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma AssumeRes r :
    trans (trigger (AssumeRes r)) = itreeV_itree (handle_AssumeRes r).
  Proof using. rewrite /trans interpV_trigger //. Qed.
  
  Lemma Guarantee P :
    trans (trigger (Guarantee P)) = itreeV_itree (handle_Guarantee P).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma ext (R : Type) (itr0 itr1 : itree _ R) (EQ : itr0 = itr1) :
    trans itr0 = trans itr1.
  Proof using. subst; et. Qed.

  (* TODO : Same lemmas for other interps ( not defined yet. ) *)
  Global Instance rdb : red_database (mk_box (@ModTr.trans)) :=
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
End RED. End Red.

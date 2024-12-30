Require Import Common.

Require Import Skeleton Mod.

Set Implicit Arguments.

Section MID.

  Context {Σ : GRA}.
  Notation iProp := (iProp Σ).

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
  Proof.
    unfold alist_encode, alist_decode.
    rewrite Any.pair_split; rewrite Any.upcast_downcast; eauto.
    induction st; s; eauto.
    destruct a.
    s; rewrite !Any.pair_split; rewrite Any.upcast_downcast; eauto.
    rewrite IHst. eauto.
  Qed.

  Definition mput_res `{stateE -< E} `{coreE -< E} (mr : Σ) : itree E unit :=
    st <- trigger sGet;; '(mp, _) :_ <- (Any.split st)?;;
    trigger (sPut (Any.pair mp mr↑)).

  Definition mget_res `{stateE -< E} `{coreE -< E} : itree E Σ :=
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

  Definition handle_Assume (P : iProp) : itree modE unit :=
    r <- trigger (Take Σ);;
    mr <- mget_res;;
    assume (✓ (r ⋅ mr));;;
    assume (Own r ⊢ P);;;
    mput_res (r ⋅ mr).

  Definition handle_Guarantee (P : iProp) : itree modE unit :=
    mr <- mget_res;;
    mr' <- trigger (Choose Σ);;
    guarantee (Own mr ==∗ P ∗ Own mr');;;
    mput_res mr'.

  Definition handle_agE : agE ~> itree modE :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | Guarantee P => handle_Guarantee P
      end.

  Definition interp_hp : itree hmodE ~> itree modE.
  Proof.
    intros T; eapply interp; intros Te e.
    destruct e as [|[|[|[|]]]].
    { apply (handle_agE a). }
    { exact (trigger (inl1 s)). }
    { exact (trigger (inr1 (inl1 c))). }
    { exact (handle_pgE p). }
    { exact (trigger (inr1 (inr1 (inr1 c)))). }
  Defined.

  Definition interp_hp_fun (f : Any.t -> itree hmodE Any.t) : Any.t -> itree modE Any.t :=
    λ x, interp_hp (f x).

End MID.

Section RED.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.
  Notation iProp := (iProp Σ).

  Lemma interp_hp_bind (R S : Type) (s : itree hmodE R) (k : R -> itree hmodE S) :
    interp_hp (s >>= k) = st <- interp_hp s;; interp_hp (k st).
  Proof. rewrite /interp_hp interp_bind //. Qed.

  (* Lemma interp_hp_body_bind R (s : itree hmodE R) (k : R -> itree hmodE Any.t) fmr :
    interp_hp_body (s >>= k) fmr = '(fr,r) <- interp_hp s fmr;; interp_hp_body (Σ:=Σ) (k r) fr.
  Proof. unfold interp_hp_body. rewrite interp_hp_bind. grind. destruct x. eauto. Qed. *)

  Lemma interp_hp_tau (R : Type) (t : itree _ R) :
    interp_hp (tau;; t) = tau;; (interp_hp t).
  Proof. rewrite /interp_hp interp_tau //. Qed.

  Lemma interp_hp_ret (R : Type) (t : R) :
    interp_hp (Ret t) = Ret t.
  Proof. rewrite /interp_hp interp_ret //. Qed.

  Lemma interp_hp_call (R : Type) (c : callE R) :
    interp_hp (trigger c) = r <- trigger c;; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_spawn fn arg :
    interp_hp (trigger (Spawn fn arg)) = r <- trigger (Spawn fn arg);; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_yield tid :
    interp_hp (trigger (Yield tid)) = r <- trigger (Yield tid);; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_tid :
    interp_hp (trigger Tid) = r <- trigger Tid;; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_pg (R : Type) (i : pgE R) :
    interp_hp (trigger i) = r <- handle_pgE i;; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_core (R : Type) (i : coreE R) :
    interp_hp (trigger i) = r <- trigger i;; tau;; Ret r.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_triggerUB (R : Type) :
    interp_hp (triggerUB) = triggerUB (A:=R).
  Proof.
    rewrite /interp_hp /triggerUB interp_bind interp_trigger; grind.
  Qed.

  Lemma interp_hp_triggerNB (R : Type) :
    interp_hp (triggerNB) = triggerNB (A:=R).
  Proof.
    rewrite /interp_hp /triggerNB interp_bind interp_trigger; grind.
  Qed.

  Lemma interp_hp_unwrapU (R : Type) (i : option R) :
    interp_hp (@unwrapU hmodE _ _ i) = r <- (unwrapU i);; Ret r.
  Proof.
    rewrite /interp_hp /unwrapU; des_ifs; grind; eauto using interp_hp_triggerUB.
  Qed.

  Lemma interp_hp_unwrapN (R : Type) (i : option R) :
    interp_hp (@unwrapN hmodE _ _ i) = r <- (unwrapN i);; Ret r.
  Proof.
    rewrite /interp_hp /unwrapN; des_ifs; grind; eauto using interp_hp_triggerNB.
  Qed.

  Lemma interp_hp_Assume P :
    interp_hp (trigger (Assume P)) = x <- handle_Assume P;; tau;; Ret x.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_Guarantee P :
    interp_hp (trigger (Guarantee P)) = x <- handle_Guarantee P;; tau;; Ret x.
  Proof. rewrite /interp_hp interp_trigger //. Qed.

  Lemma interp_hp_ext R (itr0 itr1 : itree _ R) (EQ : itr0 = itr1) :
    interp_hp itr0 = interp_hp itr1.
  Proof. subst; et. Qed.

  (* TODO : Same lemmas for other interps ( not defined yet. ) *)

  Global Program Instance interp_hp_rdb : red_database (mk_box (@interp_hp)) :=
    mk_rdb
      0
      (mk_box interp_hp_bind)
      (mk_box interp_hp_tau)
      (mk_box interp_hp_ret)
      (mk_box interp_hp_call)
      (* (mk_box interp_hp_spawn) *)
      (mk_box interp_hp_yield)
      (* (mk_box interp_hp_tid) *)
      (mk_box interp_hp_core)
      (mk_box interp_hp_pg)
      (mk_box interp_hp_triggerUB)
      (mk_box interp_hp_triggerNB)
      (mk_box interp_hp_unwrapU)
      (mk_box interp_hp_unwrapN)
      (mk_box interp_hp_Assume)
      (mk_box interp_hp_Guarantee)
      (mk_box interp_hp_ext).

End RED.


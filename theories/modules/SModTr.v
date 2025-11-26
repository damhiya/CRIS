Require Import Mod FSpec Sp.
Require Import Common ConcRA.

Definition mask {Σ : GRA} : Type := ∀ X, crisE X → bool.

Definition mask_handle `{Σ : GRA, E -< crisE} (msk : mask) {T} (e : E T) : itreeV crisE T :=
  if msk T (subevent _ e)
  then inr (existT T (subevent _ e, λ x, Ret x))
  else inr (existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).

Definition mask_trigger `{Σ : GRA, E -< crisE} (msk : mask) {X} (e : E X) : itree crisE X :=
  itreeV_itree (mask_handle msk e).

Lemma mask_trigger_gen `{Σ : GRA, E -< crisE} (msk : mask) {X} (e : E X) :
  mask_trigger msk e = if msk X (subevent _ e) then trigger e else triggerUB.
Proof. rewrite /mask_trigger /mask_handle; des_if; rewrite ?bind_ret_r /triggerUB //=; grind. Qed.

(* function semantics *)
Definition fnsem `{Σ : GRA} : Type :=
  mask *          (* event masks *)
  option fspec *  (* function spec *)
  fbody.          (* function body *)

Module SModTr. Section HOARE.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Implicit Types (fn : string) (varg arg : Any.t) (fspo sspo : option fspec).
  Implicit Types (msk : mask).
  Implicit Types (N : namespace) (stid ntid : nat) (sp : sp_type).

  (* Wraps a function call into a Hoare triple *)
  Definition HoareCall msk fspo fn varg N stid : itree crisE Any.t :=
    match fspo with
    | Some fsp =>
        x <- mask_trigger msk (Choose (meta fsp));;

        (* precondition and argument passing *)
        arg <- mask_trigger msk (Choose Any.t);;
        mask_trigger msk (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        mask_trigger msk (Guarantee ((precond fsp) (N, stid) x varg arg));;;

        (* call *)
        ret <- mask_trigger msk (Call fn arg);;

        (* postcondition argument receiving *)
        vret <- mask_trigger msk (Take Any.t);;
        mask_trigger msk (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        mask_trigger msk (Assume ((postcond fsp) (N, stid) x vret ret));;;
        Ret vret
    | None =>
        mask_trigger msk (Call fn varg)
    end.

  (* Wraps a function into a Hoare triple *)
  Definition HoareFun
      msk fspo (body : namespace → nat → Any.t → itree crisE Any.t) : Any.t → itree crisE Any.t :=
    match fspo with
    | Some fsp => λ arg,
        '(N, stid) : _ <- mask_trigger msk (Take (namespace * nat));;

        (* precondition *)
        x <- mask_trigger msk (Take (meta fsp));;
        varg <- mask_trigger msk (Take Any.t);;
        mask_trigger msk (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        mask_trigger msk (Assume (precond fsp (N, stid) x varg arg));;;

        vret <- body N stid varg;;

        (* postcondition *)
        ret <- mask_trigger msk (Choose Any.t);;
        mask_trigger msk (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        mask_trigger msk (Guarantee (postcond fsp (N, stid) x vret ret));;;

        Ret ret
    | None => λ arg, tau;; body nroot 0 arg
    end.

  (* Definition NativeSpawn fn arg : itree crisE nat :=
    trigger (Spawn fn arg). *)

  (* Wraps a spawn into a Hoare triple *)
  Definition HoareSpawn msk fspo sspo fn varg N : itree crisE nat :=
    match fspo, sspo with
    | Some fsp, Some _ =>
        x <- mask_trigger msk (Choose (meta fsp));;
        arg <- mask_trigger msk (Choose Any.t);;
        tid <- mask_trigger msk (Spawn fn arg);;
        mask_trigger msk (Assume (YIELD tid));;;
        mask_trigger msk (Guarantee (precond fsp (N, tid) x varg arg));;;
        Ret tid
    | None, Some _ =>
        tid <- mask_trigger msk (Spawn fn varg);;
        mask_trigger msk (Assume (YIELD tid));;;
        Ret tid
    | _, None =>
        mask_trigger msk (Spawn fn varg)
    end.

  (* Definition NativeYield (tid : nat) : itree crisE unit :=
    trigger (Yield tid). *)

  (* Wraps a yield into a Hoare triple *)
  Definition HoareYield msk sspo N stid ntid : itree crisE unit :=
    match sspo with
    | Some _ =>
      mask_trigger msk (Guarantee (TID stid ∗ YIELD ntid ∗ winv (↑N, ↑N)));;;
      mask_trigger msk (Yield ntid);;;
      mask_trigger msk (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)))
    | None =>
      mask_trigger msk (Yield ntid)
    end.

  (* Definition NativeGetTid : itree crisE nat :=
    trigger GetTid. *)

  Definition HoareGetTid msk sspo stid : itree crisE nat :=
    match sspo with
    | Some _ =>
      mask_trigger msk (Guarantee (TID(stid)));;;
      tid <- mask_trigger msk GetTid;;
      mask_trigger msk (Assume (⌜tid = stid⌝ ∗ TID(stid)));;;
      Ret tid
    | None =>
      mask_trigger msk GetTid
    end.

  (* Definition handle (img : bool) (sp : sp_type) : crisE ~> itreeV crisE.
  Proof.
    intros T e. destruct e.
    { exact (inr (existT _ (subevent _ a, λ v, Ret v))). }
    destruct s.
    { destruct c.
      - (* Call *)
        exact (inl (HoareCall fn args (sp fn))).
      - (* Spawn *)
        exact (inl (HoareSpawn fn args (sp fn))).
      - (* Yield *)
        exact (inl (HoareYield img tid)).
      - (* GetTid *)
        exact (inl (HoareGetTid img)).
    }
    destruct s.
    { exact (inr (existT _ (subevent _ p, λ v, Ret v))). }
    { exact (inr (existT _ (subevent _ c, λ v, Ret v))). }
  Defined. *)
  Definition handle sp msk N stid : crisE ~> itreeV crisE.
  Proof.
    intros T e.
    destruct e as [e|e].
    { (* agE *)
      exact (mask_handle msk e).
    }
    destruct e as [[fn args|fn args|tid|]|e].
    { (* Call *)
      exact (inl (HoareCall msk (sp (speckey_fn fn)) fn args N stid)).
    }
    { (* Spawn *)
      exact (inl (HoareSpawn msk (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N)).
    }
    { (* Yield *)
      exact (inl (HoareYield msk (sp (speckey_concE)) N stid tid)).
    }
    { (* GetTid *)
      exact (inl (HoareGetTid msk (sp (speckey_concE)) stid)).
    }
    (* pgE +' coreE *)
    destruct e as [e|e]; exact (mask_handle msk e).
  Defined.

  (* Definition trans img sp {R} (it : itree crisE R) : itree crisE R :=
    interpV (handle img sp) it. *)
  Definition trans sp msk N stid {R} (itr : itree crisE R) : itree crisE R :=
    interpV (handle sp msk N stid) itr.
  (* Definition trans_body : (bool * sp_type * option fspec) → fbody → fbody :=
    λ '(img, sp, fsp) bd, HoareFun fsp (trans img sp ∘ bd). *)

  (* Definition trans_ktree sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), trans_body (is_some sb.2.1, if sb.1.1.1 then sp else sp_none, fsp) bd) sb. *)
  Definition trans_fnsem (sp : sp_type) (sem : fnsem) : fbody :=
    let '(msk, fspo, fbd) := sem in
    HoareFun msk fspo (λ N stid, trans sp msk N stid ∘ fbd).
End HOARE. End SModTr.

Global Arguments SModTr.trans_fnsem: simpl never.

Notation "↧ it" := (SModTr.trans _ _ _ _ _ _ it) (at level 59, only printing).

Module SRed. Section RED.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Import SModTr.

  (* reduction lemmas for vis form - used for reduction tactics *)
  Lemma bind sp msk N stid (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans sp msk N stid (s >>= k) =
    st <- trans sp msk N stid s;; trans sp msk N stid (k st).
  Proof using. rewrite /SModTr.trans interpV_bind //. Qed.

  Lemma tau sp msk N stid (U : Type) (t : itree crisE U) :
    trans sp msk N stid (tau;; t) = tau;; (trans sp msk N stid t).
  Proof using. rewrite /SModTr.trans interpV_tau //. Qed.

  Lemma ret sp msk N stid (U : Type) (t : U) :
    trans sp msk N stid (Ret t) = Ret t.
  Proof using. rewrite /SModTr.trans interpV_ret //. Qed.

  Lemma vis_agE sp msk N stid {X R} (e : agE X) (ktr : X → itree crisE R) :
    trans sp msk N stid (vis e ktr) =
    if msk X (subevent _ e)
    then vis e (λ x, trans sp msk N stid (ktr x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /mask_handle /=.
    rewrite resum_to_subevent subevent_subevent; des_if; ss; f_equal; extensionality x; grind.
  Qed.

  Lemma vis_pgE sp msk N stid {X R} (e : pgE X) (ktr : X → itree crisE R) :
    trans sp msk N stid (vis e ktr) =
    if msk X (subevent _ e)
    then vis e (λ x, trans sp msk N stid (ktr x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /mask_handle /=.
    rewrite !resum_to_subevent !subevent_subevent; des_if; ss; f_equal; extensionality x; grind.
  Qed.

  Lemma vis_coreE sp msk N stid {X R} (e : coreE X) (ktr : X → itree crisE R) :
    trans sp msk N stid (vis e ktr) =
    if msk X (subevent _ e)
    then vis e (λ x, trans sp msk N stid (ktr x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /mask_handle /=.
    rewrite !resum_to_subevent !subevent_subevent; des_if; ss; f_equal; extensionality x; grind.
  Qed.

  Lemma vis_call sp msk N stid {R} fn args (ktr : Any.t → itree crisE R) :
    trans sp msk N stid (vis (Call fn args) ktr) =
    tau;; r <- HoareCall msk (sp (speckey_fn fn)) fn args N stid;;
    trans sp msk N stid (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_spawn sp msk N stid {R} fn args (ktr : nat → itree crisE R) :
    trans sp msk N stid (vis (Spawn fn args) ktr) =
    tau;; r <- HoareSpawn msk (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N;;
    trans sp msk N stid (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_yield sp msk N stid {R} tid (ktr : () → itree crisE R) :
    trans sp msk N stid (vis (Yield tid) ktr) =
    tau;; x <- HoareYield msk (sp (speckey_concE)) N stid tid;; trans sp msk N stid (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_gettid sp msk N stid {R} (ktr : nat → itree crisE R) :
    trans sp msk N stid (vis GetTid ktr) =
    tau;; x <- HoareGetTid msk (sp (speckey_concE)) stid;; trans sp msk N stid (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma assumeK sp msk N stid {R} P (itr : itree crisE R) :
    trans sp msk N stid (assumeK P itr) =
    if msk _ (subevent _ (Take P))
    then assumeK P (trans sp msk N stid itr)
    else triggerUB.
  Proof using.
    apply observe_eta; ss.
    rewrite resum_to_subevent /mask_handle subevent_subevent.
    des_if; ss; f_equal; extensionality x; grind.
  Qed.

  Lemma guaranteeK sp msk N stid {R} P (itr : itree crisE R) :
    trans sp msk N stid (guaranteeK P itr) =
    if msk _ (subevent _ (Choose P))
    then guaranteeK P (trans sp msk N stid itr)
    else triggerUB.
  Proof using.
    apply observe_eta; ss.
    rewrite resum_to_subevent /mask_handle subevent_subevent.
    des_if; ss; f_equal; extensionality x; grind.
  Qed.

  Lemma unwrapUK sp msk N stid {X R} x (ktr : X → itree crisE R) :
    trans sp msk N stid (unwrapUK x ktr) =
    unwrapUK x (λ x, trans sp msk N stid (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss.
    rewrite /mask_handle resum_to_subevent subevent_subevent.
    des_if; ss; f_equal; grind; extensionality x; ss.
  Qed.

  Lemma unwrapNK sp msk N stid {X R} (x : option X) (ktr : X → itree crisE R) :
    trans sp msk N stid (unwrapNK x ktr) =
    if (msk _ (subevent _ (Choose False)))
    then unwrapNK x (λ x, trans sp msk N stid (ktr x))
    else Events.unwrapUK x (λ x, trans sp msk N stid (ktr x)).
  Proof using.
    destruct x; [des_ifs|]; ss.
    apply observe_eta; ss.
    rewrite /mask_handle resum_to_subevent subevent_subevent; des_if; ss.
    { f_equal; extensionalities x; ss. }
    { f_equal; extensionalities x; ss. }
  Qed.

  (* reduction lemmas for trigger form *)
  Lemma yield sp msk N stid tid :
    trans sp msk N stid (trigger (Yield tid)) =
    tau;; HoareYield msk (sp (speckey_concE)) N stid tid.
  Proof using. rewrite vis_yield; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma spawn sp msk N stid fn args :
    trans sp msk N stid (trigger (Spawn fn args)) =
    tau;; HoareSpawn msk (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N.
  Proof using. rewrite vis_spawn; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma gettid sp msk N stid :
    trans sp msk N stid (trigger GetTid) = tau;; HoareGetTid msk (sp (speckey_concE)) stid.
  Proof using. rewrite vis_gettid; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma call sp msk N stid fn args :
    trans sp msk N stid (trigger (Call fn args)) =
    tau;; HoareCall msk (sp (speckey_fn fn)) fn args N stid.
  Proof using. rewrite vis_call; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma pg sp msk N stid (R : Type) (e : pgE R) :
    trans sp msk N stid (trigger e) = mask_trigger msk e.
  Proof using.
    rewrite vis_pgE mask_trigger_gen; des_if; rewrite vis_trigger; grind.
    erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma core sp msk N stid (R : Type) (e : coreE R) : 
    trans sp msk N stid (trigger e) = mask_trigger msk e.
  Proof using.
    rewrite vis_coreE mask_trigger_gen; des_if; rewrite vis_trigger; grind.
    erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma ag sp msk N stid (R : Type) (e : agE R) : 
    trans sp msk N stid (trigger e) = mask_trigger msk e.
  Proof using.
    rewrite vis_agE mask_trigger_gen; des_if; rewrite vis_trigger; grind.
    erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  (* Lemma unwrapU (R : Type) (i : option R) :
    SModTr.trans img sp (@unwrapU crisE _ _ i) = unwrapU i.
  Proof using.
    unfold unwrapU. des_ifs; grind.
    - rewrite ret. eauto.
    - rewrite /triggerUB bind core. f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    SModTr.trans img sp (@unwrapN crisE _ _ i) = unwrapN i.
  Proof using.
    unfold unwrapN. des_ifs; grind.
    - rewrite ret. eauto.
    - unfold triggerNB. rewrite bind vis_core.
      eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. ss.
  Qed.

  Lemma asm P : SModTr.trans img sp (assume P) = assume P.
  Proof using. unfold assume. rewrite bind core. grind. rewrite ret. refl. Qed.

  Lemma guar P : SModTr.trans img sp (guarantee P) = guarantee P.
  Proof using. unfold guarantee. rewrite bind core. grind. rewrite ret. refl. Qed. *)

  (* Lemma ru {X} (pre post : X → _) :
    SModTr.trans img sp (RealUpdate pre post) = RealUpdate pre post.
  Proof.
    rewrite /RealUpdate; unseal CRIS_FancyReal.
    repeat (rewrite bind core; f_equal; extensionalities).
    repeat (rewrite bind ag; f_equal; extensionalities).
    repeat (rewrite ag; f_equal; extensionalities).
  Qed.

  Lemma ruK {X R} (pre post : X → _) (k : _ → itree _ R) :
    SModTr.trans img sp (RealUpdateK pre post k) =
    RealUpdateK pre post (λ x, SModTr.trans img sp (k x)).
  Proof using. rewrite /RealUpdateK bind ru //. Qed. *)

  (* Lemma fbody_trivial arg : SModTr.trans img sp (fbody_trivial arg) = fbody_trivial arg.
  Proof. rewrite /fbody_trivial /= core //. Qed. *)
End RED. End SRed.

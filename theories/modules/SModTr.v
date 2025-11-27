Require Import Common ConcRA.
Require Import Mod FSpec Sp.

(* Definition mask {Σ : GRA} : Type := ∀ X, crisE X → bool.

Definition mask_handle `{Σ : GRA, E -< crisE} (msk : mask) {T} (e : E T) : itreeV crisE T :=
  if msk T (subevent _ e)
  then inr (existT T (subevent _ e, λ x, Ret x))
  else inr (existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).

Definition mask_trigger `{Σ : GRA, E -< crisE} (msk : mask) {X} (e : E X) : itree crisE X :=
  itreeV_itree (mask_handle msk e).

Lemma mask_trigger_gen `{Σ : GRA, E -< crisE} (msk : mask) {X} (e : E X) :
  mask_trigger msk e = if msk X (subevent _ e) then trigger e else triggerUB.
Proof. rewrite /mask_trigger /mask_handle; des_if; rewrite ?bind_ret_r /triggerUB //=; grind. Qed. *)

(* function semantics *)
(* Definition fnsem `{Σ : GRA} : Type :=
  mask *        
  option fspec *
  fbody.         *)

Module SModTr. Section HOARE.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Implicit Types (fn : string) (varg arg : Any.t) (fspo sspo : option fspec).
  (* Implicit Types (msk : mask). *)
  Implicit Types (N : namespace) (stid ntid : nat) (sp : sp_type).

  (* Wraps a function call into a Hoare triple *)
  Definition HoareCall fspo fn varg N stid : itree crisE Any.t :=
    match fspo with
    | Some fsp =>
        x <- trigger (Choose (meta fsp));;

        (* precondition and argument passing *)
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        trigger (Guarantee ((precond fsp) (N, stid) x varg arg));;;

        (* call *)
        ret <- trigger (Call fn arg);;

        (* postcondition and argument receiving *)
        vret <- trigger (Take Any.t);;
        trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        trigger (Assume ((postcond fsp) (N, stid) x vret ret));;;
        Ret vret
    | None =>
        trigger (Call fn varg)
    end.

  (* Wraps a function into a Hoare triple *)
  Definition HoareFun
      fspo (body : namespace → nat → Any.t → itree crisE Any.t) : Any.t → itree crisE Any.t :=
    match fspo with
    | Some fsp => λ arg,
        '(N, stid) : _ <- trigger (Take (namespace * nat));;

        (* precondition *)
        x <- trigger (Take (meta fsp));;
        varg <- trigger (Take Any.t);;
        trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        trigger (Assume (precond fsp (N, stid) x varg arg));;;

        vret <- body N stid varg;;

        (* postcondition *)
        ret <- trigger (Choose Any.t);;
        trigger (Guarantee (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)));;;
        trigger (Guarantee (postcond fsp (N, stid) x vret ret));;;

        Ret ret
    | None => λ arg, tau;; body nroot 0 arg
    end.

  (* Definition NativeSpawn fn arg : itree crisE nat :=
    trigger (Spawn fn arg). *)

  (* Wraps a spawn into a Hoare triple *)
  Definition HoareSpawn fspo sspo fn varg N : itree crisE nat :=
    match fspo, sspo with
    | Some fsp, Some _ =>
        x <- trigger (Choose (meta fsp));;
        arg <- trigger (Choose Any.t);;
        tid <- trigger (Spawn fn arg);;
        trigger (Assume (YIELD tid));;;
        trigger (Guarantee (precond fsp (N, tid) x varg arg));;;
        Ret tid
    | None, Some _ =>
        tid <- trigger (Spawn fn varg);;
        trigger (Assume (YIELD tid));;;
        Ret tid
    | _, None =>
        trigger (Spawn fn varg)
    end.

  (* Definition NativeYield (tid : nat) : itree crisE unit :=
    trigger (Yield tid). *)

  (* Wraps a yield into a Hoare triple *)
  Definition HoareYield sspo N stid ntid : itree crisE unit :=
    match sspo with
    | Some _ =>
      trigger (Guarantee (TID stid ∗ YIELD ntid ∗ winv (↑N, ↑N)));;;
      trigger (Yield ntid);;;
      trigger (Assume (TID stid ∗ YIELD stid ∗ winv (↑N, ↑N)))
    | None =>
      trigger (Yield ntid)
    end.

  (* Definition NativeGetTid : itree crisE nat :=
    trigger GetTid. *)

  Definition HoareGetTid sspo stid : itree crisE nat :=
    match sspo with
    | Some _ =>
      trigger (Guarantee (TID(stid)));;;
      tid <- trigger GetTid;;
      trigger (Assume (⌜tid = stid⌝ ∗ TID(stid)));;;
      Ret tid
    | None =>
      trigger GetTid
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
  Definition handle sp N stid : crisE ~> itreeV crisE.
  Proof.
    intros T e.
    destruct e as [e|e].
    { (* agE *)
      exact (inr (existT _ (subevent _ e, λ v, Ret v))).
    }
    destruct e as [[fn args|fn args|tid|]|e].
    { (* Call *)
      exact (inl (HoareCall (sp (speckey_fn fn)) fn args N stid)).
    }
    { (* Spawn *)
      exact (inl (HoareSpawn (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N)).
    }
    { (* Yield *)
      exact (inl (HoareYield (sp (speckey_concE)) N stid tid)).
    }
    { (* GetTid *)
      exact (inl (HoareGetTid (sp (speckey_concE)) stid)).
    }
    (* pgE +' coreE *)
    destruct e as [e|e]; exact (inr (existT _ (subevent _ e, λ v, Ret v))).
  Defined.

  (* Definition trans img sp {R} (it : itree crisE R) : itree crisE R :=
    interpV (handle img sp) it. *)
  Definition trans sp N stid {R} (itr : itree crisE R) : itree crisE R :=
    interpV (handle sp N stid) itr.
  (* Definition trans_body : (bool * sp_type * option fspec) → fbody → fbody :=
    λ '(img, sp, fsp) bd, HoareFun fsp (trans img sp ∘ bd). *)

  (* Definition trans_ktree sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), trans_body (is_some sb.2.1, if sb.1.1.1 then sp else sp_none, fsp) bd) sb. *)
  Definition trans_fnsem (sp : sp_type) (sem : option fspec * fbody) : fbody :=
    let '(fspo, fbd) := sem in
    HoareFun fspo (λ N stid, trans sp N stid ∘ fbd).
End HOARE. End SModTr.

Global Arguments SModTr.trans_fnsem: simpl never.

Notation "↧ it" := (SModTr.trans _ _ _ it) (at level 59, only printing).

Module SRed. Section RED.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Import SModTr.

  (* reduction lemmas for vis form - used for reduction tactics *)
  Lemma bind sp N stid (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans sp N stid (s >>= k) =
    st <- trans sp N stid s;; trans sp N stid (k st).
  Proof using. rewrite /SModTr.trans interpV_bind //. Qed.

  Lemma tau sp N stid (U : Type) (t : itree crisE U) :
    trans sp N stid (tau;; t) = tau;; (trans sp N stid t).
  Proof using. rewrite /SModTr.trans interpV_tau //. Qed.

  Lemma ret sp N stid (U : Type) (t : U) :
    trans sp N stid (Ret t) = Ret t.
  Proof using. rewrite /SModTr.trans interpV_ret //. Qed.

  Lemma vis_agE sp N stid {X R} (e : agE X) (ktr : X → itree crisE R) :
    trans sp N stid (vis e ktr) =
    vis e (λ x, trans sp N stid (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_pgE sp  N stid {X R} (e : pgE X) (ktr : X → itree crisE R) :
    trans sp  N stid (vis e ktr) =
    vis e (λ x, trans sp N stid (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_coreE sp  N stid {X R} (e : coreE X) (ktr : X → itree crisE R) :
    trans sp  N stid (vis e ktr) =
    vis e (λ x, trans sp N stid (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_call sp N stid {R} fn args (ktr : Any.t → itree crisE R) :
    trans sp N stid (vis (Call fn args) ktr) =
    tau;; r <- HoareCall (sp (speckey_fn fn)) fn args N stid;;
    trans sp N stid (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_spawn sp N stid {R} fn args (ktr : nat → itree crisE R) :
    trans sp N stid (vis (Spawn fn args) ktr) =
    tau;; r <- HoareSpawn (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N;;
    trans sp N stid (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_yield sp N stid {R} tid (ktr : () → itree crisE R) :
    trans sp N stid (vis (Yield tid) ktr) =
    tau;; x <- HoareYield (sp (speckey_concE)) N stid tid;; trans sp N stid (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_gettid sp N stid {R} (ktr : nat → itree crisE R) :
    trans sp N stid (vis GetTid ktr) =
    tau;; x <- HoareGetTid (sp (speckey_concE)) stid;; trans sp N stid (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma assumeK sp N stid {R} P (itr : itree crisE R) :
    trans sp N stid (assumeK P itr) = assumeK P (trans sp N stid itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma guaranteeK sp N stid {R} P (itr : itree crisE R) :
    trans sp N stid (guaranteeK P itr) = guaranteeK P (trans sp N stid itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma unwrapUK sp N stid {X R} x (ktr : X → itree crisE R) :
    trans sp N stid (unwrapUK x ktr) = unwrapUK x (λ x, trans sp N stid (ktr x)).
  Proof using. destruct x; ss. eapply observe_eta; ss. f_equal; grind; extensionality x; ss. Qed.

  Lemma unwrapNK sp N stid {X R} (x : option X) (ktr : X → itree crisE R) :
    trans sp N stid (unwrapNK x ktr) = unwrapNK x (λ x, trans sp N stid (ktr x)).
  Proof using.
    destruct x; [des_ifs|]; ss.
    apply observe_eta; ss; f_equal; extensionality x; ss.
  Qed.

  (* reduction lemmas for trigger form *)
  Lemma yield sp N stid tid :
    trans sp N stid (trigger (Yield tid)) =
    tau;; HoareYield (sp (speckey_concE)) N stid tid.
  Proof using. rewrite vis_yield; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma spawn sp N stid fn args :
    trans sp N stid (trigger (Spawn fn args)) =
    tau;; HoareSpawn (sp (speckey_fn fn)) (sp (speckey_concE)) fn args N.
  Proof using. rewrite vis_spawn; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma gettid sp N stid :
    trans sp N stid (trigger GetTid) = tau;; HoareGetTid (sp (speckey_concE)) stid.
  Proof using. rewrite vis_gettid; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma call sp N stid fn args :
    trans sp N stid (trigger (Call fn args)) =
    tau;; HoareCall (sp (speckey_fn fn)) fn args N stid.
  Proof using. rewrite vis_call; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma pg sp N stid (R : Type) (e : pgE R) : trans sp N stid (trigger e) = trigger e.
  Proof using.
    rewrite vis_pgE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma core sp N stid (R : Type) (e : coreE R) :
    trans sp N stid (trigger e) = trigger e.
  Proof using.
    rewrite vis_coreE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma ag sp N stid (R : Type) (e : agE R) : trans sp N stid (trigger e) = trigger e.
  Proof using.
    rewrite vis_agE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite ret //.
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

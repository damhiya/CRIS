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
  Implicit Types (fn : string) (varg arg : Any.t) (fspo : option fspec) (imgconc: bool).
  (* Implicit Types (msk : mask). *)
  Implicit Types (sp : specmap).

  (* Wraps a function call into a Hoare triple *)
  Definition HoareCall fspo fn varg : itree crisE Any.t :=
    match fspo with
    | Some fsp =>
        x <- trigger (Choose (meta fsp));;

        (* precondition and argument passing *)
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee ((precond fsp) x varg arg));;;

        (* call *)
        ret <- trigger (Call fn arg);;

        (* postcondition and argument receiving *)
        vret <- trigger (Take Any.t);;
        trigger (Assume ((postcond fsp) x vret ret));;;
        Ret vret
    | None =>
        trigger (Call fn varg)
    end.

  (* Wraps a function into a Hoare triple *)
  Definition HoareFun
      fspo (body : Any.t → itree crisE Any.t) : Any.t → itree crisE Any.t :=
    match fspo with
    | Some fsp => λ arg,
        (* precondition *)
        x <- trigger (Take (meta fsp));;
        varg <- trigger (Take Any.t);;
        trigger (Assume (precond fsp x varg arg));;;

        vret <- body varg;;

        (* postcondition *)
        ret <- trigger (Choose Any.t);;
        trigger (Guarantee (postcond fsp x vret ret));;;

        Ret ret
    | None => λ arg, tau;; body arg
    end.

  (* Definition NativeSpawn fn arg : itree crisE nat :=
    trigger (Spawn fn arg). *)

  (* Wraps a spawn into a Hoare triple *)
  Definition HoareSpawn fspo imgconc fn varg : itree crisE nat :=
    match fspo, imgconc with
    | Some fsp, true =>
        x <- trigger (Choose (meta fsp));;
        arg <- trigger (Choose Any.t);;
        tid <- trigger (Spawn fn arg);;
        trigger (Assume (YIELD tid));;;
        trigger (Guarantee (YIELD tid -∗ TID tid -∗ winv (⊤, ⊤) -∗ precond fsp x varg arg));;;
        Ret tid
    | None, true =>
        tid <- trigger (Spawn fn varg);;
        trigger (Assume (YIELD tid));;;
        Ret tid
    | _, false =>
        trigger (Spawn fn varg)
    end.

  (* Definition NativeYield (tid : nat) : itree crisE unit :=
    trigger (Yield tid). *)

  (* Wraps a yield into a Hoare triple *)
  Definition HoareYield imgconc ntid : itree crisE unit :=
    if imgconc
    then
      stid <- trigger (Choose nat);;
      trigger (Guarantee (TID stid ∗ YIELD ntid ∗ winv (⊤, ⊤)));;;
      trigger (Yield ntid);;;
      trigger (Assume (TID stid ∗ YIELD stid ∗ winv (⊤, ⊤)))
    else
      trigger (Yield ntid).

  (* Definition NativeGetTid : itree crisE nat :=
    trigger GetTid. *)

  Definition HoareGetTid imgconc : itree crisE nat :=
    if imgconc
    then
      stid <- trigger (Choose nat);;
      trigger (Guarantee (TID stid));;;
      tid <- trigger GetTid;;
      trigger (Assume (⌜tid = stid⌝ ∗ TID stid));;;
      Ret tid
    else
      trigger GetTid.

  (* Definition handle (img : bool) (sp : specmap) : crisE ~> itreeV crisE.
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
  Definition handle sp : crisE ~> itreeV crisE.
  Proof.
    intros T e.
    destruct e as [e|e].
    { (* agE *)
      exact (inr (existT _ (subevent _ e, λ v, Ret v))).
    }
    destruct e as [[fn args|fn args|tid|]|e].
    { (* Call *)
      exact (inl (HoareCall (sp !! (speckey_fn fn)) fn args)).
    }
    { (* Spawn *)
      exact (inl (HoareSpawn (sp !! (speckey_fn fn)) (decide (speckey_concE ∈ dom sp)) fn args)).
    }
    { (* Yield *)
      exact (inl (HoareYield (decide (speckey_concE ∈ dom sp)) tid)).
    }
    { (* GetTid *)
      exact (inl (HoareGetTid (decide (speckey_concE ∈ dom sp)))).
    }
    (* pgE +' coreE *)
    destruct e as [e|e]; exact (inr (existT _ (subevent _ e, λ v, Ret v))).
  Defined.

  (* Definition trans img sp {R} (it : itree crisE R) : itree crisE R :=
    interpV (handle img sp) it. *)
  Definition trans sp {R} (itr : itree crisE R) : itree crisE R :=
    interpV (handle sp) itr.
  (* Definition trans_body : (bool * specmap * option fspec) → fbody → fbody :=
    λ '(img, sp, fsp) bd, HoareFun fsp (trans img sp ∘ bd). *)

  (* Definition trans_ktree sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), trans_body (is_some sb.2.1, if sb.1.1.1 then sp else sp_none, fsp) bd) sb. *)
  Definition trans_fnsem (sp : specmap) (sem : option fspec * fbody) : fbody :=
    let '(fspo, fbd) := sem in
    HoareFun fspo (trans sp ∘ fbd).
End HOARE. End SModTr.

Global Arguments SModTr.trans_fnsem: simpl never.

Notation "↧ it" := (SModTr.trans _ it) (at level 59, only printing).

Module SRed. Section RED.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Import SModTr.

  (* reduction lemmas for vis form - used for reduction tactics *)
  Lemma bind sp (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans sp (s >>= k) =
    st <- trans sp s;; trans sp (k st).
  Proof using. rewrite /SModTr.trans interpV_bind //. Qed.

  Lemma tau sp (U : Type) (t : itree crisE U) :
    trans sp (tau;; t) = tau;; (trans sp t).
  Proof using. rewrite /SModTr.trans interpV_tau //. Qed.

  Lemma ret sp (U : Type) (t : U) :
    trans sp (Ret t) = Ret t.
  Proof using. rewrite /SModTr.trans interpV_ret //. Qed.

  Lemma vis_agE sp {X R} (e : agE X) (ktr : X → itree crisE R) :
    trans sp (vis e ktr) =
    vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_pgE sp  {X R} (e : pgE X) (ktr : X → itree crisE R) :
    trans sp  (vis e ktr) =
    vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_coreE sp  {X R} (e : coreE X) (ktr : X → itree crisE R) :
    trans sp  (vis e ktr) =
    vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /SModTr.trans /SModTr.handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_call sp {R} fn args (ktr : Any.t → itree crisE R) :
    trans sp (vis (Call fn args) ktr) =
    tau;; r <- HoareCall (sp !! (speckey_fn fn)) fn args;;
    trans sp (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_spawn sp {R} fn args (ktr : nat → itree crisE R) :
    trans sp (vis (Spawn fn args) ktr) =
    tau;; r <- HoareSpawn (sp !! (speckey_fn fn)) (decide (speckey_concE ∈ dom sp)) fn args;;
    trans sp (ktr r).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_yield sp {R} tid (ktr : () → itree crisE R) :
    trans sp (vis (Yield tid) ktr) =
    tau;; x <- HoareYield (decide (speckey_concE ∈ dom sp)) tid;; trans sp (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_gettid sp {R} (ktr : nat → itree crisE R) :
    trans sp (vis GetTid ktr) =
    tau;; x <- HoareGetTid (decide (speckey_concE ∈ dom sp));; trans sp (ktr x).
  Proof using. rewrite /SModTr.trans /SModTr.handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma assumeK sp {R} P (itr : itree crisE R) :
    trans sp (assumeK P itr) = assumeK P (trans sp itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma guaranteeK sp {R} P (itr : itree crisE R) :
    trans sp (guaranteeK P itr) = guaranteeK P (trans sp itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma unwrapUK sp {X R} x (ktr : X → itree crisE R) :
    trans sp (unwrapUK x ktr) = unwrapUK x (λ x, trans sp (ktr x)).
  Proof using. destruct x; ss. eapply observe_eta; ss. f_equal; grind; extensionality x; ss. Qed.

  Lemma unwrapNK sp {X R} (x : option X) (ktr : X → itree crisE R) :
    trans sp (unwrapNK x ktr) = unwrapNK x (λ x, trans sp (ktr x)).
  Proof using.
    destruct x; [des_ifs|]; ss.
    apply observe_eta; ss; f_equal; extensionality x; ss.
  Qed.

  (* reduction lemmas for trigger form *)
  Lemma yield sp tid :
    trans sp (trigger (Yield tid)) =
    tau;; HoareYield (decide (speckey_concE ∈ dom sp)) tid.
  Proof using. rewrite vis_yield; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma spawn sp fn args :
    trans sp (trigger (Spawn fn args)) =
    tau;; HoareSpawn (sp !! (speckey_fn fn)) (decide (speckey_concE ∈ dom sp)) fn args.
  Proof using. rewrite vis_spawn; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma gettid sp :
    trans sp (trigger GetTid) = tau;; HoareGetTid (decide (speckey_concE ∈ dom sp)).
  Proof using. rewrite vis_gettid; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma call sp fn args :
    trans sp (trigger (Call fn args)) =
    tau;; HoareCall (sp !! (speckey_fn fn)) fn args.
  Proof using. rewrite vis_call; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma pg sp (R : Type) (e : pgE R) : trans sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_pgE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma core sp (R : Type) (e : coreE R) :
    trans sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_coreE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite ret //.
  Qed.

  Lemma ag sp (R : Type) (e : agE R) : trans sp (trigger e) = trigger e.
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

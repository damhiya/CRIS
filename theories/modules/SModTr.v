Require Import Common ConcRA.
Require Import Mod FSpec Sp.

(* function semantics - maybe move to Mod.v? *)
Definition fnsem `{Σ : GRA} : Type := emask * (option fspec_rel * fbody).

Module SModTr. Section HOARE.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Implicit Types (fn : string) (varg arg : Any.t) (fspo : option fspec_rel) (sp : specmap).

  Definition HoareFun fspo (body : fbody) : fbody :=
    match fspo with
    | Some fsp =>
      λ arg,
      PQ <- trigger (Take (FSpec fsp));;

      (*** precondition ***)
      varg <- trigger (Take Any.t);;
      trigger (Assume (PQ.(Precond) varg arg));;;

      vret <- body varg;;

      (*** postcondition ***)
      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (PQ.(Postcond) vret ret));;;

        Ret ret
    | None => λ arg, tau;; body arg
    end.

  Definition omask_check (omsk: option emask) fn args : bool :=
    match omsk with
    | None => true
    | Some msk => msk _ (subevent _ (Call fn args))
    end.
  
  Definition HoareCall fspo omsk fn varg : itree crisE Any.t :=
    match fspo with
    | Some fsp =>
      PQ <- trigger (Choose (FSpec (if omask_check omsk fn varg then fsp else fspec_trivial)));;

      (*** precondition ***)
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (PQ.(Precond) varg arg));;;

      (* call *)
      ret <- trigger (Call fn arg);;

      (*** postcondition ***)
      vret <- trigger (Take Any.t);;
      trigger (Assume (PQ.(Postcond) vret ret));;;

      Ret vret
    | None =>
        trigger (Call fn varg)
    end.

  (* Wraps a spawn into a Hoare triple *)
  Definition HoareSpawn fspo imgconc fn varg : itree crisE nat :=
    match fspo, imgconc with
    | Some fsp, true =>
        arg <- trigger (Choose Any.t);;
        tid <- trigger (Spawn fn arg);;
        trigger (Assume (YIELD tid));;;
        PQ <- trigger (Choose (FSpec fsp));;
        trigger (Guarantee (YIELD tid -∗ TID tid -∗ winv (⊤, ⊤) -∗ (Precond PQ) varg arg));;;
        Ret tid
    | None, true =>
        tid <- trigger (Spawn fn varg);;
        trigger (Assume (YIELD tid));;;
        Ret tid
    | _, false =>
        trigger (Spawn fn varg)
    end.

  (* Wraps a yield into a Hoare triple *)
  Definition HoareYield (imgconc : bool) ntid : itree crisE unit :=
    if imgconc
    then
      stid <- trigger (Choose nat);;
      trigger (Guarantee (TID stid ∗ YIELD ntid ∗ winv (⊤, ⊤)));;;
      trigger (Yield ntid);;;
      trigger (Assume (TID stid ∗ YIELD stid ∗ winv (⊤, ⊤)))
    else
      trigger (Yield ntid).

  Definition HoareGetTid (imgconc : bool) : itree crisE nat :=
    if imgconc
    then
      stid <- trigger (Choose nat);;
      trigger (Guarantee (TID stid));;;
      tid <- trigger GetTid;;
      trigger (Assume (⌜tid = stid⌝ ∗ TID stid));;;
      Ret tid
    else
      trigger GetTid.

  Definition handle sp (omsk: option emask) : crisE ~> itreeV crisE.
  Proof.
    intros T e.
    destruct e as [e|e].
    (* agE *)
    { exact (inr (existT _ (subevent _ e, λ v, Ret v))). }
    destruct e as [[fn args|fn args|tid|]|e].
    (* Call *)
    { exact (inl (HoareCall (sp.1 !! (fid fn)) omsk fn args)). }
    (* Spawn *)
    { exact (inl (HoareSpawn (sp.1 !! (fid fn)) sp.2 fn args)). }
    (* Yield *)
    { exact (inl (HoareYield sp.2 tid)). }
    (* GetTid *)
    { exact (inl (HoareGetTid sp.2)). }
    (* pgE +' coreE *)
    destruct e as [e|e]; exact (inr (existT _ (subevent _ e, λ v, Ret v))).
  Defined.

  Definition _trans sp (omsk: option emask) {R} (itr : itree crisE R) : itree crisE R :=
    interpV (handle sp omsk) itr.

  Definition trans sp {R} (itr : itree crisE R) : itree crisE R :=
    _trans sp None itr.
  
  Definition trans_fnsem (sp : specmap) (sem : option fspec_rel * fbody) : fbody :=
    let '(fspo, fbd) := sem in HoareFun fspo (trans sp ∘ fbd).

  Definition trans_cancel sp (sem : emask * (option fspec_rel * fbody)) : fbody :=
    let '(msk, (fspo, fbd)) := sem in HoareFun fspo (_trans sp (Some msk) ∘ fbd).

End HOARE. End SModTr.

Global Arguments SModTr.trans_fnsem: simpl never.

Notation "↧ it" := (SModTr.trans _ it) (at level 59, only printing).

Module SRed. Section RED.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Import SModTr.

  (* reduction lemmas for vis form - used for reduction tactics *)

  Lemma _bind sp omsk (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    _trans sp omsk (s >>= k) = st <- _trans sp omsk s;; _trans sp omsk (k st).
  Proof using. rewrite /_trans interpV_bind //. Qed.

  Lemma _tau sp omsk (U : Type) (t : itree crisE U) :
    _trans sp omsk (tau;; t) = tau;; (_trans sp omsk t).
  Proof using. rewrite /_trans interpV_tau //. Qed.

  Lemma _ret sp omsk (U : Type) (t : U) :
    _trans sp omsk (Ret t) = Ret t.
  Proof using. rewrite /_trans interpV_ret //. Qed.

  Lemma _vis_agE sp omsk {X R} (e : agE X) (ktr : X → itree crisE R) :
    _trans sp omsk (vis e ktr) = vis e (λ x, _trans sp omsk (ktr x)).
  Proof using.
    rewrite /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma _vis_pgE sp omsk  {X R} (e : pgE X) (ktr : X → itree crisE R) :
    _trans sp omsk  (vis e ktr) = vis e (λ x, _trans sp omsk (ktr x)).
  Proof using.
    rewrite /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma _vis_coreE sp omsk  {X R} (e : coreE X) (ktr : X → itree crisE R) :
    _trans sp omsk  (vis e ktr) = vis e (λ x, _trans sp omsk (ktr x)).
  Proof using.
    rewrite /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma _vis_call sp omsk {R} fn args (ktr : Any.t → itree crisE R) :
    _trans sp omsk (vis (Call fn args) ktr) =
      tau;; r <- HoareCall (sp.1 !! (fid fn)) omsk fn args;;
      _trans sp omsk (ktr r).
  Proof using. rewrite /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma _vis_spawn sp omsk {R} fn args (ktr : nat → itree crisE R) :
    _trans sp omsk (vis (Spawn fn args) ktr) =
      tau;; r <- HoareSpawn (sp.1 !! (fid fn)) sp.2 fn args;;
      _trans sp omsk (ktr r).
  Proof using. rewrite /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma _vis_yield sp omsk {R} tid (ktr : () → itree crisE R) :
    _trans sp omsk (vis (Yield tid) ktr) =
      tau;; x <- HoareYield sp.2 tid;; _trans sp omsk (ktr x).
  Proof using. rewrite /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma _vis_gettid sp omsk {R} (ktr : nat → itree crisE R) :
    _trans sp omsk (vis GetTid ktr) =
      tau;; x <- HoareGetTid sp.2;; _trans sp omsk (ktr x).
  Proof using. rewrite /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma _assumeK sp omsk {R} P (itr : itree crisE R) :
    _trans sp omsk (assumeK P itr) = assumeK P (_trans sp omsk itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma _guaranteeK sp omsk {R} P (itr : itree crisE R) :
    _trans sp omsk (guaranteeK P itr) = guaranteeK P (_trans sp omsk itr).
  Proof using. apply observe_eta; ss; f_equal; extensionality x; grind. Qed.

  Lemma _unwrapUK sp omsk {X R} x (ktr : X → itree crisE R) :
    _trans sp omsk (unwrapUK x ktr) = unwrapUK x (λ x, _trans sp omsk (ktr x)).
  Proof using. destruct x; ss. eapply observe_eta; ss. f_equal; grind; extensionality x; ss. Qed.

  Lemma _unwrapNK sp omsk {X R} (x : option X) (ktr : X → itree crisE R) :
    _trans sp omsk (unwrapNK x ktr) = unwrapNK x (λ x, _trans sp omsk (ktr x)).
  Proof using. destruct x; [des_ifs|]; ss. apply observe_eta; s; f_equal; extensionalities; ss. Qed.

  (* reduction lemmas for trigger form *)
  Lemma _yield sp omsk tid :
    _trans sp omsk (trigger (Yield tid)) = tau;; HoareYield sp.2 tid.
  Proof using. rewrite _vis_yield; grind; erewrite <- bind_ret_r; grind; rewrite _ret //. Qed.

  Lemma _spawn sp omsk fn args :
    _trans sp omsk (trigger (Spawn fn args)) =
      tau;; HoareSpawn (sp.1 !! (fid fn)) sp.2 fn args.
  Proof using. rewrite _vis_spawn; grind; erewrite <- bind_ret_r; grind; rewrite _ret //. Qed.

  Lemma _gettid sp omsk :
    _trans sp omsk (trigger GetTid) = tau;; HoareGetTid sp.2.
  Proof using. rewrite _vis_gettid; grind; erewrite <- bind_ret_r; grind; rewrite _ret //. Qed.

  Lemma _call sp omsk fn args :
    _trans sp omsk (trigger (Call fn args)) =
    tau;; HoareCall (sp.1 !! (fid fn)) omsk fn args.
  Proof using. rewrite _vis_call; grind; erewrite <- bind_ret_r; grind; rewrite _ret //. Qed.

  Lemma _pg sp omsk (R : Type) (e : pgE R) : _trans sp omsk (trigger e) = trigger e.
  Proof using.
    rewrite _vis_pgE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite _ret //.
  Qed.

  Lemma _core sp omsk (R : Type) (e : coreE R) :
    _trans sp omsk (trigger e) = trigger e.
  Proof using.
    rewrite _vis_coreE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite _ret //.
  Qed.

  Lemma _ag sp omsk (R : Type) (e : agE R) : _trans sp omsk (trigger e) = trigger e.
  Proof using.
    rewrite _vis_agE vis_trigger; grind; erewrite <- bind_ret_r; grind; rewrite _ret //.
  Qed.

  Lemma _ru sp omsk pp : _trans sp omsk (RealUpdate pp) = RealUpdate pp.
  Proof.
    rewrite /RealUpdate; unseal CRIS_FancyReal.
    repeat (rewrite _bind _core; f_equal; extensionalities).
    repeat (rewrite _bind _ag; f_equal; extensionalities).
    repeat (rewrite _ag; f_equal; extensionalities).
  Qed.

  Lemma _ruK {R} sp omsk pp (k : _ → itree _ R) :
    _trans sp omsk (RealUpdateK pp k) = RealUpdateK pp (λ x, _trans sp omsk (k x)).
  Proof using. rewrite /RealUpdateK _bind _ru //. Qed.


  

  Lemma bind sp (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans sp (s >>= k) = st <- trans sp s;; trans sp (k st).
  Proof using. rewrite /trans /_trans interpV_bind //. Qed.

  Lemma tau sp (U : Type) (t : itree crisE U) :
    trans sp (tau;; t) = tau;; (trans sp t).
  Proof using. rewrite /trans /_trans interpV_tau //. Qed.

  Lemma ret sp (U : Type) (t : U) :
    trans sp (Ret t) = Ret t.
  Proof using. rewrite /trans /_trans interpV_ret //. Qed.

  Lemma vis_agE sp {X R} (e : agE X) (ktr : X → itree crisE R) :
    trans sp (vis e ktr) = vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /trans /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_pgE sp  {X R} (e : pgE X) (ktr : X → itree crisE R) :
    trans sp  (vis e ktr) = vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /trans /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_coreE sp  {X R} (e : coreE X) (ktr : X → itree crisE R) :
    trans sp  (vis e ktr) = vis e (λ x, trans sp (ktr x)).
  Proof using.
    rewrite /trans /_trans /handle /=; apply observe_eta; rewrite /=.
    f_equal; extensionality x; grind.
  Qed.

  Lemma vis_call sp {R} fn args (ktr : Any.t → itree crisE R) :
    trans sp (vis (Call fn args) ktr) =
      tau;; r <- HoareCall (sp.1 !! (fid fn)) None fn args;;
      trans sp (ktr r).
  Proof using. rewrite /trans /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_spawn sp {R} fn args (ktr : nat → itree crisE R) :
    trans sp (vis (Spawn fn args) ktr) =
      tau;; r <- HoareSpawn (sp.1 !! (fid fn)) sp.2 fn args;;
      trans sp (ktr r).
  Proof using. rewrite /trans /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_yield sp {R} tid (ktr : () → itree crisE R) :
    trans sp (vis (Yield tid) ktr) =
      tau;; x <- HoareYield sp.2 tid;; trans sp (ktr x).
  Proof using. rewrite /trans /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

  Lemma vis_gettid sp {R} (ktr : nat → itree crisE R) :
    trans sp (vis GetTid ktr) =
      tau;; x <- HoareGetTid sp.2;; trans sp (ktr x).
  Proof using. rewrite /trans /_trans /handle /= interpV_vis. apply observe_eta; ss. Qed.

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
  Proof using. destruct x; [des_ifs|]; ss. apply observe_eta; s; f_equal; extensionalities; ss. Qed.

  (* reduction lemmas for trigger form *)
  Lemma yield sp tid :
    trans sp (trigger (Yield tid)) = tau;; HoareYield sp.2 tid.
  Proof using. rewrite vis_yield; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma spawn sp fn args :
    trans sp (trigger (Spawn fn args)) =
      tau;; HoareSpawn (sp.1 !! (fid fn)) sp.2 fn args.
  Proof using. rewrite vis_spawn; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma gettid sp :
    trans sp (trigger GetTid) = tau;; HoareGetTid sp.2.
  Proof using. rewrite vis_gettid; grind; erewrite <- bind_ret_r; grind; rewrite ret //. Qed.

  Lemma call sp fn args :
    trans sp (trigger (Call fn args)) =
    tau;; HoareCall (sp.1 !! (fid fn)) None fn args.
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

  Lemma ru sp pp : trans sp (RealUpdate pp) = RealUpdate pp.
  Proof.
    rewrite /RealUpdate; unseal CRIS_FancyReal.
    repeat (rewrite bind core; f_equal; extensionalities).
    repeat (rewrite bind ag; f_equal; extensionalities).
    repeat (rewrite ag; f_equal; extensionalities).
  Qed.

  Lemma ruK {R} sp pp (k : _ → itree _ R) :
    trans sp (RealUpdateK pp k) = RealUpdateK pp (λ x, trans sp (k x)).
  Proof using. rewrite /RealUpdateK bind ru //. Qed.
End RED. End SRed.

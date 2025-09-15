From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.
Require Import Mod FSpec Sp.
Require Import Common ConcRA.

Set Implicit Arguments.

Module SModTr. Section HOARE.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Implicit Types (fn : string) (varg arg : Any.t) (fspo : option fspec).

  (* Wraps a function call into a Hoare triple *)
  Definition HoareCall fn varg fspo : itree crisE Any.t :=
    match fspo with
    | Some (@fspec_call _ meta pre post) =>
        x <- trigger (Choose meta);;

        (* precondition *)
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee (pre x varg arg));;;

        (* call *)
        ret <- trigger (Call fn arg);;

        (* postcondition *)
        vret <- trigger (Take Any.t);;
        trigger (Assume (post x vret ret));;;

        Ret vret
    | Some _ =>
        (* Calling a spawnable function is undefined behavior *)
        triggerNB
    | None =>
        trigger (Call fn varg)
    end.

  (* Wraps a function into a Hoare triple *)
  Definition HoareFun fspo body : Any.t → itree crisE Any.t :=
    match fspo with
    | Some (@fspec_call _ meta pre post) => λ arg,
        x <- trigger (Take meta);;
        varg <- trigger (Take Any.t);;
        trigger (Assume (pre x varg arg));;; (* precondition *)

        vret <- body varg;;

        ret <- trigger (Choose Any.t);;
        trigger (Guarantee (post x vret ret));;; (* postcondition *)

        Ret ret
    | Some (@fspec_spawn _ meta pre post) => λ arg,
        tid <- trigger (Take nat);;
        trigger (Assume (TID tid ∗ YIELD tid));;; (* Concurrency precondition *)

        x <- trigger (Take meta);;
        varg <- trigger (Take Any.t);;
        trigger (Assume (pre (tid, x) varg arg));;; (* precondition *)

        vret <- body varg;;

        ret <- trigger (Choose Any.t);;
        trigger (Guarantee (post (tid, x) vret ret));;; (* postcondition *)

        trigger (Guarantee (TID tid));;; (* Concurrency postcondition *)

        Ret ret
    | None => λ arg, tau;; body arg
    end.

  Definition NativeSpawn fn arg : itree crisE nat :=
    trigger (Spawn fn arg).

  (* Wraps a spawn into a Hoare triple *)
  Definition HoareSpawn fn varg fspo : itree crisE nat :=
    match fspo with
    | Some (@fspec_call _ meta pre post) =>
        triggerNB
    | Some (@fspec_spawn _ meta pre post) =>
        x <- trigger (Choose meta);;
        arg <- trigger (Choose Any.t);;
        tid <- trigger (Spawn fn arg);;
        trigger (Assume (YIELD tid));;;
        trigger (Guarantee (pre (tid, x) varg arg));;;
        Ret tid
    | None =>
        NativeSpawn fn varg
    end.

  Definition NativeYield (tid : nat) : itree crisE unit :=
    trigger (Yield tid).

  (* Wraps a yield into a Hoare triple *)
  Definition HoareYield (img : bool) (tid : nat) : itree crisE unit :=
    if img
    then
      my_tid <- trigger (Choose nat);;
      trigger (Guarantee (TID(my_tid) ∗ YIELD(tid)));;;
      trigger (Yield tid);;;
      trigger (Assume (TID(my_tid) ∗ YIELD(my_tid)))
    else
      NativeYield tid.

  Definition NativeGetTid : itree crisE nat :=
    trigger GetTid.

  Definition HoareGetTid (img : bool) : itree crisE nat :=
    if img
    then
      my_tid <- trigger (Choose nat);;
      trigger (Guarantee (TID(my_tid)));;;
      tid <- trigger GetTid;;
      trigger (Assume (⌜tid = my_tid⌝ ∗ TID(my_tid)));;;
      Ret tid
    else
      NativeGetTid.

  Definition handle (img : bool) (sp : sp_type) : crisE ~> itreeV crisE.
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
  Defined.

  Definition trans img sp {R} (it : itree crisE R) : itree crisE R :=
    interpV (handle img sp) it.

  Definition trans_body : (bool * sp_type * option fspec) → fbody → fbody :=
    λ '(img, sp, fsp) bd, HoareFun fsp (trans (* img *) (is_some fsp) sp ∘ bd).

  Definition trans_ktree sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp, bd), trans_body (sb.1.1.1, if sb.1.1.1 then sp else sp_none, fsp) bd) sb.
End HOARE. End SModTr.

Global Arguments SModTr.trans_ktree: simpl never.

Notation "↧ it" := (SModTr.trans _ _ it) (at level 59, only printing).

Module SRed. Section RED.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Context (img : bool) (sp : sp_type).

  Lemma bind (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    SModTr.trans img sp (s >>= k) = st <- SModTr.trans img sp s;; SModTr.trans img sp (k st).
  Proof using. unfold SModTr.trans in *. rewrite interpV_bind //. Qed.

  Lemma tau (U : Type) (t : itree _ U) :
    SModTr.trans img sp (tau;; t) = tau;; (SModTr.trans img sp t).
  Proof using. unfold SModTr.trans in *. rewrite interpV_tau //. Qed.

  Lemma ret (U : Type) (t : U) :
    SModTr.trans img sp (Ret t) = Ret t.
  Proof using. unfold SModTr.trans in *. rewrite interpV_ret //. Qed.

  Lemma vis_ag {X R} (e : agE X) (ktr : X -> itree crisE R) :
    SModTr.trans img sp (vis e ktr) = vis e (λ x, SModTr.trans img sp (ktr x)).
  Proof using. eapply observe_eta; ss. f_equal. extensionality x. eapply observe_eta; ss. Qed.

  Lemma vis_yield {R} tid (ktr : () -> itree crisE R) :
    SModTr.trans img sp (vis (Yield tid) ktr) =
    tau;; x <- SModTr.HoareYield img tid;; SModTr.trans img sp (ktr x).
  Proof using. unfold SModTr.trans. rewrite interpV_vis. eapply observe_eta; ss. Qed.

  Lemma vis_spawn {R} fn args (ktr : nat -> itree crisE R) :
    SModTr.trans img sp (vis (Spawn fn args) ktr) =
    tau;; x <- SModTr.HoareSpawn fn args (sp fn);; SModTr.trans img sp (ktr x).
  Proof using. unfold SModTr.trans. rewrite interpV_vis. eapply observe_eta; ss. Qed.

  Lemma vis_gettid {R} (ktr : nat -> itree crisE R) :
    SModTr.trans img sp (vis GetTid ktr) =
    tau;; x <- SModTr.HoareGetTid img;; SModTr.trans img sp (ktr x).
  Proof using. unfold SModTr.trans. rewrite interpV_vis. eapply observe_eta; ss. Qed.

  Lemma vis_call {R} fn args (ktr : Any.t -> itree crisE R) :
    SModTr.trans img sp (vis (Call fn args) ktr) =
    tau;; x <- SModTr.HoareCall fn args (sp fn);; SModTr.trans img sp (ktr x).
  Proof using. unfold SModTr.trans. rewrite interpV_vis. eapply observe_eta; ss. Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree crisE R) :
    SModTr.trans img sp (vis e ktr) = vis e (λ x, SModTr.trans img sp (ktr x)).
  Proof using. eapply observe_eta; ss. f_equal. extensionality x. eapply observe_eta; ss. Qed.

  Lemma vis_core {X R} (e : coreE X) (ktr : X -> itree crisE R) :
    SModTr.trans img sp (vis e ktr) = vis e (λ x, SModTr.trans img sp (ktr x)).
  Proof using. eapply observe_eta; ss. f_equal. extensionality x. eapply observe_eta; ss. Qed.

  Lemma assumeK {R} P (itr : itree crisE R) :
    SModTr.trans img sp (assumeK P itr) = assumeK P (SModTr.trans img sp itr).
  Proof using. eapply observe_eta; ss. f_equal. extensionality x. eapply observe_eta; ss. Qed.

  Lemma guaranteeK {R} P (itr : itree crisE R) :
    SModTr.trans img sp (guaranteeK P itr) = guaranteeK P (SModTr.trans img sp itr).
  Proof using. eapply observe_eta; ss. f_equal. extensionality x. eapply observe_eta; ss. Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree crisE R) :
    SModTr.trans img sp (unwrapUK x ktr) = unwrapUK x (λ x, SModTr.trans img sp (ktr x)).
  Proof using. destruct x; ss. eapply observe_eta; ss. f_equal. extensionality x. ss. Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree crisE R) :
    SModTr.trans img sp (unwrapNK x ktr) = unwrapNK x (λ x, SModTr.trans img sp (ktr x)).
  Proof using. destruct x; ss. eapply observe_eta; ss. f_equal. extensionality x. ss. Qed.

  Lemma yield tid :
    SModTr.trans img sp (trigger (Yield tid)) = tau;; SModTr.HoareYield img tid.
  Proof using.
    rewrite vis_yield. f_equal. f_equal. erewrite <- bind_ret_r; f_equal.
    extensionalities; rewrite ret //.
  Qed.

  Lemma spawn fn args :
    SModTr.trans img sp (trigger (Spawn fn args)) = tau;; SModTr.HoareSpawn fn args (sp fn).
  Proof using.
    rewrite vis_spawn. do 3 f_equal.
    rewrite -{2}(bind_ret_r (SModTr.HoareSpawn _ _ _)).
    f_equal. extensionalities. rewrite ret. et.
  Qed.

  Lemma gettid :
    SModTr.trans img sp (trigger GetTid) = tau;; SModTr.HoareGetTid img.
  Proof using.
    rewrite vis_gettid. do 3 f_equal.
    rewrite -{2}(bind_ret_r (SModTr.HoareGetTid _)).
    f_equal. extensionalities. rewrite ret. et.
  Qed.

  Lemma call fn args :
    SModTr.trans img sp (trigger (Call fn args)) = tau;; SModTr.HoareCall fn args (sp fn).
  Proof using.
    rewrite vis_call. do 3 f_equal.
    rewrite -{2}(bind_ret_r (SModTr.HoareCall _ _ _)).
    f_equal. extensionalities. rewrite ret. et.
  Qed.

  Lemma pg (R : Type) (i : pgE R) : SModTr.trans img sp (trigger i) = trigger i.
  Proof using.
    rewrite vis_pg. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma core (R : Type) (e : coreE R) : SModTr.trans img sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_core. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma ag {A} (e : agE A) : SModTr.trans img sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_ag. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
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
  Proof using. unfold guarantee. rewrite bind core. grind. rewrite ret. refl. Qed.

  Lemma ru {X} (pre post : X → _) :
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
  Proof using. rewrite /RealUpdateK bind ru //. Qed.

  Lemma fbody_trivial arg : SModTr.trans img sp (fbody_trivial arg) = fbody_trivial arg.
  Proof. rewrite /fbody_trivial /= core //. Qed.
End RED. End SRed.

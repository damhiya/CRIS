Require Import Common.
From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.
Require Import Mod FSpec Sp.

Set Implicit Arguments.

Arguments precond : simpl never.
Arguments postcond : simpl never.

Module SModTr.
Section HOARE.
  Context `{Σ: GRA}.

  Definition HoareCall fn (varg: Any.t) (fspo: option fspec): itree crisE Any.t
    :=
    match fspo with
    | Some fsp =>
      x <- trigger (Choose (meta fsp));;
    
      (*** precondition ***)
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (precond fsp x varg arg));;;

      (*** call ***)
      ret <- trigger (Call fn arg);;

      (*** postcondition ***)
      vret <- trigger (Take Any.t);;
      trigger (Assume (postcond fsp x vret ret));;;

      Ret vret
    | None =>
      trigger (Call fn varg)
    end.

  Definition HoareFun (fspo: option fspec) (body: Any.t → itree crisE Any.t)
    : Any.t → itree crisE Any.t
    :=
    match fspo with
    | Some fsp =>
      λ arg,
      x <- trigger (Take (meta fsp));;
      varg <- trigger (Take Any.t);;
      trigger (Assume (precond fsp x varg arg));;; (*** precondition ***)

      vret <- body varg;;

      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (postcond fsp x vret ret));;; (*** postcondition ***)

      Ret ret
    | None =>
      λ arg, tau;; body arg
    end.

  Definition NativeSpawn `{Σ: GRA} (fn: string) (arg: Any.t) : itree crisE nat :=
    trigger (Spawn fn arg).

  Definition HoareSpawn fn (varg: Any.t) (fspo: option fspec) : itree crisE nat :=
    match fspo with
    | Some fsp =>
      x <- trigger (Choose (meta fsp));; 
      arg <- trigger (Choose Any.t);; 
      trigger (Guarantee (precond fsp x varg arg));;;
      trigger (Spawn fn arg)
    | None =>
      NativeSpawn fn varg
    end.

  Definition handle (sp: sp_type): crisE ~> itreeV crisE.
  Proof.
    intros T e. destruct e.
    { exact (inr (existT _ (subevent _ a, fun v => Ret v))). }
    destruct s.
    { destruct c.
      - (* Call *)
        exact
          (inl (HoareCall fn args (sp fn))).
      - (* Spawn *)
        exact
          (inl ((HoareSpawn fn args) (sp fn))).
      - (* Yield *)
        exact (inl (trigger (Yield tid))).
    }
    destruct s.
    { exact (inr (existT _ (subevent _ p, fun v => Ret v))). }
    { exact (inr (existT _ (subevent _ c, fun v => Ret v))). }
  Defined.

  Definition trans sp {R} (it : itree crisE R) : itree crisE R :=
    interpV (handle sp) it.

  Definition trans_body : (sp_type * option fspec) → fbody → fbody :=
    λ '(sp,fsp) bd, HoareFun fsp (trans sp ∘ bd).

  Definition trans_ktree sp (sb: fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), trans_body (if sb.1.1.1 then sp else sp_none, fsp) bd) sb.

End HOARE.
End SModTr.

Notation "↧ it" := (SModTr.trans _ it) (at level 59, only printing).

Module SRed.
Section RED.
  Context `{Σ: GRA}.

  Variable sp: sp_type.

  Lemma bind
        (R S: Type)
        (s : itree crisE R) (k : R → itree crisE S)
    :
      SModTr.trans sp (s >>= k)
      =
      st <- SModTr.trans sp s;; SModTr.trans sp (k st).
  Proof using.
    unfold SModTr.trans in *. rewrite interpV_bind. et.
  Qed.

  Lemma tau
        (U : Type)
        (t : itree _ U)
    :
      SModTr.trans sp (tau;; t)
      =
      tau;; (SModTr.trans sp t).
  Proof using.
    unfold SModTr.trans in *. rewrite interpV_tau. et.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
    :
      SModTr.trans sp (Ret t)
      =
      Ret t.
  Proof using.
    unfold SModTr.trans in *. rewrite interpV_ret. et.
  Qed.

  Lemma vis_ag {X R} (e : agE X) (ktr : X -> itree crisE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_yield {R} tid (ktr : () -> itree crisE R) :
    SModTr.trans sp (vis (Yield tid) ktr) = tau;; my_tid <- trigger (Yield tid);; SModTr.trans sp (ktr my_tid).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_spawn {R} fn args (ktr : nat -> itree crisE R) :
    SModTr.trans sp (vis (Spawn fn args) ktr) =
      tau;;
      x <- SModTr.HoareSpawn fn args (sp fn);;
      SModTr.trans sp (ktr x).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss.
  Qed.
  
  Lemma vis_call {R} fn args (ktr : Any.t -> itree crisE R) :
    SModTr.trans sp (vis (Call fn args) ktr) =
      tau;;
      x <- SModTr.HoareCall fn args (sp fn);;
      SModTr.trans sp (ktr x).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree crisE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_core {X R} (e : coreE X) (ktr : X -> itree crisE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} P (itr : itree crisE R) :
    SModTr.trans sp (assumeK P itr) = assumeK P (SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK {R} P (itr : itree crisE R) :
    SModTr.trans sp (guaranteeK P itr) = guaranteeK P (SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree crisE R) :
    SModTr.trans sp (unwrapUK x ktr) = unwrapUK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree crisE R) :
    SModTr.trans sp (unwrapNK x ktr) = unwrapNK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma yield tid
    :
      SModTr.trans sp (trigger (Yield tid))
      =
      tau;; trigger (Yield tid).
  Proof using.
    rewrite vis_yield. f_equal. f_equal.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    f_equal. extensionalities. ired. f_equal. extensionalities. rewrite ret. et.
  Qed.

  Lemma spawn fn args
    :
    SModTr.trans sp (trigger (Spawn fn args))
    =
    tau;;
    SModTr.HoareSpawn fn args (sp fn).
  Proof using.
    rewrite vis_spawn. do 3 f_equal.
    rewrite -{2}(bind_ret_r (SModTr.HoareSpawn _ _ _)).
    f_equal. extensionalities. rewrite ret. et.
  Qed.
  
  Lemma call fn args
    :
    SModTr.trans sp (trigger (Call fn args))
    =
    tau;;
    SModTr.HoareCall fn args (sp fn).
  Proof using.
    rewrite vis_call. do 3 f_equal.
    rewrite -{2}(bind_ret_r (SModTr.HoareCall _ _ _)).
    f_equal. extensionalities. rewrite ret. et.
  Qed.

  Lemma pg
        (R: Type)
        (i: pgE R)
    :
      SModTr.trans sp (trigger i)
      =
      trigger i.
  Proof using.
    rewrite vis_pg. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma core
        (R: Type)
        (e: coreE R)
    :
    SModTr.trans sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_core. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma ag {A} (e: agE A)
    :
    SModTr.trans sp (trigger e) = trigger e.
  Proof using.
    rewrite vis_ag. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
    :
      SModTr.trans sp (@unwrapU crisE _ _ i)
      =
      unwrapU i.
  Proof using.
    unfold unwrapU. des_ifs; grind.
    - rewrite ret. eauto.
    - rewrite /triggerUB bind core. f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN
        (R: Type)
        (i: option R)
    :
      SModTr.trans sp (@unwrapN crisE _ _ i)
      =
      unwrapN i.
  Proof using.
    unfold unwrapN. des_ifs; grind.
    - rewrite ret. eauto.
    - unfold triggerNB. rewrite bind vis_core.
      eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. ss.
  Qed.
  
  Lemma asm P
    : 
      SModTr.trans sp (assume P)
      =
      assume P.
  Proof using.
    unfold assume. rewrite bind core. grind. rewrite ret. refl.
  Qed. 

  Lemma guar P
    : 
      SModTr.trans sp (guarantee P)
      =
      guarantee P.
  Proof using.
    unfold guarantee. rewrite bind core. grind. rewrite ret. refl.
  Qed.

  Lemma assume_proph {X R} Pre Post:
    SModTr.trans sp (@AssumeProph _ X R Pre Post) = AssumeProph Pre Post.
  Proof.
    rewrite /AssumeProph; unseal CRIS_PROPH.
    repeat (rewrite bind core; f_equal; extensionalities).
    repeat (rewrite bind ag; f_equal; extensionalities).
    rewrite ret. et.
  Qed.

  Lemma assume_prophK {X S R} Pre Post ktr :
    SModTr.trans sp (@AssumeProphK _ X S R Pre Post ktr)
    = AssumeProphK Pre Post (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    rewrite /AssumeProphK. rewrite bind assume_proph. et.
  Qed.

  Lemma fspec_proph fsp bd arg
    :
    SModTr.trans sp (fspec_proph fsp bd arg) =
    fspec_proph fsp ((SModTr.trans sp) ∘ bd) arg.
  Proof.
    rewrite /fspec_proph /AssumeProph. s. unseal CRIS_PROPH.
    rewrite !bind !core. repeat f_equal.
    - extensionalities. rewrite !bind !core. repeat f_equal.
      extensionalities. rewrite !bind !ag; et. repeat f_equal.
      extensionalities. f_equal. rewrite ret. et.
    - extensionalities. rewrite !bind. f_equal.
      extensionalities. rewrite !bind !ag; et. repeat f_equal.
      extensionalities. rewrite ret. et.
  Qed.

  Lemma fbody_trivial arg:
    SModTr.trans sp (fbody_trivial arg) = fbody_trivial arg.
  Proof.
    rewrite /fbody_trivial. s. rewrite core. et.
  Qed.

End RED. End SRed.

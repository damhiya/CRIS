Require Import Common.
Require Import HMod FSpec.

Set Implicit Arguments.

Arguments precond : simpl never.
Arguments postcond : simpl never.

Module SModTr.
Section HOARE.

  Context `{Σ: GRA}.

  Variable sp: string → option fspec.

  Definition HoareCall (fsp: fspec): string → Any.t → (itree hmodE) Any.t 
    := 
    λ fn varg,
      x <- trigger (Choose fsp.(meta));; 

      (*** precondition ***)
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (fsp.(precond) x varg arg));;;

      (*** call ***)
      ret <- trigger (Call fn arg);;

      (*** postcondition ***)
      vret <- trigger (Take Any.t);;
      trigger (Assume (fsp.(postcond) x vret ret));;;

      Ret vret.

  Definition HoareSpawn (fsp: fspec) (fn: string) (varg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; 
    arg <- trigger (Choose Any.t);;
    tid <- trigger (Spawn fn arg);;
    trigger (Guarantee (fsp.(precond) x varg arg));;;
    trigger (Yield tid);;;
    Ret tid.

  Definition handle: hmodE ~> itreeV hmodE :=
    fun T e =>
      match e with
      | inr1 (inl1 c) =>
          match c in callE T return itreeV hmodE T with
          | Call fn args =>
              inl (fsp <- (sp fn)!;; HoareCall fsp fn args)
          | Spawn fn args =>
              inl (fsp <- (sp fn)!;; HoareSpawn fsp fn args)
          | Yield tid => inr (existT _ (subevent _ (Yield tid), fun v => Ret v))
          end
      | _ =>
          inr (existT _ (e, fun v => Ret v))
      end.
  
  Definition trans R (it : itree hmodE R) : itree hmodE R :=
    interpV handle it.

  Definition HoareFun {X: Type}
      (P: X → Any.t → Any.t → iProp Σ)
      (Q: X → Any.t → Any.t → iProp Σ)
      (body: Any.t → itree hmodE Any.t): Any.t → itree hmodE Any.t :=
    λ arg,
      x <- trigger (Take X);;

      varg <- trigger (Take _);;
      trigger (Assume (P x varg arg));;; (*** precondition ***)

      vret <- body varg;;

      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (Q x vret ret));;; (*** postcondition ***)

      Ret ret.
  
  Definition trans_ktree (sb: fspecbody): (Any.t → itree hmodE Any.t) :=
    let fs: fspec := sb.(fsb_fspec) in
    HoareFun fs.(precond) fs.(postcond) (λ arg, trans (sb.(fsb_body) arg)).

End HOARE.
End SModTr.

Notation "↧ it" := (SModTr.trans _ it) (at level 59, only printing).

Module SRed.
Section RED.

  Context `{Σ : GRA}.

  Variable sp: string → option fspec.

  Lemma bind
        (R S: Type)
        (s : itree hmodE R) (k : R → itree hmodE S)
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

  Lemma vis_ag {X R} (e : agE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_yield {R} tid (ktr : () -> itree hmodE R) :
    SModTr.trans sp (vis (Yield tid) ktr) = vis (Yield tid) (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_spawn {R} fn args (ktr : nat -> itree hmodE R) :
    SModTr.trans sp (vis (Spawn fn args) ktr) =
      tau;; fsp <- (sp fn)!;; x <- SModTr.HoareSpawn fsp fn args;; SModTr.trans sp (ktr x).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. ired. eauto.
  Qed.
  
  Lemma vis_call {R} fn args (ktr : Any.t -> itree hmodE R) :
    SModTr.trans sp (vis (Call fn args) ktr) =
      tau;; fsp <- (sp fn)!;; x <- SModTr.HoareCall fsp fn args;; SModTr.trans sp (ktr x).
  Proof using.
    unfold SModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. ired. eauto.
  Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_core {X R} (e : coreE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} P (itr : itree hmodE R) :
    SModTr.trans sp (assumeK P itr) = assumeK P (SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK {R} P (itr : itree hmodE R) :
    SModTr.trans sp (guaranteeK P itr) = guaranteeK P (SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree hmodE R) :
    SModTr.trans sp (unwrapUK x ktr) = unwrapUK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree hmodE R) :
    SModTr.trans sp (unwrapNK x ktr) = unwrapNK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma yield tid
    :
      SModTr.trans sp (trigger (Yield tid))
      =
      trigger (Yield tid).
  Proof using.
    rewrite vis_yield. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma spawn fn args
    :
    SModTr.trans sp (trigger (Spawn fn args))
    =
    tau;; fsp <- (sp fn)!;; SModTr.HoareSpawn fsp fn args.
  Proof using.
    rewrite vis_spawn. do 3 f_equal. extensionalities.
    etrans; cycle 1.
    - rewrite -(bind_ret_r (SModTr.HoareSpawn _ _ _)). refl.
    - f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma call fn args
    :
      SModTr.trans sp (trigger (Call fn args))
      =
      tau;; fsp <- (sp fn)!;; SModTr.HoareCall fsp fn args.
  Proof using.
    rewrite vis_call. do 3 f_equal. extensionalities.
    etrans; cycle 1.
    - rewrite -(bind_ret_r (SModTr.HoareCall _ _ _)). refl.
    - f_equal. extensionalities. rewrite ret. eauto.
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
      SModTr.trans sp (@unwrapU hmodE _ _ i)
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
      SModTr.trans sp (@unwrapN hmodE _ _ i)
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

  Lemma fbody_trivial arg:
    SModTr.trans sp (fbody_trivial arg) = fbody_trivial arg.
  Proof.
    rewrite /fbody_trivial. s. rewrite core. et.
  Qed.
  
End RED. End SRed.

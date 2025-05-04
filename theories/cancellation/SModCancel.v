Require Import Common.
Require Import SMod HMod.
Require Import SModTr.

Set Implicit Arguments.

Module SModCancel.
Section Cancel.
  Import SMod.
  Context `{Σ: GRA}.

  Definition HoareSpawn (fn: string) (varg: Any.t) : itree hmodE nat :=
    tid <- trigger (Spawn fn varg);;
    trigger (Yield tid);;;
    Ret tid.

  Definition handle: hmodE ~> itreeV hmodE :=
    fun T e =>
      match e with
      | inr1 (inl1 c) =>
          match c in callE T with
          | Call fn args =>
              inl (trigger (Call fn args))
          | Spawn fn args => inl (HoareSpawn fn args)
          | Yield tid => inr (existT _ (subevent _ (Yield tid), fun v => Ret v))
          end
      | _ =>
          inr (existT _ (e, fun v => Ret v))
      end.
  
  Definition trans R (it : itree hmodE R) : itree hmodE R :=
    interpV handle it.

  Definition trans_ktree (sb: fspecbody): Any.t -> itree hmodE Any.t :=
    fun arg =>
      trans (sb.(fsb_body) arg).
  
  Program Definition to_hmod (ms: t): HMod.t := {|
    HMod.scopes := ms.(scopes);
    HMod.fnsems := List.map (map_snd (λ ksb, (ksb.1, trans_ktree ksb.2))) (ms.(fnsems));
    HMod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite! alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End Cancel.
End SModCancel.

Module SCancelRed.

  Lemma bind `{Σ : GRA}
        (R S: Type)
        
        (s : itree hmodE R) (k : R -> itree hmodE S)
    :
      SModCancel.trans (s >>= k)
      =
      st <- SModCancel.trans s;; SModCancel.trans (k st).
  Proof using.
    unfold SModCancel.trans in *. rewrite interpV_bind. eauto.
  Qed.

  Lemma tau `{Σ : GRA}
        (U : Type)
        (t : itree _ U)
        
    :
      SModCancel.trans (tau;; t)
      =
      tau;; (SModCancel.trans t).
  Proof using.
    unfold SModCancel.trans in *. rewrite interpV_tau. eauto.
  Qed.

  Lemma ret `{Σ : GRA}
        (U: Type)
        (t: U)
        
    :
      SModCancel.trans (Ret t)
      =
      Ret t.
  Proof using.
    unfold SModCancel.trans in *. rewrite interpV_ret. eauto.
  Qed.

  Lemma yield `{Σ : GRA}
    tid
    :
    SModCancel.trans (trigger (Yield tid))
    =
    trigger (Yield tid).
  Proof using.
    unfold SModCancel.trans in *. unfold trigger. rewrite interpV_vis. s.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    rewrite interpV_ret. et.
  Qed.

  Lemma spawn `{Σ : GRA}
    fn args
    :
    SModCancel.trans (trigger (Spawn fn args))
    =
    tau;; SModCancel.HoareSpawn fn args.
  Proof using.
    unfold SModCancel.trans in *. unfold trigger. rewrite interpV_vis. s.
    ired. do 2 f_equal. eapply observe_eta; ss. f_equal. extensionalities.
    ired. f_equal. extensionalities. rewrite interpV_ret. et.
  Qed.
  
  Lemma call `{Σ : GRA}
    fn args
    :
    SModCancel.trans (trigger (Call fn args))
    =
    tau;; trigger (Call fn args).
  Proof using.
    unfold SModCancel.trans, trigger in *. rewrite interpV_vis. s. ired.
    eapply observe_eta; ss. f_equal.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    rewrite interpV_ret. eauto.
  Qed.

  Lemma pg `{Σ : GRA}
        (R: Type)
        (i: pgE R)
        
    :
      SModCancel.trans (trigger i)
      =
      trigger i.
  Proof using.
    unfold SModCancel.trans, trigger. rewrite interpV_vis. s. ired.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    rewrite interpV_ret. eauto.
  Qed.

  Lemma core `{Σ : GRA}
        (R: Type)
        (i: coreE R)
        
    :
      SModCancel.trans (trigger i)
      =
      trigger i.
  Proof using.
    unfold SModCancel.trans, trigger. rewrite interpV_vis. s. ired.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    rewrite interpV_ret. eauto.
  Qed.

  Lemma ag `{Σ : GRA} {A} (e: agE A)
        
    :
      SModCancel.trans (trigger e)
      =
      trigger e.
  Proof using.
    unfold SModCancel.trans, trigger. rewrite interpV_vis. s. ired.
    eapply observe_eta; ss. f_equal. extensionalities. ired.
    rewrite interpV_ret. eauto.
  Qed.
  
  Lemma unwrapU `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      SModCancel.trans (@unwrapU hmodE _ _ i)
      =
      unwrapU i.
  Proof using.
    unfold SModCancel.trans, unwrapU in *. des_ifs; grind.
    - rewrite interpV_ret. et.
    - unfold triggerUB. rewrite !interpV_bind !interpV_vis. s.
      ired. eapply observe_eta; ss. f_equal. extensionalities.
      ired. ss.
  Qed.

  Lemma unwrapN `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      SModCancel.trans (@unwrapN hmodE _ _ i)
      =
      unwrapN i.
  Proof using.
    unfold SModCancel.trans, unwrapN in *. des_ifs; grind.
    - rewrite interpV_ret. et.
    - unfold triggerUB. rewrite !interpV_bind !interpV_vis. s.
      ired. eapply observe_eta; ss. f_equal. extensionalities.
      ired. ss.
  Qed.
  
  Lemma asm `{Σ : GRA}
        P
    : 
      SModCancel.trans (assume P)
      =
      assume P.
  Proof using.
    unfold assume. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed. 

  Lemma grt `{Σ : GRA}
        P
    : 
      SModCancel.trans (guarantee P)
      =
      guarantee P.
  Proof using.
    unfold guarantee. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed.

End SCancelRed.

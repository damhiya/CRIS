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

  Definition handle_schE_hmodE : schE ~> itree hmodE :=
    fun _ e =>
      match e in schE T return itree hmodE T with
      | Spawn fn varg => HoareSpawn fn varg
      | Yield tid => trigger (Yield tid)
      end.

  Definition trans R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_schE_hmodE
           (case_ (bif:=sum1) trivial_Handler
                              trivial_Handler))) it.

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
    unfold SModCancel.trans in *. grind.
  Qed.

  Lemma tau `{Σ : GRA}
        (U : Type)
        (t : itree _ U)
        
    :
      SModCancel.trans (tau;; t)
      =
      tau;; (SModCancel.trans t).
  Proof using.
    unfold SModCancel.trans in *. grind.
  Qed.

  Lemma ret `{Σ : GRA}
        (U: Type)
        (t: U)
        
    :
      SModCancel.trans (Ret t)
      =
      Ret t.
  Proof using.
    unfold SModCancel.trans in *. grind.
  Qed.

  Lemma sch `{Σ : GRA}
        (R: Type)
        (i: schE R)
        
    :
      SModCancel.trans (trigger i)
      =
      r <- SModCancel.handle_schE_hmodE i;; tau;; Ret r.
  Proof using.
    unfold SModCancel.trans in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma call `{Σ : GRA}
        (R: Type)
        (i: callE R)
        
    :
      SModCancel.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold SModCancel.trans in *. rewrite interp_trigger. grind.
  Qed.

  Lemma pg `{Σ : GRA}
        (R: Type)
        (i: pgE R)
        
    :
      SModCancel.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold SModCancel.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma core `{Σ : GRA}
        (R: Type)
        (i: coreE R)
        
    :
      SModCancel.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold SModCancel.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma ag `{Σ : GRA} {A} (e: agE A)
        
    :
      SModCancel.trans (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof using.
    unfold SModCancel.trans. rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      SModCancel.trans (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof using.
    unfold SModCancel.trans, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma unwrapN `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      SModCancel.trans (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof using.
    unfold SModCancel.trans, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma asm `{Σ : GRA}
        P
    : 
      SModCancel.trans (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof using.
    unfold assume. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed. 

  Lemma grt `{Σ : GRA}
        P
    : 
      SModCancel.trans (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof using.
    unfold guarantee. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed.

End SCancelRed.

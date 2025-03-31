Require Import Common.
Require Import SMod HMod.
Require Import SMod2HMod.

Set Implicit Arguments.

Section Cancel.
  Context {Σ: GRA}.

  Definition Spawn_cancel (fn: string) (varg: Any.t) : itree hmodE nat :=
    tid <- trigger (Spawn fn varg);;
    trigger (Yield tid);;;
    Ret tid.

  Definition handle_schE_hmodE_cancel : schE ~> itree hmodE :=
    fun _ e =>
      match e in schE T return itree hmodE T with
      | Spawn fn varg => Spawn_cancel fn varg
      | Yield tid => trigger (Yield tid)
      end.

  Definition interp_smod_cancel R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_schE_hmodE_cancel
           (case_ (bif:=sum1) trivial_Handler
                              trivial_Handler))) it.

  Definition interp_sb_hp_cancel (sb: fspecbody): Any.t -> itree hmodE Any.t :=
    fun arg =>
      interp_smod_cancel (sb.(fsb_body) arg).

End Cancel.

Module SModCancel.
Section Cancel.
  Import SMod.
  Context `{Σ: GRA}.

  Program Definition to_hmod (ms: t): HMod.t := {|
    HMod.scopes := ms.(scopes);
    HMod.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp_cancel ksb.2))) (ms.(fnsems));
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
      interp_smod_cancel (s >>= k)
      =
      st <- interp_smod_cancel s;; interp_smod_cancel (k st).
  Proof using.
    unfold interp_smod_cancel in *. grind.
  Qed.

  Lemma tau `{Σ : GRA}
        (U : Type)
        (t : itree _ U)
        
    :
      interp_smod_cancel (tau;; t)
      =
      tau;; (interp_smod_cancel t).
  Proof using.
    unfold interp_smod_cancel in *. grind.
  Qed.

  Lemma ret `{Σ : GRA}
        (U: Type)
        (t: U)
        
    :
      interp_smod_cancel (Ret t)
      =
      Ret t.
  Proof using.
    unfold interp_smod_cancel in *. grind.
  Qed.

  Lemma sch `{Σ : GRA}
        (R: Type)
        (i: schE R)
        
    :
      interp_smod_cancel (trigger i)
      =
      r <- handle_schE_hmodE_cancel i;; tau;; Ret r.
  Proof using.
    unfold interp_smod_cancel in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma call `{Σ : GRA}
        (R: Type)
        (i: callE R)
        
    :
      interp_smod_cancel (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold interp_smod_cancel in *. rewrite interp_trigger. grind.
  Qed.

  Lemma pg `{Σ : GRA}
        (R: Type)
        (i: pgE R)
        
    :
      interp_smod_cancel (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold interp_smod_cancel. rewrite interp_trigger. grind.
  Qed.

  Lemma core `{Σ : GRA}
        (R: Type)
        (i: coreE R)
        
    :
      interp_smod_cancel (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold interp_smod_cancel. rewrite interp_trigger. grind.
  Qed.

  Lemma ag `{Σ : GRA} {A} (e: agE A)
        
    :
      interp_smod_cancel (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof using.
    unfold interp_smod_cancel. rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      interp_smod_cancel (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof using.
    unfold interp_smod_cancel, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma unwrapN `{Σ : GRA}
        (R: Type)
        (i: option R)
        
    :
      interp_smod_cancel (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof using.
    unfold interp_smod_cancel, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma asm `{Σ : GRA}
        P
    : 
      interp_smod_cancel (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof using.
    unfold assume. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed. 

  Lemma grt `{Σ : GRA}
        P
    : 
      interp_smod_cancel (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof using.
    unfold guarantee. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed.

End SCancelRed.

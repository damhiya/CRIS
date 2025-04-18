Require Import Common.
Require Import HMod.

Set Implicit Arguments.

Module PModTr.
Section PMOD.

  Context `{Σ : GRA}.

  Definition handle_core: coreE ~> itree hmodE :=
    fun T e =>
      match e return itree hmodE T with
      | Take X => if excluded_middle_informative (∃ P: Prop, X = P)
                  then trigger e
                  else triggerUB
      | _ => trigger e
      end.

  Definition trans {R} (itr: itree pmodE R) : itree hmodE R
    :=
    interp
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) trivial_Handler
         handle_core)))
      itr.

End PMOD.
End PModTr.

Notation "↥ it" := (PModTr.trans it) (at level 60, only printing).

Module PRed.
Section RED.

  Context `{Σ : GRA}.

(* itree reduction *)
  Lemma bind
        (R S: Type)
        (s : itree pmodE R) (k : R -> itree pmodE S)
    :
    PModTr.trans (s >>= k)
    =
    st <- PModTr.trans s;; PModTr.trans (k st).
  Proof using.
    unfold PModTr.trans. grind.
  Qed.

  Lemma tau
        (U: Type)
        (t : itree _ U)
    :
      PModTr.trans (tau;; t)
      =
      tau;; (PModTr.trans t).
  Proof using.
    unfold PModTr.trans. grind.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
    :
      PModTr.trans (Ret t)
      =
      Ret t.
  Proof using.
    unfold PModTr.trans. grind.
  Qed.

  Lemma vis_sch {X R} (e : schE X) (ktr : X -> itree pmodE R) :
    PModTr.trans (vis e ktr) = vis e (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_call {X R} (e : callE X) (ktr : X -> itree pmodE R) :
    PModTr.trans (vis e ktr) = vis e (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree pmodE R) :
    PModTr.trans (vis e ktr) = vis e (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_choose {X R} (ktr : X -> itree pmodE R) :
    PModTr.trans (vis (Choose X) ktr) = vis (Choose X) (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_take {X : Prop} {R} (ktr : X -> itree pmodE R) :
    PModTr.trans (vis (Take X) ktr) = vis (Take X) (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists X. reflexivity.
  Qed.

  Lemma vis_io {I O R} fn args (ktr : O -> itree pmodE R) :
    PModTr.trans (vis (@IO I O fn args) ktr) = vis (IO fn args) (fun x => tau;; PModTr.trans (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} P (itr : itree pmodE R) :
    PModTr.trans (assumeK P itr) = assumeK P (tau;; PModTr.trans itr).
  Proof using.
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists P. reflexivity.
  Qed.

  Lemma guaranteeK {R} P (itr : itree pmodE R) :
    PModTr.trans (guaranteeK P itr) = guaranteeK P (tau;; PModTr.trans itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree pmodE R) :
    PModTr.trans (unwrapUK x ktr) = unwrapUK x (fun x => PModTr.trans (ktr x)).
  Proof using.
    destruct x; ss. eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists False. reflexivity.
  Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree pmodE R) :
    PModTr.trans (unwrapNK x ktr) = unwrapNK x (fun x => PModTr.trans (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call
        (R: Type)
        (i: callE R)
    :
      PModTr.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PModTr.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma sch
        (R: Type)
        (i: schE R)
    :
      PModTr.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PModTr.trans. rewrite interp_trigger. grind.
  Qed.
  
  Lemma pg
        (R: Type)
        (i: pgE R)
    :
      PModTr.trans (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PModTr.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma take
        (P: Prop)
    :
      PModTr.trans (trigger (Take P))
      =
      r <- trigger (Take P);; tau;; Ret r.
  Proof using.
    unfold PModTr.trans, PModTr.handle_core.
    rewrite interp_trigger. grind.
    exfalso. eauto.
  Qed.
  
  Lemma choose
        (X: Type)
    :
      PModTr.trans (trigger (Choose X))
      =
      r <- trigger (Choose X);; tau;; Ret r.
  Proof using.
    unfold PModTr.trans, PModTr.handle_core.
    rewrite interp_trigger. grind.
  Qed.

  Lemma io
        I O fn args
    :
      PModTr.trans (trigger (@IO I O fn args))
      =
      r <- trigger (IO fn args);; tau;; Ret r.
  Proof using.
    unfold PModTr.trans, PModTr.handle_core.
    rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
    :
    PModTr.trans (@unwrapU pmodE _ _ i)
    =
    unwrapU i.
  Proof using.
    rewrite /unwrapU. des_ifs.
    - rewrite ret; eauto.
    - rewrite /triggerUB !bind !take. grind.
  Qed.

  Lemma unwrapN
        (R: Type)
        (i: option R)
    :
      PModTr.trans (@unwrapN pmodE _ _ i)
      =
      unwrapN i.
  Proof using.
    rewrite /unwrapN. des_ifs.
    - rewrite ret; eauto.
    - rewrite /triggerNB !bind !choose. grind.
  Qed.

  Lemma asm
        P
    : 
      PModTr.trans (assume P)
      =
      assume P;;; tau;; Ret ().
  Proof using.
    rewrite /assume !bind !take !ret. grind.
  Qed. 

  Lemma guar
        P
    : 
      PModTr.trans (guarantee P)
      =
      guarantee P;;; tau;; Ret ().
  Proof using.
    rewrite /guarantee !bind !choose !ret. grind.
  Qed.
  
End RED.
End PRed.

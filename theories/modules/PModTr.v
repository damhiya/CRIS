Require Import Common.
Require Import FSpec HMod.

Set Implicit Arguments.

Module PModTr.
Section PMOD.

  Context `{Σ : GRA}.

  Definition handle: hmodE ~> itreeV hmodE :=
    fun T e =>
      inr
      match e with
      | inr1 (inr1 (inr1 (Take X))) =>
          if excluded_middle_informative (∃ P: Prop, X = P)
          then existT _ (subevent _ e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inl1 (Assume P) =>
          existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | _ => existT _ (e, fun v => Ret v)
      end.

  Definition trans {R} (itr: itree hmodE R) : itree hmodE R
    :=
    interpV handle itr.

End PMOD.
End PModTr.

Notation "↥ it" := (PModTr.trans it) (at level 60, only printing).

Module PRed.
Section RED.

  Context `{Σ : GRA}.

  (* itree reduction *)
  Lemma bind
        (R S: Type)
        (s : itree hmodE R) (k : R -> itree hmodE S)
    :
    PModTr.trans (s >>= k)
    =
    st <- PModTr.trans s;; PModTr.trans (k st).
  Proof using.
    unfold PModTr.trans. rewrite interpV_bind. eauto.
  Qed.

  Lemma tau
        (U: Type)
        (t : itree _ U)
    :
      PModTr.trans (tau;; t)
      =
      tau;; (PModTr.trans t).
  Proof using.
    unfold PModTr.trans. rewrite interpV_tau. eauto.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
    :
      PModTr.trans (Ret t)
      =
      Ret t.
  Proof using.
    unfold PModTr.trans. rewrite interpV_ret. eauto.
  Qed.

  Lemma vis_call {X R} (e : callE X) (ktr : X -> itree hmodE R) :
    PModTr.trans (vis e ktr) = vis e (fun x => PModTr.trans (ktr x)).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_ag {X R} (e : agE X) (ktr : X -> itree hmodE R)
    :
    match e with | Assume _ => False | _ => True end →
    PModTr.trans (vis e ktr) = vis e (fun x => PModTr.trans (ktr x)).
  Proof using.
    i. eapply observe_eta; ss. destruct e; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
  Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree hmodE R) :
    PModTr.trans (vis e ktr) = vis e (fun x => PModTr.trans (ktr x)).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_choose {X R} (ktr : X -> itree hmodE R) :
    PModTr.trans (vis (Choose X) ktr) = vis (Choose X) (fun x => PModTr.trans (ktr x)).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_take {X : Prop} {R} (ktr : X -> itree hmodE R) :
    PModTr.trans (vis (Take X) ktr) = vis (Take X) (fun x => PModTr.trans (ktr x)).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists X. reflexivity.
  Qed.

  Lemma vis_io {I O R} fn args (ktr : O -> itree hmodE R) :
    PModTr.trans (vis (@IO I O fn args) ktr) = vis (IO fn args) (fun x => PModTr.trans (ktr x)).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.    
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} P (itr : itree hmodE R) :
    PModTr.trans (assumeK P itr) = assumeK P (PModTr.trans itr).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.    
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists P. reflexivity.
  Qed.

  Lemma guaranteeK {R} P (itr : itree hmodE R) :
    PModTr.trans (guaranteeK P itr) = guaranteeK P (PModTr.trans itr).
  Proof using.
    unfold PModTr.trans. rewrite interpV_vis.    
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree hmodE R) :
    PModTr.trans (unwrapUK x ktr) = unwrapUK x (fun x => PModTr.trans (ktr x)).
  Proof using.
    destruct x; ss. eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists False. reflexivity.
  Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree hmodE R) :
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
      trigger i.
  Proof using.
    rewrite vis_call. eapply observe_eta; ss. f_equal. extensionalities.
    rewrite ret. eauto.
  Qed.

  Lemma ag {A} (e: agE A)
    :
    match e with | Assume _ => False | _ => True end →
    PModTr.trans (trigger e) = trigger e.
  Proof using.
    i. rewrite vis_ag; et. unfold trigger.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma pg
        (R: Type)
        (i: pgE R)
    :
      PModTr.trans (trigger i)
      =
      trigger i.
  Proof using.
    rewrite vis_pg. eapply observe_eta; ss. f_equal. extensionalities.
    rewrite ret. ired. eauto.
  Qed.

  Lemma take
        (P: Prop)
    :
      PModTr.trans (trigger (Take P))
      =
      trigger (Take P).
  Proof using.
    rewrite vis_take. eapply observe_eta; ss. f_equal. extensionalities.
    rewrite ret. ired. eauto.
  Qed.
  
  Lemma choose
        (X: Type)
    :
      PModTr.trans (trigger (Choose X))
      =
      trigger (Choose X).
  Proof using.
    rewrite vis_choose. eapply observe_eta; ss. f_equal. extensionalities.
    rewrite ret. ired. eauto.
  Qed.

  Lemma io
        I O fn args
    :
      PModTr.trans (trigger (@IO I O fn args))
      =
      trigger (IO fn args).
  Proof using.
    rewrite vis_io. eapply observe_eta; ss. f_equal. extensionalities.
    rewrite ret. ired. eauto.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
    :
    PModTr.trans (@unwrapU hmodE _ _ i)
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
      PModTr.trans (@unwrapN hmodE _ _ i)
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
      assume P.
  Proof using.
    rewrite /assume !bind !take !ret. grind.
  Qed. 

  Lemma guar
        P
    : 
      PModTr.trans (guarantee P)
      =
      guarantee P.
  Proof using.
    rewrite /guarantee !bind !choose !ret. grind.
  Qed.

  Lemma assume_proph {X R} Pre Post:
    PModTr.trans (@AssumeProph _ X R Pre Post) = AssumeProph Pre Post.
  Proof.
    rewrite /AssumeProph. unseal CRIS_PROPH.
    repeat (rewrite bind choose; f_equal; extensionalities).
    repeat (rewrite bind ag; f_equal; extensionalities).
    rewrite ret. et.
  Qed.

  Lemma assume_prophK {X S R} Pre Post ktr :
    PModTr.trans (@AssumeProphK _ X S R Pre Post ktr)
    = AssumeProphK Pre Post (fun x => PModTr.trans (ktr x)).
  Proof using.
    rewrite /AssumeProphK. rewrite bind assume_proph. et.
  Qed.

  Lemma fspec_proph fsp fbody arg
    :
    PModTr.trans (fspec_proph fsp fbody arg) =
    fspec_proph fsp (λ arg, PModTr.trans (fbody arg)) arg.
  Proof.
    rewrite /fspec_proph /AssumeProph.
    unseal CRIS_PROPH. rewrite !bind !choose. repeat f_equal.
    - extensionalities. rewrite !bind !choose. repeat f_equal.
      extensionalities. rewrite !bind !ag; et. repeat f_equal.
      extensionalities. f_equal. rewrite ret. et.
    - extensionalities. rewrite !bind. f_equal.
      extensionalities. rewrite !bind !ag; et. repeat f_equal.
      extensionalities. rewrite ret. et.
  Qed.

  Lemma fbody_trivial arg:
    PModTr.trans (fbody_trivial arg) = fbody_trivial arg.
  Proof.
    rewrite /fbody_trivial. extensionalities. s. rewrite choose. et.
  Qed.
  
End RED.
End PRed.

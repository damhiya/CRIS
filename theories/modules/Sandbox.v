Require Import FSpec.
Require Import Common.

Module SB. Section SB.
  Context `{Σ : GRA}.

  (**** Sandboxing ****)

  Definition msk_default T (e : crisE T) : bool :=
    match e with
    | (|||Choose X)%sum => true
    | (|||Take X)%sum => excluded_middle_informative (∃ P : Prop, X = P)
    | (Guarantee _|)%sum => true
    | (AssumeRes _|)%sum => true
    | _ => false
    end.

  Definition handle (msk : emask) : crisE ~> itreeV crisE :=
    λ T e,
      if msk T (subevent _ e) || msk_default T (subevent _ e)
      then inr (existT T (subevent _ e, λ x, Ret x))
      else inr (existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).

  Definition sandbox (msk : emask) {T} (itr : itree crisE T) : itree crisE T :=
    interpV (handle msk) itr.

  Definition sandbox_body (kb : emask * fbody) : Any.t → itree crisE Any.t :=
    λ arg, sandbox kb.1 (kb.2 arg).
End SB. End SB.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind msk {A B} (itr : itree crisE A) (ktr : A → itree crisE B) :
    SB.sandbox msk (itr >>= ktr) =
    a <- (SB.sandbox msk itr);; (SB.sandbox msk (ktr a)).
  Proof using. rewrite /SB.sandbox interpV_bind; eauto. Qed.

  Lemma tau msk {A} (itr : itree crisE A) :
    SB.sandbox msk (tau;; itr) = tau;; (SB.sandbox msk itr).
  Proof using. rewrite /SB.sandbox interpV_tau; eauto. Qed.

  Lemma ret msk {A} (a : A) :
    SB.sandbox msk (Ret a) = Ret a.
  Proof using. rewrite /SB.sandbox interpV_ret; eauto. Qed.

  Lemma vis msk {X R} (e : crisE X) (k : X → itree crisE R) :
    SB.sandbox msk (Vis e k) =
    if msk X e || SB.msk_default X e
    then Vis e (λ x, SB.sandbox msk (k x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SB.sandbox interpV_vis /SB.handle ?subevent_subevent.
    case_match eqn : H; rewrite H /=.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind.
    ired.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind. 
  Qed.

  Lemma assumeK msk {R} P (itr : itree crisE R) :
    SB.sandbox msk (assumeK P itr) = assumeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. rewrite /SB.handle; s.
    destruct (excluded_middle_informative _); s; cycle 1.
    { exfalso. eapply n. et. }
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma guaranteeK msk {R} P (itr : itree crisE R) :
    SB.sandbox msk (guaranteeK P itr) = guaranteeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. rewrite /SB.handle; s.
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma unwrapUK msk {X R} x (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapUK x ktr) = unwrapUK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    eapply observe_eta; ss. destruct x; et; ss. rewrite /SB.handle; s.
    destruct (excluded_middle_informative _); s; cycle 1.
    { exfalso. eapply n. et. }
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma unwrapNK msk {X R} (x : option X) (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapNK x ktr) = unwrapNK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    eapply observe_eta; ss. destruct x; et; ss. rewrite /SB.handle; s.
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma ruK msk {R} pp (ktr : _ → itree crisE R) :
    SB.sandbox msk (RealUpdateK pp ktr) = RealUpdateK pp (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    rewrite /RealUpdateK /RealUpdate. unseal CRIS_FancyReal. ired.
    rewrite !SBRed.bind !SBRed.vis !trigger_vis; s; bsimpl.
    f_equal; [repeat f_equal; extensionalities; apply ret|extensionalities].
    rewrite !SBRed.bind !SBRed.vis !trigger_vis; s; bsimpl.
    repeat (repeat f_equal; extensionalities); apply ret.
  Qed.

End SBRed. End SBRed.

Section Properties.
  Context `{Σ: GRA}.

  Lemma sandbox_sandbox {R} (t : itree crisE R) (msk1 msk2 : emask) :
    msk_sub msk1 msk2 →
    SB.sandbox msk2 (SB.sandbox msk1 t) = SB.sandbox msk1 t.
  Proof using.
    intros Hmsk; eapply bisim_is_eq.
    eapply gpaco2_init with (clo:=eqitC _ _ _); eauto with paco.
    revert R t msk1 msk2 Hmsk. gcofix CIH. i.
    rewrite (bisim_is_eq (itree_eta t)). destruct (observe t).
    { rewrite !SBRed.ret. eapply Reflexive_eqit_gen. et. }
    { rewrite !SBRed.tau. gstep. econs. gbase. et. }

    rewrite -bind_trigger !SBRed.bind.
    rewrite !SBRed.vis; case_match eqn : Hmsk1; cycle 1.
    { rewrite !SBRed.vis; case_match eqn : Hmsk2; ss.
      { gstep. rewrite !bind_vis. econs; ss. }
      gstep. rewrite !bind_vis. econs; ss.
    }
    rewrite !SBRed.vis; case_match eqn : Hmsk2; ss; cycle 1.
    { bsimpl. destruct Hmsk2 as [E1 E2]. rewrite E2 in Hmsk1. des; ss.
      eapply Hmsk in Hmsk1. rewrite E1 in Hmsk1. ss. }
    rewrite !bind_vis. gstep. econs. intros x.
    rewrite !SBRed.ret; ired.
    gbase. eapply CIH. auto.
  Qed.
End Properties.

Notation "░ it" := (SB.sandbox _ it) (at level 60, only printing).
Notation "'⇓sbox(' msk ')'" := (SB.sandbox msk) (at level 60, only parsing).

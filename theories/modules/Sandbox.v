Require Import FSpec.
Require Import Common.

(* Set Implicit Arguments. *)

(* Definition fnsem_type `{Σ : GRA} T : Type :=
  bool *               (* imaginary or real spec *)
  (string → bool) *   (* emask *)
  (list string) *      (* scope *)
  T.                   function semantics *)

(* Masks for function calls *)
(* Section WMask.
  Definition wmask_all : string → bool := const true.

  Definition wmask_none : string → bool := const false.

  Definition wmask_list (fns: list string) : string → bool :=
    λ f, (existsb (String.eqb f) fns).

  Definition wmask_or (msk1 msk2 : string → bool) :=
    λ fn, msk1 fn || msk2 fn.

  Definition wmask_and (msk1 msk2 : string → bool) :=
    λ fn, msk1 fn && msk2 fn.

  Definition wmask_sub (msk1 msk2 : string→bool) :=
    ∀ fn, msk1 fn → msk2 fn.
End WMask. *)

Module SB. Section SB.
  Context `{Σ : GRA}.

  (**** Sandboxing ****)
  Definition handle (msk : emask) : crisE ~> itreeV crisE :=
    λ T e,
      if msk T (subevent _ e)
      then inr (existT T (subevent _ e, λ x, Ret x))
      else inr (existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
    (* : ∀ T, crisE T → (itree crisE T + {X: Type & crisE X * (X → itree crisE T)})%type. *)
  (* Proof.
    intros T e. right. destruct e.
    { destruct a.
      - (* Assume P *)
        exact
        (if img
         then existT _ (subevent _ (Assume P), λ v, Ret v)
         else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
      - (* AssumeRes P *)
        exact (existT _ (subevent _ (AssumeRes r), λ v, Ret v)).
      - (* Guarantee P *)
        exact (existT _ (subevent _ (Guarantee P), λ v, Ret v)).
    }
    destruct s.
    { destruct c.
      - (* Call *)
        exact
        (if msk fn
         then existT _ (subevent _ (Call fn args), λ v, Ret v)
         else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
      - (* Spawn *)
        exact
        (if msk fn
         then existT _ (subevent _ (Spawn fn args), λ v, Ret v)
         else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
      - (* Yield *)
        exact (existT _ (subevent _ (Yield tid), λ v, Ret v)).
      - exact (existT _ (subevent _ GetTid, λ v, Ret v)).
    }
    destruct s.
    { destruct p.
      - (* Put *)
        exact
        (if existsb (String.eqb k.1) scp
         then existT _ (subevent _ (SPut k v), λ v, Ret v)
         else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
      - (* Get *)
        exact
        (if existsb (String.eqb k.1) scp
         then existT _ (subevent _ (SGet k), λ v, Ret v)
         else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
    }
    destruct c.
    - (* Choose *)
      exact (existT _ (subevent _ (Choose X), λ v, Ret v)).
    - (* Take *)
      exact
      (if img || excluded_middle_informative (∃ P: Prop, X = P)
       then existT _ (subevent _ (Take X), λ v, Ret v)
       else existT _ (subevent _ (Take False), λ v, Ret (False_rect _ v))).
    - (* IO *)
      exact (existT _ (subevent _ (@IO I O fn args), λ v, Ret v)).
  Defined. *)

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
    if msk X e
    then Vis e (λ x, SB.sandbox msk (k x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SB.sandbox interpV_vis /SB.handle ?subevent_subevent.
    case_match eqn : H; rewrite H /=.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind.
    ired.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind. 
  Qed.
(* 
  Lemma vis_choose msk {X R} (k : X → itree crisE R) :
    SB.sandbox msk (vis (Choose X) k) = vis (Choose X) (λ x, SB.sandbox msk (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_take X {R} msk (k : X → itree crisE R) :
    SB.sandbox msk (vis (Take X) k) =
      if img || excluded_middle_informative (∃ P: Prop, X = P)
      then vis (Take X) (λ x, SB.sandbox msk (k x))
      else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_take_img X {R} msk scp (k : X → itree crisE R) :
    SB.sandbox true msk scp (vis (Take X) k) =
      vis (Take X) (λ x, SB.sandbox true msk scp (k x)).
  Proof using.
    rewrite vis_take. et.
  Qed.

  Lemma vis_io {I O R} f arg msk (k : O → itree crisE R) :
    SB.sandbox msk (vis (@IO I O f arg) k) =
      vis (IO f arg) (λ x, SB.sandbox msk (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_Assume {R} P msk (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (Assume P) ktr) =
      if img
      then vis (Assume P) (λ x, SB.sandbox msk (ktr x))
      else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_Assume_img {R} P msk scp (ktr : () → itree crisE R) :
    SB.sandbox true msk scp (vis (Assume P) ktr) =
      vis (Assume P) (λ x, SB.sandbox true msk scp (ktr x)).
  Proof using.
    rewrite vis_Assume. et.
  Qed.

  Lemma vis_AssumeRes {R} P msk (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (AssumeRes P) ktr) =
      vis (AssumeRes P) (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_Guarantee {R} P msk (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (Guarantee P) ktr) =
      vis (Guarantee P) (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_yield {R} msk tid (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (Yield tid) ktr) = vis (Yield tid) (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_spawn {R} msk f a (ktr : nat → itree crisE R) :
    SB.sandbox msk (vis (Spawn f a) ktr) =
      if msk f
      then vis (Spawn f a) (λ x, SB.sandbox msk (ktr x))
      else vis (Take False) (λ x, Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_gettid {R} msk (ktr : nat → itree crisE R) :
    SB.sandbox msk (vis GetTid ktr) = vis GetTid (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_call {R} msk f a (ktr : Any.t → itree crisE R) :
    SB.sandbox msk (vis (Call f a) ktr) =
      if msk f
      then vis (Call f a) (λ x, SB.sandbox msk (ktr x))
      else vis (Take False) (λ x, Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_put {R} msk k v (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (SPut k v) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SPut k v) (λ x, SB.sandbox msk (ktr x))
      else vis (Take False) (λ x, Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_get {R} k msk (ktr : Any.t → itree crisE R) :
    SB.sandbox msk (vis (SGet k) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SGet k) (λ x, SB.sandbox msk (ktr x))
      else vis (Take False) (λ x, Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed. *)

  Definition putSB {R} msk k v (itr : itree crisE R) : itree crisE R :=
    SB.sandbox msk (trigger (SPut k v));;; itr.

  Definition getSB {R} msk k (ktr : Any.t → itree crisE R) : itree crisE R :=
    SB.sandbox msk (trigger (SGet k)) >>= ktr.

  (* Lemma SPut_putSB {R} msk k v (ktr : () → itree crisE R) :
    SB.sandbox msk (vis (SPut k v) ktr) = putSB msk k v (SB.sandbox msk (ktr tt)).
  Proof using.
    destruct k. unfold putSB, trigger. rewrite !vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities x. destruct x.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed. *)

  (* Lemma putSB_SPut {R} msk k v (itr : itree crisE R) :
    putSB msk k v itr = SB.sandbox msk (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed. *)

  (* Lemma putSB_bind {T U} msk k v (itr : itree crisE T) (ktr : T → itree crisE U) :
    putSB msk k v itr >>= ktr = putSB msk k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed. *)

  (* Lemma SGet_getSB {R} msk k (ktr : Any.t → itree crisE R) :
    SB.sandbox msk (vis (SGet k) ktr) = getSB msk k (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    destruct k. unfold getSB, trigger. rewrite !vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed. *)

  (* Lemma getSB_SGet {R} msk k (ktr : Any.t → itree crisE R) :
    getSB msk k ktr = x <- SB.sandbox msk (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed. *)

  (* Lemma getSB_bind {T U} msk k (ktr1 : Any.t → itree crisE T) (ktr2 : T → itree crisE U) :
    getSB msk k ktr1 >>= ktr2 = getSB msk k (λ x, ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed. *)

  (* Definition callSB {R} msk f a (ktr : Any.t → itree crisE R) : itree crisE R :=
    SB.sandbox msk (trigger (Call f a)) >>= ktr. *)

  (* Lemma Call_callSB {R} msk f a (ktr : Any.t → itree crisE R) :
    SB.sandbox msk (vis (Call f a) ktr) = callSB msk f a (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold callSB, trigger. rewrite !vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed. *)

  (* Lemma callSB_Call {R} msk f a (ktr : Any.t → itree crisE R) :
    callSB msk f a ktr = x <- SB.sandbox msk (trigger (Call f a));; ktr x.
  Proof using.
    reflexivity.
  Qed. *)

  (* Lemma callSB_bind {T U} msk f a (ktr1 : Any.t → itree crisE T) (ktr2 : T → itree crisE U) :
    callSB msk f a ktr1 >>= ktr2 = callSB msk f a (λ x, ktr1 x >>= ktr2).
  Proof using.
    unfold callSB. rewrite bind_bind. reflexivity.
  Qed. *)

  (* Definition spawnSB {R} msk f a (ktr : _ → itree crisE R) : itree crisE R :=
    SB.sandbox msk (trigger (Spawn f a)) >>= ktr. *)

  (* Lemma Spawn_spawnSB {R} msk f a (ktr : _ → itree crisE R) :
    SB.sandbox msk (vis (Spawn f a) ktr) = spawnSB msk f a (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    unfold spawnSB, trigger. rewrite !vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed. *)

  (* Lemma spawnSB_Spawn {R} msk f a (ktr : _ → itree crisE R) :
    spawnSB msk f a ktr = x <- SB.sandbox msk (trigger (Spawn f a));; ktr x.
  Proof using.
    reflexivity.
  Qed. *)

  (* Lemma spawnSB_bind {T U} msk f a (ktr1 : _ → itree crisE T) (ktr2 : T → itree crisE U) :
    spawnSB msk f a ktr1 >>= ktr2 = spawnSB msk f a (λ x, ktr1 x >>= ktr2).
  Proof using.
    unfold spawnSB. rewrite bind_bind. reflexivity.
  Qed. *)

  (* Lemma assumeK {R} msk P (itr : itree crisE R) :
    SB.sandbox msk (assumeK P itr) = assumeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0; cycle 1.
    { exfalso. destruct (excluded_middle_informative _); destruct img; ss; et. }
    s. f_equal. extensionalities. ired. eauto.
  Qed. *)

  (* Lemma guaranteeK {R} msk P (itr : itree crisE R) :
    SB.sandbox msk (guaranteeK P itr) = guaranteeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed. *)

  (* Lemma unwrapUK {X R} msk x (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapUK x ktr) = unwrapUK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0.
    - ss. f_equal. extensionality x. ss.
    - exfalso. destruct (excluded_middle_informative _); destruct img; ss; et.
  Qed. *)

  (* Lemma unwrapNK {X R} msk x (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapNK x ktr) = unwrapNK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed. *)

  (* Lemma call f a msk :
    SB.sandbox msk (trigger (Call f a)) =
      if msk f
      then trigger (Call f a)
      else triggerUB.
  Proof using.
    rewrite vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma put msk k v :
    SB.sandbox msk (trigger (SPut k v)) =
      if existsb (String.eqb k.1) scp
      then trigger (SPut k v)
      else triggerUB.
  Proof using.
    rewrite vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma get msk k :
    SB.sandbox msk (trigger (SGet k)) =
      if existsb (String.eqb k.1) scp
      then trigger (SGet k)
      else triggerUB.
  Proof using.
    rewrite vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma choose T msk :
    SB.sandbox msk (trigger (Choose T)) = trigger (Choose T).
  Proof using.
    rewrite vis_choose.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma take T msk :
    SB.sandbox msk (trigger (Take T)) =
      if img || excluded_middle_informative (∃ P: Prop, T = P)
      then trigger (Take T)
      else v <- trigger (Take False);; Ret (False_rect _ v).
  Proof using.
    rewrite vis_take. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma io I O f arg msk :
    SB.sandbox msk (trigger (@IO I O f arg)) = trigger (IO f arg).
  Proof using.
    rewrite vis_io.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma Assume P msk :
    SB.sandbox msk (trigger (Assume P)) =
      if img
      then trigger (Assume P)
      else v <- trigger (Take False);; Ret (False_rect _ v).
  Proof using.
    rewrite vis_Assume.
    des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma Assume_img (P: iProp Σ) msk scp :
    SB.sandbox true msk scp (trigger (Events.Assume P)) =
      trigger (Events.Assume P).
  Proof using.
    rewrite Assume. et.
  Qed.

  Lemma AssumeRes P msk :
    SB.sandbox msk (trigger (AssumeRes P)) = trigger (AssumeRes P).
  Proof using.
    rewrite vis_AssumeRes.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma Guarantee P msk :
    SB.sandbox msk (trigger (Guarantee P)) = trigger (Guarantee P).
  Proof using.
    rewrite vis_Guarantee.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma yield msk tid :
    SB.sandbox msk (trigger (Yield tid)) = trigger (Yield tid).
  Proof using.
    rewrite vis_yield.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma spawn f a msk :
    SB.sandbox msk (trigger (Spawn f a)) =
      if msk f
      then trigger (Spawn f a)
      else triggerUB.
  Proof using.
    rewrite vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma gettid msk :
    SB.sandbox msk (trigger GetTid) = trigger GetTid.
  Proof.
    rewrite vis_gettid.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma unwrapU R msk (r : option R) :
    SB.sandbox msk (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - rewrite bind take. des_ifs.
      + f_equal. extensionalities. ss.
      + ired. f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R msk (r : option R) :
    SB.sandbox msk (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - rewrite !bind !choose.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm msk P :
    SB.sandbox msk (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind take ret. des_ifs; et.
    exfalso. destruct img; ss. destruct (excluded_middle_informative _); ss; et.
  Qed.

  Lemma guar msk P :
    SB.sandbox msk (guarantee P) = guarantee P.
  Proof using.
    unfold guarantee. rewrite bind choose ret. eauto.
  Qed.

  Lemma ru {X} (pre post: X → _) msk :
    SB.sandbox msk (RealUpdate pre post) = RealUpdate pre post.
  Proof.
    rewrite /RealUpdate. unseal CRIS_FancyReal.
    repeat (rewrite bind choose; f_equal; extensionalities).
    repeat (rewrite bind Guarantee; f_equal; extensionalities).
    repeat (rewrite AssumeRes; f_equal; extensionalities).
  Qed.

  Lemma ruK {X R} (pre post : X → _) (k : _ → itree crisE R) msk :
    SB.sandbox msk (RealUpdateK pre post k) =
    RealUpdateK pre post (λ x, SB.sandbox msk (k x)).
  Proof using. rewrite /RealUpdateK bind ru //. Qed. *)
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
    { rewrite Hmsk in Hmsk2; ss. }
    rewrite !bind_vis. gstep. econs. intros x.
    rewrite !SBRed.ret; ired.
    gbase. eapply CIH. auto.
  Qed.
End Properties.

Notation "░ it" := (SB.sandbox _ it) (at level 60, only printing).

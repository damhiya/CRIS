Require Import FSpec.
Require Import Common.

Set Implicit Arguments.

Definition fnsem_type `{Σ:GRA} T : Type :=
  bool *               (* imaginary or real spec *)  
  (string -> bool) *   (* mask *)
  (list string) *      (* scope *)
  T.                   (* function semantics *)

Section WMask.

  Definition wmask_all : string->bool := fun _ => true.

  Definition wmask_none : string->bool := fun _ => false.
  
  Definition wmask_list (fns: list string) : string->bool :=
    fun f => (existsb (String.eqb f) fns).

  Definition wmask_or (msk1 msk2: string->bool) :=
    fun fn => msk1 fn || msk2 fn.

  Definition wmask_and (msk1 msk2: string->bool) :=
    fun fn => msk1 fn && msk2 fn.

  Definition wmask_sub (msk1 msk2: string→bool) :=
    ∀ fn, msk1 fn → msk2 fn.

End WMask.

Module SB. Section SB.
  Context `{Σ: GRA}.
  
  (**** Sandboxing ****)
  Definition handle_sandbox (img: bool) (msk: string->bool) (scp: list string)
    : ∀ T, crisE T -> (itree crisE T + {X: Type & crisE X * (X -> itree crisE T)})%type.
  Proof.
    intros T e. right. destruct e.
    { destruct a.
      - (* Assume P *)
        exact
        (if img
         then existT _ (subevent _ (Assume P), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
      - (* AssumeRes P *)
        exact (existT _ (subevent _ (AssumeRes r), fun v => Ret v)).
      - (* Guarantee P *)
        exact (existT _ (subevent _ (Guarantee P), fun v => Ret v)).
    }
    destruct s.
    { destruct c.
      - (* Call *)
        exact
        (if msk fn
         then existT _ (subevent _ (Call fn args), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
      - (* Spawn *)
        exact
        (if msk fn
         then existT _ (subevent _ (Spawn fn args), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
      - (* Yield *)
        exact (existT _ (subevent _ (Yield tid), fun v => Ret v)).
    }
    destruct s.
    { destruct p.
      - (* Put *)
        exact
        (if existsb (String.eqb k.1) scp
         then existT _ (subevent _ (SPut k v), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
      - (* Get *)
        exact
        (if existsb (String.eqb k.1) scp
         then existT _ (subevent _ (SGet k), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
    }
    destruct c.
    - (* Choose *)
      exact (existT _ (subevent _ (Choose X), fun v => Ret v)).
    - (* Take *)
      exact
      (if img || excluded_middle_informative (∃ P: Prop, X = P)
       then existT _ (subevent _ (Take X), fun v => Ret v)
       else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
    - (* IO *)
      exact (existT _ (subevent _ (@IO I O fn args), fun v => Ret v)).
  Defined.

  Definition sandbox {T} img msk scp (itr : itree crisE T) :=
    interpV (handle_sandbox img msk scp) itr.

  Definition sandbox_body (kb : fnsem_type fbody) :=
    λ arg, sandbox kb.1.1.1 kb.1.1.2 kb.1.2 (kb.2 arg).

End SB. End SB.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind A B img msk scp (itr : itree crisE A) (ktr : A → itree crisE B) :
    SB.sandbox img msk scp (itr >>= ktr)
    = a <- (SB.sandbox img msk scp itr);; (SB.sandbox img msk scp (ktr a)).
  Proof using. unfold SB.sandbox. rewrite interpV_bind; eauto. Qed.

  Lemma tau A img msk scp (itr : itree crisE A) :
    SB.sandbox img msk scp (tau;; itr) = tau;; (SB.sandbox img msk scp itr).
  Proof using. unfold SB.sandbox. rewrite interpV_tau; eauto. Qed.

  Lemma ret A (a : A) img msk scp :
    SB.sandbox img msk scp (Ret a) = Ret a.
  Proof using. unfold SB.sandbox. rewrite interpV_ret; eauto. Qed.

  Lemma vis_choose X {R} img msk scp (k : X -> itree crisE R) :
    SB.sandbox img msk scp (vis (Choose X) k) = vis (Choose X) (fun x => SB.sandbox img msk scp (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_take X {R} img msk scp (k : X -> itree crisE R) :
    SB.sandbox img msk scp (vis (Take X) k) =
      if img || excluded_middle_informative (∃ P: Prop, X = P)
      then vis (Take X) (fun x => SB.sandbox img msk scp (k x))
      else vis (Take False) (fun v => Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_take_img X {R} msk scp (k : X -> itree crisE R) :
    SB.sandbox true msk scp (vis (Take X) k) =
      vis (Take X) (fun x => SB.sandbox true msk scp (k x)).
  Proof using.
    rewrite vis_take. et.
  Qed.

  Lemma vis_io {I O R} f arg img msk scp (k : O -> itree crisE R) :
    SB.sandbox img msk scp (vis (@IO I O f arg) k) =
      vis (IO f arg) (fun x => SB.sandbox img msk scp (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_Assume {R} P img msk scp (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (Assume P) ktr) =
      if img
      then vis (Assume P) (fun x => SB.sandbox img msk scp (ktr x))
      else vis (Take False) (fun v => Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_Assume_img {R} P msk scp (ktr : () -> itree crisE R) :
    SB.sandbox true msk scp (vis (Assume P) ktr) =
      vis (Assume P) (fun x => SB.sandbox true msk scp (ktr x)).
  Proof using.
    rewrite vis_Assume. et.
  Qed.
  
  Lemma vis_AssumeRes {R} P img msk scp (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (AssumeRes P) ktr) =
      vis (AssumeRes P) (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
  
  Lemma vis_Guarantee {R} P img msk scp (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (Guarantee P) ktr) =
      vis (Guarantee P) (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
  
  Lemma vis_yield {R} img msk scp tid (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (Yield tid) ktr) = vis (Yield tid) (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
               
  Lemma vis_spawn {R} img msk scp f a (ktr : nat -> itree crisE R) :
    SB.sandbox img msk scp (vis (Spawn f a) ktr) =
      if msk f
      then vis (Spawn f a) (fun x => SB.sandbox img msk scp (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_call {R} img msk scp f a (ktr : Any.t -> itree crisE R) :
    SB.sandbox img msk scp (vis (Call f a) ktr) =
      if msk f
      then vis (Call f a) (fun x => SB.sandbox img msk scp (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_put {R} img msk scp k v (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (SPut k v) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SPut k v) (fun x => SB.sandbox img msk scp (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_get {R} k img msk scp (ktr : Any.t -> itree crisE R) :
    SB.sandbox img msk scp (vis (SGet k) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SGet k) (fun x => SB.sandbox img msk scp (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Definition putSB {R} img msk scp k v (itr : itree crisE R) : itree crisE R :=
    SB.sandbox img msk scp (trigger (SPut k v));;; itr.

  Definition getSB {R} img msk scp k (ktr : Any.t -> itree crisE R) : itree crisE R :=
    SB.sandbox img msk scp (trigger (SGet k)) >>= ktr.

  Lemma SPut_putSB {R} img msk scp k v (ktr : () -> itree crisE R) :
    SB.sandbox img msk scp (vis (SPut k v) ktr) = putSB img msk scp k v (SB.sandbox img msk scp (ktr tt)).
  Proof using.
    destruct k. unfold putSB, trigger. rewrite !vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities x. destruct x.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma putSB_SPut {R} img msk scp k v (itr : itree crisE R) :
    putSB img msk scp k v itr = SB.sandbox img msk scp (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed.

  Lemma putSB_bind {T U} img msk scp k v (itr : itree crisE T) (ktr : T -> itree crisE U) :
    putSB img msk scp k v itr >>= ktr = putSB img msk scp k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma SGet_getSB {R} img msk scp k (ktr : Any.t -> itree crisE R) :
    SB.sandbox img msk scp (vis (SGet k) ktr) = getSB img msk scp k (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    destruct k. unfold getSB, trigger. rewrite !vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma getSB_SGet {R} img msk scp k (ktr : Any.t -> itree crisE R) :
    getSB img msk scp k ktr = x <- SB.sandbox img msk scp (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma getSB_bind {T U} img msk scp k (ktr1 : Any.t -> itree crisE T) (ktr2 : T -> itree crisE U) :
    getSB img msk scp k ktr1 >>= ktr2 = getSB img msk scp k (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition callSB {R} img msk scp f a (ktr : Any.t -> itree crisE R) : itree crisE R :=
    SB.sandbox img msk scp (trigger (Call f a)) >>= ktr.

  Lemma Call_callSB {R} img msk scp f a (ktr : Any.t -> itree crisE R) :
    SB.sandbox img msk scp (vis (Call f a) ktr) = callSB img msk scp f a (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    unfold callSB, trigger. rewrite !vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma callSB_Call {R} img msk scp f a (ktr : Any.t -> itree crisE R) :
    callSB img msk scp f a ktr = x <- SB.sandbox img msk scp (trigger (Call f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma callSB_bind {T U} img msk scp f a (ktr1 : Any.t -> itree crisE T) (ktr2 : T -> itree crisE U) :
    callSB img msk scp f a ktr1 >>= ktr2 = callSB img msk scp f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold callSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition spawnSB {R} img msk scp f a (ktr : _ -> itree crisE R) : itree crisE R :=
    SB.sandbox img msk scp (trigger (Spawn f a)) >>= ktr.

  Lemma Spawn_spawnSB {R} img msk scp f a (ktr : _ -> itree crisE R) :
    SB.sandbox img msk scp (vis (Spawn f a) ktr) = spawnSB img msk scp f a (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    unfold spawnSB, trigger. rewrite !vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma spawnSB_Spawn {R} img msk scp f a (ktr : _ -> itree crisE R) :
    spawnSB img msk scp f a ktr = x <- SB.sandbox img msk scp (trigger (Spawn f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma spawnSB_bind {T U} img msk scp f a (ktr1 : _ -> itree crisE T) (ktr2 : T -> itree crisE U) :
    spawnSB img msk scp f a ktr1 >>= ktr2 = spawnSB img msk scp f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold spawnSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma assumeK {R} img msk scp P (itr : itree crisE R) :
    SB.sandbox img msk scp (assumeK P itr) = assumeK P (SB.sandbox img msk scp itr).
  Proof using.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0; cycle 1.
    { exfalso. destruct (excluded_middle_informative _); destruct img; ss; et. }
    s. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma guaranteeK {R} img msk scp P (itr : itree crisE R) :
    SB.sandbox img msk scp (guaranteeK P itr) = guaranteeK P (SB.sandbox img msk scp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma unwrapUK {X R} img msk scp x (ktr : X -> itree crisE R) :
    SB.sandbox img msk scp (unwrapUK x ktr) = unwrapUK x (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0.
    - ss. f_equal. extensionality x. ss.
    - exfalso. destruct (excluded_middle_informative _); destruct img; ss; et.
  Qed.

  Lemma unwrapNK {X R} img msk scp x (ktr : X -> itree crisE R) :
    SB.sandbox img msk scp (unwrapNK x ktr) = unwrapNK x (fun x => SB.sandbox img msk scp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call f a img msk scp :
    SB.sandbox img msk scp (trigger (Call f a)) =
      if msk f
      then trigger (Call f a)
      else triggerUB.
  Proof using.
    rewrite vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma put img msk scp k v :
    SB.sandbox img msk scp (trigger (SPut k v)) =
      if existsb (String.eqb k.1) scp
      then trigger (SPut k v)
      else triggerUB.
  Proof using.
    rewrite vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma get img msk scp k :
    SB.sandbox img msk scp (trigger (SGet k)) =
      if existsb (String.eqb k.1) scp
      then trigger (SGet k)
      else triggerUB.
  Proof using.
    rewrite vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma choose T img msk scp :
    SB.sandbox img msk scp (trigger (Choose T)) = trigger (Choose T).
  Proof using.
    rewrite vis_choose.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma take T img msk scp :
    SB.sandbox img msk scp (trigger (Take T)) =
      if img || excluded_middle_informative (∃ P: Prop, T = P)
      then trigger (Take T)
      else v <- trigger (Take False);; Ret (False_rect _ v).
  Proof using.
    rewrite vis_take. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma io I O f arg img msk scp :
    SB.sandbox img msk scp (trigger (@IO I O f arg)) = trigger (IO f arg).
  Proof using.
    rewrite vis_io.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma Assume P img msk scp :
    SB.sandbox img msk scp (trigger (Assume P)) =
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
  
  Lemma AssumeRes P img msk scp :
    SB.sandbox img msk scp (trigger (AssumeRes P)) = trigger (AssumeRes P).
  Proof using.
    rewrite vis_AssumeRes.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma Guarantee P img msk scp :
    SB.sandbox img msk scp (trigger (Guarantee P)) = trigger (Guarantee P).
  Proof using.
    rewrite vis_Guarantee.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma yield img msk scp tid:
    SB.sandbox img msk scp (trigger (Yield tid)) = trigger (Yield tid).
  Proof using.
    rewrite vis_yield.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma spawn f a img msk scp :
    SB.sandbox img msk scp (trigger (Spawn f a)) =
      if msk f
      then trigger (Spawn f a)
      else triggerUB.
  Proof using.
    rewrite vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.
  
  Lemma unwrapU R img msk scp (r : option R) :
    SB.sandbox img msk scp (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - rewrite bind take. des_ifs.
      + f_equal. extensionalities. ss.
      + ired. f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R img msk scp (r : option R) :
    SB.sandbox img msk scp (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - rewrite !bind !choose.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm img msk scp P :
    SB.sandbox img msk scp (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind take ret. des_ifs; et.
    exfalso. destruct img; ss. destruct (excluded_middle_informative _); ss; et.
  Qed.

  Lemma guar img msk scp P :
    SB.sandbox img msk scp (guarantee P) = guarantee P.
  Proof using.
    unfold guarantee. rewrite bind choose ret. eauto.
  Qed.

  Lemma update_proph {X A R} pre (post : X → R → iProp Σ) (arg : A) img msk scp :
    SB.sandbox img msk scp (UpdateProph pre post arg) = UpdateProph pre post arg.
  Proof.
    rewrite /UpdateProph. unseal CRIS_PROPH.
    repeat (rewrite bind choose; f_equal; extensionalities).
    repeat (rewrite bind Guarantee; f_equal; extensionalities).
    repeat (rewrite bind AssumeRes; f_equal; extensionalities).
    repeat (rewrite bind Guarantee; f_equal; extensionalities).
    rewrite ret //.
  Qed.

  Lemma update_prophK
      {X A R R2} pre (post : X → R → iProp Σ) (arg : A) (k : _ → itree crisE R2) img msk scp :
    SB.sandbox img msk scp (UpdateProphK pre post arg k) =
    UpdateProphK pre post arg (λ x, SB.sandbox img msk scp (k x)).
  Proof using. rewrite /UpdateProphK bind update_proph //. Qed.
End SBRed. End SBRed.

Section Properties.

  Context `{Σ: GRA}.

  Lemma sandbox_sandbox {R} (t: itree crisE R) (img img': bool) (msk msk' : _ → bool) scp scp'
      (IMPL: img → img')
      (SUB: wmask_sub msk msk')
      (INCL: incl scp scp') :
    SB.sandbox img' msk' scp' (SB.sandbox img msk scp t) = SB.sandbox img msk scp t.
  Proof using.
    eapply bisim_is_eq.
    eapply gpaco2_init with (clo:=eqitC _ _ _); eauto with paco.
    revert R t scp scp' INCL. gcofix CIH. i.
    rewrite (bisim_is_eq (itree_eta t)). destruct (observe t).
    { rewrite !SBRed.ret. eapply Reflexive_eqit_gen. et. }
    { rewrite !SBRed.tau. gstep. econs. gbase. et. }

    rewrite -bind_trigger !SBRed.bind.
    destruct e; [ |destruct s;
                   [destruct c|destruct s; [destruct p|]]].
    + destruct a.
      * rewrite !SBRed.Assume. des_ifs.
        { specialize (IMPL eq_refl). destruct img'; ss.
          gstep. rewrite SBRed.Assume !bind_trigger. econs. i. gbase. et. }
        { gstep. rewrite SBRed.bind SBRed.take.
          des_ifs; ired; rr; s; econs; ss. }
      * rewrite !SBRed.AssumeRes.
        gstep. rewrite !bind_trigger. econs. i. gbase. et.
      * rewrite !SBRed.Guarantee.
        gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.call. des_ifs; cycle 1.
      { rewrite /triggerUB SBRed.unwrapU. s. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.call. des_ifs; cycle 1.
      { eapply SUB in Heq. rewrite Heq0 in Heq. ss. }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.spawn. des_ifs; cycle 1.
      { rewrite /triggerUB SBRed.unwrapU. s. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.spawn. des_ifs; cycle 1.
      { eapply SUB in Heq. rewrite Heq0 in Heq. ss. }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.yield.
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.put. des_ifs; cycle 1.
      { rewrite /triggerUB SBRed.unwrapU. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.put. des_ifs; cycle 1.
      { exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        apply INCL in Heq.
        hexploit (proj2 (existsb_exists (String.eqb k0.1) scp')).
        { esplits; et. apply String.eqb_eq. et. }
        i. rewrite H in Heq0. ss.
      }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + rewrite !SBRed.get. des_ifs; cycle 1.
      { rewrite /triggerUB SBRed.unwrapU. ired.
        gstep. rewrite !bind_trigger. econs. ss. }
      rewrite !SBRed.get. des_ifs; cycle 1.
      { exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        apply INCL in Heq.
        hexploit (proj2 (existsb_exists (String.eqb k0.1) scp')).
        { esplits; et. apply String.eqb_eq. et. }
        i. rewrite H in Heq0. ss.
      }
      gstep. rewrite !bind_trigger. econs. i. gbase. et.
    + destruct c.
      * rewrite !SBRed.choose.
        gstep. rewrite !bind_trigger. econs. i. gbase. et.
      * rewrite !SBRed.take. des_ifs; cycle 1.
        { destruct img'.
          - rewrite SBRed.bind SBRed.take. ired.
            gstep. rewrite !bind_trigger. econs. i. ss.
          - rewrite SBRed.bind SBRed.take. ired. des_ifs; ired.
            + gstep. rewrite !bind_trigger. econs. i. ss.
            + gstep. rewrite !bind_trigger. econs. i. ss.
        }
        { rewrite SBRed.take. destruct img; ss.
          - destruct img'; ss; cycle 1.
            { specialize (IMPL eq_refl). inv IMPL. }
            gstep. rewrite !bind_trigger. econs. i. gbase. et.
          - rewrite Heq orb_true_r.
            gstep. rewrite !bind_trigger. econs. i. gbase. et.
        }
      * rewrite !SBRed.io.
        gstep. rewrite !bind_trigger. econs. i. gbase. et.
  Qed.
End Properties.

Notation "░ it" := (SB.sandbox _ _ _ it) (at level 60, only printing).

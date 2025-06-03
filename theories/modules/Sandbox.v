Require Import Common.
Require Import FSpec Mod.

Set Implicit Arguments.

Definition fnsem_type `{Σ:GRA} (T: Type) : Type :=
  ((string -> bool) *   (* mask *)
   (list string) *      (* scope *)
   (T *                 (* imaginary or real spec *)
    fbody))%type.       (* function semantics *)

Section WMask.

  Definition wmask_all : string->bool := fun _ => true.

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
  Definition handle_sandbox (msk: string->bool) (scp: list string) (img: bool)
    : ∀ T, hmodE T -> (itree hmodE T + {X: Type & hmodE X * (X -> itree hmodE T)})%type.
  Proof.
    intros T e. right. destruct e.
    { destruct a.
      - (* Assume P *)
        exact
        (if img
         then existT _ (subevent _ (Assume P), fun v => Ret v)
         else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))).
      - (* AssumePrecise P *)
        exact (existT _ (subevent _ (AssumePrecise P), fun v => Ret v)).
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

  Definition sandbox {T} msk scp img (itr : itree hmodE T) :=
    interpV (handle_sandbox msk scp img) itr.

  Definition sandbox_body (kb : fnsem_type bool) :=
    λ arg, sandbox kb.1.1 kb.1.2 kb.2.1 (kb.2.2 arg).

End SB. End SB.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind A B msk scp img (itr : itree hmodE A) (ktr : A → itree hmodE B) :
    SB.sandbox msk scp img (itr >>= ktr)
    = a <- (SB.sandbox msk scp img itr);; (SB.sandbox msk scp img (ktr a)).
  Proof using. unfold SB.sandbox. rewrite interpV_bind; eauto. Qed.

  Lemma tau A msk scp img (itr : itree hmodE A) :
    SB.sandbox msk scp img (tau;; itr) = tau;; (SB.sandbox msk scp img itr).
  Proof using. unfold SB.sandbox. rewrite interpV_tau; eauto. Qed.

  Lemma ret A (a : A) msk scp img :
    SB.sandbox msk scp img (Ret a) = Ret a.
  Proof using. unfold SB.sandbox. rewrite interpV_ret; eauto. Qed.

  Lemma vis_choose X {R} msk scp img (k : X -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Choose X) k) = vis (Choose X) (fun x => SB.sandbox msk scp img (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_take X {R} msk scp img (k : X -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Take X) k) =
      if img || excluded_middle_informative (∃ P: Prop, X = P)
      then vis (Take X) (fun x => SB.sandbox msk scp img (k x))
      else vis (Take False) (fun v => Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_take_img X {R} mask scopes (k : X -> itree hmodE R) :
    SB.sandbox mask scopes true (vis (Take X) k) =
      vis (Take X) (fun x => SB.sandbox mask scopes true (k x)).
  Proof using.
    rewrite vis_take. et.
  Qed.
  
  Lemma vis_io {I O R} f arg msk scp img (k : O -> itree hmodE R) :
    SB.sandbox msk scp img (vis (@IO I O f arg) k) =
      vis (IO f arg) (fun x => SB.sandbox msk scp img (k x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma vis_Assume {R} P msk scp img (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Assume P) ktr) =
      if img
      then vis (Assume P) (fun x => SB.sandbox msk scp img (ktr x))
      else vis (Take False) (fun v => Ret (False_rect _ v)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ired. et.
    - depdes H0. depdes H1. ired.
      eapply observe_eta. s. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_Assume_img {R} P mask scopes (ktr : () -> itree hmodE R) :
    SB.sandbox mask scopes true (vis (Assume P) ktr) =
      vis (Assume P) (fun x => SB.sandbox mask scopes true (ktr x)).
  Proof using.
    rewrite vis_Assume. et.
  Qed.
  
  Lemma vis_AssumePrecise {R} P msk scp img (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (AssumePrecise P) ktr) =
      vis (AssumePrecise P) (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
  
  Lemma vis_Guarantee {R} P msk scp img (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Guarantee P) ktr) =
      vis (Guarantee P) (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
  
  Lemma vis_yield {R} msk scp img tid (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Yield tid) ktr) = vis (Yield tid) (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis.
    eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
  Qed.
               
  Lemma vis_spawn {R} msk scp img f a (ktr : nat -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Spawn f a) ktr) =
      if msk f
      then vis (Spawn f a) (fun x => SB.sandbox msk scp img (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_call {R} msk scp img f a (ktr : Any.t -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Call f a) ktr) =
      if msk f
      then vis (Call f a) (fun x => SB.sandbox msk scp img (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_put {R} msk scp img k v (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (SPut k v) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SPut k v) (fun x => SB.sandbox msk scp img (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Lemma vis_get {R} k msk scp img (ktr : Any.t -> itree hmodE R) :
    SB.sandbox msk scp img (vis (SGet k) ktr) =
      if existsb (String.eqb k.1) scp
      then vis (SGet k) (fun x => SB.sandbox msk scp img (ktr x))
      else vis (Take False) (fun x => Ret (False_rect _ x)).
  Proof using.
    destruct k.
    unfold SB.sandbox. rewrite interpV_vis. s. des_ifs; depdes H0.
    - eapply observe_eta. ss. f_equal. extensionalities. ired. eauto.
    - eapply observe_eta. ss. f_equal. extensionalities. ss.
  Qed.

  Definition putSB {R} msk scp img k v (itr : itree hmodE R) : itree hmodE R :=
    SB.sandbox msk scp img (trigger (SPut k v));;; itr.

  Definition getSB {R} msk scp img k (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    SB.sandbox msk scp img (trigger (SGet k)) >>= ktr.

  Lemma SPut_putSB {R} msk scp img k v (ktr : () -> itree hmodE R) :
    SB.sandbox msk scp img (vis (SPut k v) ktr) = putSB msk scp img k v (SB.sandbox msk scp img (ktr tt)).
  Proof using.
    destruct k. unfold putSB, trigger. rewrite !vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities x. destruct x.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma putSB_SPut {R} msk scp img k v (itr : itree hmodE R) :
    putSB msk scp img k v itr = SB.sandbox msk scp img (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed.

  Lemma putSB_bind {T U} msk scp img k v (itr : itree hmodE T) (ktr : T -> itree hmodE U) :
    putSB msk scp img k v itr >>= ktr = putSB msk scp img k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma SGet_getSB {R} msk scp img k (ktr : Any.t -> itree hmodE R) :
    SB.sandbox msk scp img (vis (SGet k) ktr) = getSB msk scp img k (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    destruct k. unfold getSB, trigger. rewrite !vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma getSB_SGet {R} msk scp img k (ktr : Any.t -> itree hmodE R) :
    getSB msk scp img k ktr = x <- SB.sandbox msk scp img (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma getSB_bind {T U} msk scp img k (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    getSB msk scp img k ktr1 >>= ktr2 = getSB msk scp img k (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition callSB {R} msk scp img f a (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    SB.sandbox msk scp img (trigger (Call f a)) >>= ktr.

  Lemma Call_callSB {R} msk scp img f a (ktr : Any.t -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Call f a) ktr) = callSB msk scp img f a (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    unfold callSB, trigger. rewrite !vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma callSB_Call {R} msk scp img f a (ktr : Any.t -> itree hmodE R) :
    callSB msk scp img f a ktr = x <- SB.sandbox msk scp img (trigger (Call f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma callSB_bind {T U} msk scp img f a (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    callSB msk scp img f a ktr1 >>= ktr2 = callSB msk scp img f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold callSB. rewrite bind_bind. reflexivity.
  Qed.

  Definition spawnSB {R} msk scp img f a (ktr : _ -> itree hmodE R) : itree hmodE R :=
    SB.sandbox msk scp img (trigger (Spawn f a)) >>= ktr.

  Lemma Spawn_spawnSB {R} msk scp img f a (ktr : _ -> itree hmodE R) :
    SB.sandbox msk scp img (vis (Spawn f a) ktr) = spawnSB msk scp img f a (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    unfold spawnSB, trigger. rewrite !vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities.
      rewrite ret. ired. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma spawnSB_Spawn {R} msk scp img f a (ktr : _ -> itree hmodE R) :
    spawnSB msk scp img f a ktr = x <- SB.sandbox msk scp img (trigger (Spawn f a));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma spawnSB_bind {T U} msk scp img f a (ktr1 : _ -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    spawnSB msk scp img f a ktr1 >>= ktr2 = spawnSB msk scp img f a (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold spawnSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma assumeK {R} msk scp img P (itr : itree hmodE R) :
    SB.sandbox msk scp img (assumeK P itr) = assumeK P (SB.sandbox msk scp img itr).
  Proof using.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0; cycle 1.
    { exfalso. destruct (excluded_middle_informative _); destruct img; ss; et. }
    s. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma guaranteeK {R} msk scp img P (itr : itree hmodE R) :
    SB.sandbox msk scp img (guaranteeK P itr) = guaranteeK P (SB.sandbox msk scp img itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionalities. ired. eauto.
  Qed.

  Lemma unwrapUK {X R} msk scp img x (ktr : X -> itree hmodE R) :
    SB.sandbox msk scp img (unwrapUK x ktr) = unwrapUK x (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. des_ifs; depdes H1; depdes H0.
    - ss. f_equal. extensionality x. ss.
    - exfalso. destruct (excluded_middle_informative _); destruct img; ss; et.
  Qed.

  Lemma unwrapNK {X R} msk scp img x (ktr : X -> itree hmodE R) :
    SB.sandbox msk scp img (unwrapNK x ktr) = unwrapNK x (fun x => SB.sandbox msk scp img (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call f a msk scp img :
    SB.sandbox msk scp img (trigger (Call f a)) =
      if msk f
      then trigger (Call f a)
      else triggerUB.
  Proof using.
    rewrite vis_call. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma put msk scp img k v :
    SB.sandbox msk scp img (trigger (SPut k v)) =
      if existsb (String.eqb k.1) scp
      then trigger (SPut k v)
      else triggerUB.
  Proof using.
    rewrite vis_put. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma get msk scp img k :
    SB.sandbox msk scp img (trigger (SGet k)) =
      if existsb (String.eqb k.1) scp
      then trigger (SGet k)
      else triggerUB.
  Proof using.
    rewrite vis_get. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma choose T msk scp img :
    SB.sandbox msk scp img (trigger (Choose T)) = trigger (Choose T).
  Proof using.
    rewrite vis_choose.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma take T msk scp img :
    SB.sandbox msk scp img (trigger (Take T)) =
      if img || excluded_middle_informative (∃ P: Prop, T = P)
      then trigger (Take T)
      else v <- trigger (Take False);; Ret (False_rect _ v).
  Proof using.
    rewrite vis_take. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma io I O f arg msk scp img :
    SB.sandbox msk scp img (trigger (@IO I O f arg)) = trigger (IO f arg).
  Proof using.
    rewrite vis_io.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma Assume P msk scp img :
    SB.sandbox msk scp img (trigger (Assume P)) =
      if img
      then trigger (Assume P)
      else v <- trigger (Take False);; Ret (False_rect _ v).
  Proof using.
    rewrite vis_Assume.
    des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.

  Lemma Assume_img (P: iProp Σ) mask scopes :
    SB.sandbox mask scopes true (trigger (Events.Assume P)) =
      trigger (Events.Assume P).
  Proof using.
    rewrite Assume. et.
  Qed.
  
  Lemma AssumePrecise P msk scp img :
    SB.sandbox msk scp img (trigger (AssumePrecise P)) = trigger (AssumePrecise P).
  Proof using.
    rewrite vis_AssumePrecise.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma Guarantee P msk scp img :
    SB.sandbox msk scp img (trigger (Guarantee P)) = trigger (Guarantee P).
  Proof using.
    rewrite vis_Guarantee.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.
  
  Lemma yield msk scp img tid:
    SB.sandbox msk scp img (trigger (Yield tid)) = trigger (Yield tid).
  Proof using.
    rewrite vis_yield.
    eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
  Qed.

  Lemma spawn f a msk scp img :
    SB.sandbox msk scp img (trigger (Spawn f a)) =
      if msk f
      then trigger (Spawn f a)
      else triggerUB.
  Proof using.
    rewrite vis_spawn. des_ifs.
    - eapply observe_eta; ss. f_equal. extensionalities. rewrite ret. eauto.
    - eapply observe_eta; ss. f_equal. extensionalities. ss.
  Qed.
  
  Lemma unwrapU R msk scp img (r : option R) :
    SB.sandbox msk scp img (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - rewrite bind take. des_ifs.
      + f_equal. extensionalities. ss.
      + ired. f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R msk scp img (r : option R) :
    SB.sandbox msk scp img (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - rewrite !bind !choose.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm msk scp img P :
    SB.sandbox msk scp img (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind take ret. des_ifs; et.
    exfalso. destruct img; ss. destruct (excluded_middle_informative _); ss; et.
  Qed.

  Lemma guar msk scp img P :
    SB.sandbox msk scp img (guarantee P) = guarantee P.
  Proof using.
    unfold guarantee. rewrite bind choose ret. eauto.
  Qed.

  Lemma assume_proph {X R} Pre Post msk scp img:
    SB.sandbox msk scp img (@AssumeProph _ X R Pre Post) = AssumeProph Pre Post.
  Proof.
    rewrite /AssumeProph. unseal CRIS_PROPH.
    repeat (rewrite bind choose; f_equal; extensionalities).
    repeat (rewrite bind Guarantee; f_equal; extensionalities).
    repeat (rewrite bind AssumePrecise; f_equal; extensionalities).
    rewrite ret. et.
  Qed.

  Lemma assume_prophK {X S R} msk scp img Pre Post k :
    SB.sandbox msk scp img (@AssumeProphK _ X S R Pre Post k)
    = AssumeProphK Pre Post (fun x => SB.sandbox msk scp img (k x)).
  Proof using.
    rewrite /AssumeProphK. rewrite bind assume_proph. et.
  Qed.

End SBRed. End SBRed.

Section Properties.

  Context `{Σ: GRA}.

  Lemma sandbox_sandbox {R} (t: itree hmodE R) (img img': bool) (msk msk':_→bool) scp scp'
    (IMPL: img → img')
    (INCL: incl scp scp')
    (SUB: wmask_sub msk msk')
    :
    SB.sandbox msk' scp' img' (SB.sandbox msk scp img t) = SB.sandbox msk scp img t.
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
      * rewrite !SBRed.AssumePrecise.
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

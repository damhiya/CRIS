Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import HMod FSpec.
Require Import ISim MainAdequacy.

Set Implicit Arguments.

(* Inlining every function call in HMod. *)
Section INTERP.
  Context `{Σ: GRA}.

  Definition handle_callE (prog: string -> fbody) (itr: itree hmodE Any.t)
    : itree hmodE (itree hmodE Any.t + Any.t)
    :=
    match observe itr with
    | RetF r => Ret (inr r)
    | TauF itr' => tau;; Ret (inl itr')
    | VisF (inr1 (inl1 c)) k =>
        match c in (callE T) return ((T → _) → _)
        with
        | Call fn args =>
            λ k, Ret (inl (x <- prog fn args;; (tau;; k x)))
        | Spawn fn args =>
            λ k, v <- trigger (Spawn fn args);; Ret (inl (k v))
        | Yield tid =>
            λ k, v <- trigger (Yield tid);; Ret (inl (k v))
        end k
    | VisF e k =>
        v <- trigger e;; Ret (inl (k v))
    end.

  Definition sandboxed_prog (ms: HMod.t) fn (arg: Any.t) : itree hmodE Any.t :=
    kb <- (alist_find fn ms.(HMod.fnsems))?;;
    SB.sandbox_body kb arg.

  Definition inline_hp prog := ITree.iter (handle_callE prog).
  
  Definition inline_hfun prog (body: fbody) : fbody :=
    inline_hp prog ∘ body.

  Definition inline_fsem ms kb : fnsem_type bool :=
    (wmask_all, ms.(HMod.scopes), (true, inline_hfun (sandboxed_prog ms) (SB.sandbox_body kb))).
      
End INTERP.

Module HModInline.
  Import HMod.

  Program Definition inline `{Σ: GRA} (ms: HMod.t): HMod.t := {|
    scopes := ms.(scopes);
    fnsems := List.map (map_snd (inline_fsem ms)) (ms.(fnsems));
    initial_code := o2map (inline_fsem ms) ms.(initial_code);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. depdes ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite! alist_find_map in H. unfold o_map in H.
    des_ifs; ss. 
  Qed.
  Next Obligation.
    i. destruct (initial_code ms); ss. destruct o; ss.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
End HModInline.

Module HIRed.

  Lemma ret `{Σ: GRA}
    prog (x: Any.t)
  :
    inline_hp prog (Ret x) = Ret x.
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma tau `{Σ: GRA}
    prog t
  :
    inline_hp prog (tau;; t) = tau;; tau;; inline_hp prog t.
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind `{Σ: GRA} prg
    i k
  :
    inline_hp prg (i >>= k)
    =
    x <- inline_hp prg i;; inline_hp prg (k x).
  Proof using.
    rewrite /inline_hp. eapply bisim_is_eq.
    eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
    revert i k. gcofix CIH. i.
    ides i.
    - grind. rewrite [_ _ (Ret _)]unfold_iter_eq. grind.
      gfinal. right. eapply paco2_mon_bot; eauto.
      apply Reflexive_eqit. auto.
    - grind. rewrite !unfold_iter_eq. grind.
      gstep. econs. gstep. econs. gbase. eapply CIH.
    - rewrite !unfold_iter_eq.
      destruct e.
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      }
      destruct s; [destruct c|].
      {
        grind. gstep. econs. 
        guclo eqit_clo_trans; eauto.
        econs; cycle 1.
        { refl. }
        { gbase. eapply CIH. }
        { instantiate (1:= eq). i. subst. refl. }
        { i. subst. refl. }
        grind.
        replace (' x :_ <- prg fn args;; (tau;; ITree.subst k (k0 x)))
        with (' r0 : _ <- prg fn args;; ' x : _ <- (tau;; k0 r0);; k x) by grind.
        refl.
      } 
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.  
      }
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      }
      grind. rewrite! bind_trigger. gstep. econs. i.
      r. grind. gstep. econs. gbase. eauto.
    Unshelve. eauto with paco.
  Qed.

  Lemma bind_spawn `{Σ: GRA}
    prog fn args ktr
  :
    inline_hp prog (x <- trigger (Spawn fn args);; ktr x) 
    =
    x <- trigger (Spawn fn args);; tau;; inline_hp prog (ktr x).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_yield `{Σ: GRA}
    prog tid ktr
  :
    inline_hp prog (x <- trigger (Yield tid);; ktr x) 
    =
    x <- trigger (Yield tid);; tau;; inline_hp prog (ktr x).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.
  
  Lemma bind_core `{Σ: GRA}
    X prog (e: coreE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_pg `{Σ: GRA}
    X prog (e: pgE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_ag `{Σ: GRA}
    X prog (e: agE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma call `{Σ: GRA}
    prog ktr (fn: string) arg 
  :
    inline_hp prog (trigger (Call fn arg) >>= ktr)
    =
    tau;; inline_hp prog (x <- prog fn arg;; tau;; ITree.subst ktr (Ret x)).
  Proof using.
    rewrite/inline_hp unfold_iter_eq. ired. refl.
  Qed.

End HIRed.

(* CANCEL *)
Lemma sandbox_inline_commute `{Σ: GRA}
    ms fn sb
    (FIND: alist_find fn ms.(HMod.fnsems) = Some sb)
  :
  SB.sandbox_body (inline_fsem ms sb)
  = 
  inline_hfun (sandboxed_prog ms) (SB.sandbox_body sb).
Proof using.
  extensionality args.
  unfold inline_fsem. s.
  unfold SB.sandbox_body, inline_hfun. destruct sb as [[msk sc] [img bd]]. s.
  assert(SCP := ms.(HMod.well_scoped_fns)).
  specialize (SCP fn). rewrite/fnsems_scopes FIND in SCP.
  apply bisim_is_eq. move sc at bottom.
  ginit. generalize (bd args) as itr. clear FIND bd fn args.
  revert_until ms. gcofix CIH. i.
  ides itr.
  { rewrite !SBRed.ret HIRed.ret SBRed.ret. gstep. econs. refl. }
  { rewrite !SBRed.tau HIRed.tau !SBRed.tau. 
    gstep. econs. gstep. econs. gbase. eauto. }
  rewrite -bind_trigger !SBRed.bind.
  destruct e.
  {
    assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind.
    destruct a.
    - rewrite H !SBRed.Assume. des_ifs.
      + rewrite HIRed.bind_ag SBRed.bind SBRed.Assume !bind_trigger.
        gstep. econs. i. r. rewrite SBRed.tau. gstep. econs. gbase. eauto.
      + ired. rewrite !HIRed.bind_core SBRed.bind SBRed.take. s.
        gstep. r; s; econs. ss.
    - rewrite H !SBRed.AssumePrecise HIRed.bind_ag SBRed.bind SBRed.AssumePrecise !bind_trigger.
      gstep. econs. i. r. rewrite SBRed.tau. gstep. econs. gbase. eauto.
    - rewrite H !SBRed.Guarantee HIRed.bind_ag SBRed.bind SBRed.Guarantee !bind_trigger.
      gstep. econs. i. r. rewrite SBRed.tau. gstep. econs. gbase. eauto.
  }
  destruct s; [destruct c|].
  {
    rewrite !SBRed.call. des_ifs; cycle 1.
    { ired. rewrite !HIRed.bind_core !SBRed.bind SBRed.take !bind_trigger.
      gstep. econs. ss.
    }

    rewrite HIRed.call SBRed.tau. s.
    gstep. econs.
    destruct (alist_find fn (HMod.fnsems ms)) eqn: FIND; cycle 1.
    { ired. rewrite {2 4}/sandboxed_prog FIND. s. ired.
      rewrite !HIRed.bind_core !SBRed.bind SBRed.take !bind_trigger.
      gstep. econs. ss.
    }

    rewrite /sandboxed_prog /SB.sandbox_body. ired.
    destruct f as [[msk0 sc0] [img0 bd0]]. s.
    match goal with
    [|- _ _ (_ _ ?itr)] => assert (EX: exists itr', itr = SB.sandbox wmask_all (HMod.scopes ms) true itr'); cycle 1
    end.
    { des. rewrite EX. gbase. eapply CIH; try refl. }

    rewrite FIND. s. ired.
    eexists. instantiate (1:= _ >>= _).
    rewrite SBRed.bind. f_equal.
    { 
      erewrite <-(@sandbox_well_scoped _ _ _ _ _ _ sc0); try refl; eauto.
      ii. eapply HMod.well_scoped_fns. unfold fnsems_scopes.
      erewrite FIND. et.
    }
    extensionality x.
    rewrite subst_bind bind_ret_l -SBRed.tau.
    erewrite <-(@sandbox_well_scoped _ _ _ _ _ _ sc); eauto.
  }
  {
    rewrite !SBRed.spawn. des_ifs.
    + rewrite HIRed.bind_spawn SBRed.bind SBRed.spawn. s.
      rewrite !bind_trigger.
      gstep. econs. i. r.
      rewrite SBRed.tau. gstep. econs. gbase. eauto.
    + ired. rewrite !HIRed.bind_core !SBRed.bind SBRed.take !bind_trigger.
      gstep. econs. ss.
  }
  {
    rewrite !SBRed.yield HIRed.bind_yield SBRed.bind SBRed.yield !bind_trigger.
    gstep. econs. i. r.
    rewrite SBRed.tau. gstep. econs. gbase. eauto.
  }
  destruct s; [destruct p|].
  {
    rewrite !SBRed.put. des_ifs; cycle 1.
    { ired. rewrite !HIRed.bind_core !SBRed.bind SBRed.take !bind_trigger.
      gstep. econs. ss.
    }

    rewrite HIRed.bind_pg SBRed.bind SBRed.put. des_ifs; cycle 1.
    {
      exfalso. assert (existsb (String.eqb k0.1) (HMod.scopes ms) = true).
      {
        eapply existsb_exists. eapply existsb_exists in Heq. des.
        esplits; eauto.
      }
      rewrite H in Heq0. ss.
    }
    rewrite !bind_trigger. gstep. econs. i.
    rewrite SBRed.tau. gstep. econs. gbase; eauto. 
  }
  {
    rewrite !SBRed.get. des_ifs; cycle 1.
    { ired. rewrite !HIRed.bind_core !SBRed.bind SBRed.take !bind_trigger.
      gstep. econs. ss.
    }

    rewrite HIRed.bind_pg SBRed.bind SBRed.get. des_ifs; cycle 1.
    {
      exfalso. assert (existsb (String.eqb k0.1) (HMod.scopes ms) = true).
      {
        eapply existsb_exists. eapply existsb_exists in Heq. des.
        esplits; eauto.
      }
      rewrite H in Heq0. ss.
    }
    gstep. r; s. econs. i. ired.
    gstep. r; s. econs. gbase. et.
  }
  {
    destruct c.
    - rewrite SBRed.choose HIRed.bind_core SBRed.bind SBRed.choose !bind_trigger.
      gstep. econs. i. r. rewrite SBRed.tau. gstep. econs. gbase; eauto.
    - rewrite SBRed.take. des_ifs.
      + rewrite HIRed.bind_core SBRed.bind SBRed.take !bind_trigger.
        gstep. econs. i. gstep. r; s. econs. gbase. et.
      + ired. rewrite HIRed.bind_core SBRed.bind SBRed.take. s.
        gstep. r; s; econs. ss.
    - rewrite SBRed.io HIRed.bind_core SBRed.bind SBRed.io !bind_trigger.
      gstep. econs. i. r. rewrite SBRed.tau. gstep. econs. gbase; eauto.
  }
(*SLOW*)Qed.

Definition bindRR `{Σ: GRA} {R} RR P : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp Σ :=
  fun nths '(st0, ret0) '(st1, ret1) => (P ∗ RR nths (st0, ret0) (st1, ret1))%I.

Definition IstRR `{Σ: GRA} {R} Ist : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp Σ :=
  fun nths '(st0, ret0) '(st1, ret1) => (⌜ret0 = ret1⌝ ∗ Ist nths st0 st1)%I.

Lemma isim_RR_frame `{Σ: GRA}
    fls flt contextual r g nths
    {R} Ist (P: iProp Σ)
    ps pt sti_src sti_tgt
  :
    (P ∗ @isim _ contextual fls flt Ist r g R R 
          (fun nths '(sts, vs) '(stt, vt) => ⌜vs = vt⌝ ∗ Ist nths sts stt)%I
          ps pt nths sti_src sti_tgt)  
    ⊢ isim contextual fls flt Ist r g 
       (bindRR (IstRR Ist) P) ps pt nths sti_src sti_tgt.
Proof using.
  iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto.
Qed.

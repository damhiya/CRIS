Require Import Common.

Require Import HMod.
Require Import ISim MainAdequacy.

Set Implicit Arguments.

(* Inlining every function call in HMod. *)
Section INTERP.
  Context `{Σ: GRA}.

  Definition handle_callE (prog: callE ~> itree hmodE): itree hmodE Any.t -> itree hmodE (_ + Any.t)
  :=
    fun itr =>
      match observe (itr: itree hmodE Any.t) with
      | RetF rv => Ret (inr rv)
      | TauF itr' => tau;; Ret (inl itr')
      | VisF (inr1 (inr1 (inr1 (inr1 e)))) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inr1 (inl1 e)))) k => 
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inl1 c))) k =>
          Ret (inl (x <- prog _ c;; tau;; (k x)))
      | VisF (inr1 (inl1 e)) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inl1 e) k =>
          v <- trigger e;; Ret (inl (k v))
      end.

  Definition inline_hp (prog: callE ~> itree hmodE) (itr: itree hmodE Any.t)
    : itree hmodE Any.t
    :=
    ITree.iter (handle_callE prog) itr.

  Definition inline_hp_fun (prog: callE ~> itree hmodE) (body: Any.t -> itree hmodE Any.t)
    : Any.t -> itree hmodE Any.t
    :=
    fun args =>
      inline_hp prog (body args).

  Definition prog (ms: HMod.t) : callE ~> itree hmodE :=
    fun _ '(Call fn args) =>
      lbody <- (alist_find fn ms.(HMod.fnsems))!;;
      HMod.sandbox_body lbody args.
      
  Definition inline_hp_fbody (ms: HMod.t)
    : (list string * (Any.t -> itree hmodE Any.t)) -> (list string * (Any.t -> itree hmodE Any.t))
    :=
    fun '(k, b) => (k, inline_hp_fun (prog ms) b).

  Definition wrap_sandbox scopeS: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    := 
    fun kb => (scopeS, HMod.sandbox_body kb).

  Definition wrap_elimI ms: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    :=
    fun kb => inline_hp_fbody ms (wrap_sandbox ms.(HMod.scopes) kb). 

End INTERP.

Module HModInline.
  Import HMod.

  Program Definition inline `{Σ: GRA} (ms: HMod.t): HMod.t := {|
    HMod.scopes := ms.(scopes);
    HMod.fnsems := List.map (map_snd (wrap_elimI ms)) (ms.(fnsems));
    (* HMod.fnsems := List.map (map_snd (λ ksb, (ksb.1, inline_hp_fun (prog ms) ksb.2))) (ms.(fnsems)); *)
    HMod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. depdes ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite! alist_find_map in H. unfold o_map in H.
    des_ifs; ss. 
    (* inv Heq0.
    specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto. *)
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

  (* Definition to_elim ms := to_hmod ((interp_sb_hp_elim) ∘ fsb_body) ms. *)
End HModInline.

Module HIRed.

  Lemma iter_handle_bind `{Σ: GRA} ms i k:
    ITree.iter (handle_callE (prog ms)) (i >>= k)
    =
    x <- (ITree.iter (handle_callE (prog ms)) i);; ITree.iter (handle_callE (prog ms)) (k x).
  Proof. 
    eapply bisim_is_eq.
    eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
    revert i k. gcofix CIH. i.
    ides i.
    - grind. rewrite [_ _ (Ret _)]unfold_iter_eq. grind.
      gfinal. right. eapply paco2_mon_bot; eauto.
      apply Reflexive_eqit. auto.
    - grind. rewrite! unfold_iter_eq. grind.
      gstep. econs. gstep. econs. gbase. eapply CIH.
    - rewrite! unfold_iter_eq.
      destruct e.
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      }
      destruct p.
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.  
      }
      destruct s.
      {
        grind. gstep. econs. 
        guclo eqit_clo_trans; eauto.
        econs; cycle 1.
        { refl. }
        { gbase. eapply CIH. }
        { instantiate (1:= eq). i. subst. refl. }
        { i. subst. refl. }
        grind. 
        replace (' x : X <- prog ms c;; (tau;; ITree.subst k (k0 x)))
        with (' r0 : X <- prog ms c;; ' x : Any.t <- (tau;; k0 r0);; k x) by grind.
        refl.
      } 
      destruct s.
      {
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      }
      grind. rewrite! bind_trigger. gstep. econs. i.
      r. grind. gstep. econs. gbase. eauto.
    Unshelve. eauto with paco.
  Qed.
      
  Lemma ret `{Σ: GRA}
    prog (x: Any.t)
  :
    inline_hp prog (Ret x) = Ret x.
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma tau `{Σ: GRA}
    prog t
  :
    inline_hp prog (tau;; t) = tau;; tau;; inline_hp prog t.
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind `{Σ: GRA} ms
    itr ktr
  :
    inline_hp (prog ms) (itr >>= ktr)
    =
    x <- inline_hp (prog ms) itr;; inline_hp (prog ms) (ktr x).
  Proof.
    rewrite/inline_hp iter_handle_bind. refl.
  Qed.

  Lemma bind_sch `{Σ: GRA}
    X prog (e: schE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_core `{Σ: GRA}
    X prog (e: coreE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_pg `{Σ: GRA}
    X prog (e: pgE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma bind_ag `{Σ: GRA}
    X prog (e: agE X) ktr
  :
    inline_hp prog (x <- trigger e;; ktr x) 
    =
    x <- trigger e;; tau;; inline_hp prog (ktr x).
  Proof.
    rewrite/inline_hp unfold_iter_eq. grind.
  Qed.

  Lemma call `{Σ: GRA}
    prog ktr (fn: string) arg 
  :
    inline_hp prog (trigger (Call fn arg) >>= ktr)
    =
    tau;; inline_hp prog (x <- prog Any.t (resum IFun Any.t (Call fn arg));; tau;; ITree.subst ktr (Ret x)).
  Proof.
    rewrite/inline_hp unfold_iter_eq. ired. refl.
  Qed.

End HIRed.

(* CANCEL *)

Lemma wrap_elimI_well_scoped `{Σ: GRA}
    ms fn sb
    (FIND: alist_find fn ms.(HMod.fnsems) = Some sb)
  :
  HMod.sandbox_body (wrap_elimI ms sb)
  = 
  inline_hp_fun (prog ms) (HMod.sandbox_body sb).
Proof.
  extensionality args. 
  unfold wrap_elimI, inline_hp_fbody. s.
  unfold HMod.sandbox_body, inline_hp_fun. destruct sb. s.
  assert(SCP := ms.(HMod.well_scoped_fns)).
  specialize (SCP fn). rewrite/fnsems_scopes FIND in SCP.
  
  (* remember (HMod.scopes ms) as scopeS. i. *)
  rename l into scopeT. 
  apply bisim_is_eq. move scopeT at bottom.
  eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
  generalize (i args) as itr. clear FIND fn i args.
  revert_until ms. gcofix CIH. i.
  ides itr.
  - rewrite !SBRed.ret HIRed.ret SBRed.ret. gstep. econs. refl.
  - rewrite !SBRed.tau HIRed.tau !SBRed.tau. 
    gstep. econs. gstep. econs. gbase. eauto.
  - rewrite -bind_trigger !SBRed.bind.
    destruct e.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind. 
      rewrite H !SBRed.ag HIRed.bind_ag SBRed.bind SBRed.ag !bind_trigger.
      gstep. econs. i. r.
      rewrite SBRed.tau. gstep. econs. gbase. eauto.
    }
    destruct p.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inl1 s))) = trigger s) by grind.
      rewrite H !SBRed.sch HIRed.bind_sch SBRed.bind SBRed.sch !bind_trigger.
      gstep. econs. i. r.
      rewrite SBRed.tau. gstep. econs. gbase. eauto.
    }
    destruct s.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inl1 c)))) = trigger c) by grind.
      destruct c. rewrite H.
      rewrite !SBRed.call HIRed.call SBRed.tau. s.
      gstep. econs.
      destruct (alist_find fn (HMod.fnsems ms)) eqn: FIND.
      { 
        ired. assert (X:=@sandbox_well_scoped). 
        unfold HMod.sandbox_body. destruct p. s.
        gbase.
        match goal with
        [|- _ _ (_ _ ?itr)] => assert (EX: exists itr', itr = HMod.sandbox (HMod.scopes ms) itr')
        end.
        {
          eexists. instantiate (1:= _ >>= _). 
          rewrite SBRed.bind. f_equal.
          { 
            erewrite <-(@sandbox_well_scoped _ _ l); eauto. 
            assert(SCP0 := ms.(HMod.well_scoped_fns)).
            specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0.
            eauto.
          }
          extensionality x.
          instantiate (1:= fun x => tau;;(_ x)). s.
          rewrite SBRed.tau. do 2 f_equal.
          ired.
          erewrite <-(@sandbox_well_scoped _ _ scopeT); eauto. 
          instantiate (1:= fun x => HMod.sandbox scopeT (k x)). 
          s. refl.
        }
        des. rewrite EX. eapply CIH. refl.
      }
      ired. unfold triggerNB. ired. 
      rewrite !HIRed.bind_core !SBRed.bind SBRed.core !bind_trigger.
      gstep. econs. i. ss.
    }
    destruct s.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inl1 p))))) = trigger p) by grind.
      destruct p; rewrite H.
      {
        rewrite !SBRed.put. des_ifs.
        {
          rewrite HIRed.bind_pg SBRed.bind SBRed.put. des_ifs; cycle 1.
          {
            exfalso. assert (existsb (eqb k0.1) (HMod.scopes ms) = true).
            {
              eapply existsb_exists. eapply existsb_exists in Heq. des.
              esplits; eauto.
            }
            rewrite H0 in Heq0. ss.
          }
          rewrite !bind_trigger. gstep. econs. i.
          rewrite SBRed.tau. gstep. econs. gbase; eauto. 
        }
        rewrite HIRed.bind_core SBRed.bind SBRed.core !bind_trigger. 
        gstep. econs. i. r. 
        rewrite SBRed.tau. gstep. econs. gbase; eauto.
      }
      rewrite !SBRed.get. des_ifs.
      {
        rewrite HIRed.bind_pg SBRed.bind SBRed.get. des_ifs; cycle 1.
        {
          exfalso. assert (existsb (eqb k0.1) (HMod.scopes ms) = true).
          {
            eapply existsb_exists. eapply existsb_exists in Heq. des.
            esplits; eauto.
          }
          rewrite H0 in Heq0. ss.
        }
        rewrite !bind_trigger. gstep. econs. i.
        rewrite SBRed.tau. gstep. econs. gbase; eauto. 
      }
      rewrite HIRed.bind_core SBRed.bind SBRed.core !bind_trigger. 
      gstep. econs. i. r. 
      rewrite SBRed.tau. gstep. econs. gbase; eauto.
    }
    assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inr1 c))))) = trigger c) by grind.
    rewrite H SBRed.core HIRed.bind_core SBRed.bind SBRed.core !bind_trigger.
    gstep. econs. i. r.
    rewrite SBRed.tau. gstep. econs. gbase; eauto.
  Unshelve.
    eapply eqit__mono; eauto.
Qed.

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
Proof.
  iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto.
Qed.

Definition progI `{Σ: GRA} fl : callE ~> itree hmodE :=
  fun _ '(Call fn args) =>
    lbody <- (alist_find fn fl)!;;
    lbody args.

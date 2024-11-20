Require Import Coqlib.
Require Import Behavior.
Require Import AList.
Require Import SMod2HMod SMod2HModElim.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim ISim HPSim.
Require Import CtxRefine CtxRefineFacts MainAdequacy ClosedAdequacy.
Require Import SimGlobal SimGlobalFacts.
Require Import Cancel.
Require Import SMod HMod Mod Events.

Set Implicit Arguments.


Module StRed.
Section RED.

  Lemma interp_bind
        A B
        (itr: itree (stateE +' coreE) A)
        (ktr: A -> itree (stateE +' coreE) B)
        st0
    :
      interp_stateE B (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_stateE A (itr) st0 ;; interp_stateE B (ktr v) st1.
  Proof.
    unfold interp_stateE. grind. destruct x. grind.
  Qed.

  Lemma interp_tau
        A (itr: itree (stateE +' coreE) A)
        st0 
    :
      interp_stateE _ (tau;; itr) st0 = tau;; interp_stateE _ itr st0
  .
  Proof. 
    unfold interp_stateE. grind. 
  Qed.

  Lemma interp_st
        E st0 T e
    :
      @interp_stateE E T (trigger e) st0 =
      '(st1, r) <- handle_stateE _ e st0;;
      tau;; Ret (st1, r).
  Proof.
    unfold interp_stateE. grind. destruct x. grind.
  Qed.

  Lemma interp_ret
        E A st0 v
    :
      @interp_stateE E A (Ret v) st0 = Ret (st0, v)
  .
  Proof. 
    unfold interp_stateE. grind.
  Qed.
  
  Lemma interp_core
        st0 T
        (e: coreE T)
    :
      @interp_stateE (coreE) _ (trigger e) st0 = r <- trigger e;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_stateE. grind.
    unfold Mod2STS.pure_state. grind.
  Qed.

  Lemma interp_UB
        st0 A
    :
      (@interp_stateE (stateE +' coreE) A (triggerUB) st0) = triggerUB
  .
  Proof.
    unfold interp_stateE, Mod2STS.pure_state, triggerUB. grind.
  Qed.
  
  Lemma interp_NB
        st0 A
    :
      (@interp_stateE (stateE +' coreE) A (triggerNB) st0) = triggerNB
  .
  Proof.
    unfold interp_stateE, Mod2STS.pure_state, triggerNB. grind.
  Qed.  

End RED.
End StRed.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Variable md: SMod.t.

  Let sk: Sk.t := SMod.sk md.
  Let ms (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0) := 
    SMod.modsem md sk0.
  Let sbtb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspecbody) := 
    (ms SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Lemma stb_in_alist_find
        sk0 fn fsp
        (SKINCL: incl sk sk0) 
        (SKWF: Sk.wf sk0)
        (SOME: stb sk0 fn = Some fsp)
      :
        exists l fbody, 
          alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (l, {|fsb_fspec :=fsp; fsb_body := fbody|}).
  Proof.
    destruct (alist_find fn (_stb SKINCL SKWF)) eqn: FIND; cycle 1.
    { eapply STBSOUND in FIND. des. clarify. }
    unfold _stb, sbtb, ms in FIND.
    rewrite/__ alist_find_map_snd/o_map in FIND. des_ifs.
    destruct p0, f. exists l, fsb_body. repeat f_equal.
    assert (alist_find fn (_stb SKINCL SKWF) = Some (l, fsb_fspec)).
    { rewrite/_stb alist_find_map_snd /o_map /sbtb /ms Heq. ss. }
    eapply STBCOMPLETE in H. ss. rewrite SOME in H. inv H. ss.
  Qed.

  Lemma fsb_find_spec fn l fsp fbody sk0
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
    alist_find fn (_stb SKINCL SKWF) = Some (l, fsp).
  Proof.
    unfold sbtb, _stb.
    rewrite/__ alist_find_map_snd/o_map FIND. ss.
  Qed. 

  Lemma stb_find_fsb fn fsp l fspec fbody sk0
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (STB: stb sk0 fn = Some fsp)
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec:= fspec; fsb_body := fbody|}))
  :
    fsp = fspec.
  Proof.
    specialize (STBCOMPLETE SKINCL SKWF fn).
    eapply fsb_find_spec, STBCOMPLETE in FIND. ss.
    rewrite FIND in STB. inv STB. ss. 
  Qed.

  Let md_elim: HMod.t := HModAux.to_elimI (SModElim.to_elim md). 
  Let md_tgt: HMod.t := HModAux.to_elimI (SMod.to_hmod ginv stb md).
  
  Let ms_elim: HModSem.t := HMod.modsem md_elim (md_elim.(HMod.sk)).
  Let ms_tgt: HModSem.t := HMod.modsem md_tgt (md_tgt.(HMod.sk)).

  (* Sk.t lemmas *)
  (* sk0: list (string * Any.t) *)
  (* SKINCL: incl (SMod.sk md) sk0 *)
  (* SKWF: Sk.wf sk0 *)

  Definition hmod_elim_head X P : Any.t -> itree hmodE ((nat * X * nat * X) * Any.t)
    :=
    fun varg =>
      my_tid <- trigger Tid;; tau;;
      x <- trigger (Choose X);; tau;;
      arg <- trigger (Choose Any.t);; tau;;
      trigger (Guarantee (P my_tid x varg arg));;; tau;; tau;;
      my_tid' <- trigger Tid;; tau;;
      x' <- trigger (Take X);; tau;;
      varg' <- trigger (Take _);; tau;;
      trigger (Assume (P my_tid' x' varg' arg));;; tau;;
      Ret ((my_tid, x, my_tid', x'), varg').

  Definition hmod_elim_tail X Q : (nat * X * nat * X) -> Any.t -> itree hmodE Any.t
    :=
    fun '(my_tid, x, my_tid', x') vret' =>
      ret <- trigger (Choose Any.t);; tau;;
      trigger (Guarantee (Q my_tid' x' vret' ret));;; tau;; tau;; tau;;
      vret <- trigger (Take Any.t);; tau;;
      trigger (Assume (Q my_tid x vret ret));;; tau;;
      Ret vret.
      
  Definition HoareSpawnE ginv' (fsp: fspec) (fn: gname) (arg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; tau;;
    varg <- trigger (Choose Any.t);; tau;;
    tid <- trigger (Spawn fn arg);; tau;;
    trigger (Guarantee (ginv' tid -∗ fsp.(precond) tid x arg varg));;; tau;;
    Ret tid.

  Definition HoareYieldE ginv' (tid: nat) : itree hmodE unit :=
    trigger (Guarantee (ginv' tid));;; tau;;
    trigger (Yield tid);;; tau;;
    my_tid <- trigger Tid;; tau;;
    trigger (Assume (ginv' my_tid)).

  (*** use interp_hpI ***) 
  Variant elim_rel_def
    (relc: forall X Y (RR: X -> Y -> Prop), bool -> itree hmodE X -> itree hmodE Y -> Prop)
    {X Y}
    (RR: X -> Y -> Prop)
    (reli: bool -> itree hmodE X -> itree hmodE Y -> Prop)
    : bool -> itree hmodE X -> itree hmodE Y -> Prop
  :=
  | elim_rel_base v0 v1 p
    (RET: RR v0 v1)
    :
    elim_rel_def relc RR reli p (Ret v0) (Ret v1)

  | elim_rel_tau_src p itrS itrT
      (ITR: reli true itrS itrT)
    :
    elim_rel_def relc RR reli p (tau;; itrS) (itrT)

  | elim_rel_tau_tgt p itrS itrT
      (ITR: reli true itrS itrT)
    :
    elim_rel_def relc RR reli p (itrS) (tau;; itrT)

  | elim_rel_add {R} p itr ktrS ktrT
      (KTR: forall (v: R), reli true (ktrS v) (ktrT v))
    :
    elim_rel_def relc RR reli p (itr >>= ktrS) (itr >>= ktrT)

  | elim_rel_head X P p v src tgt ktrS ktrT
      (KTR: forall m, reli true (ktrS v) (ktrT (m, v)))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_head X P v) >>= ktrT)
    :
    elim_rel_def relc RR reli p src tgt
                  
  | elim_rel_tail X Q m v p src tgt ktrS ktrT
      (KTR: reli true (ktrS v) (ktrT v))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_tail X Q m v) >>= ktrT)
    :
    elim_rel_def relc RR reli p src tgt

  | elim_rel_NB
      p src tgt itrS ktrT
      (EQS: src = itrS)
      (EQT: tgt = trigger (Choose void) >>= ktrT)
    :
    elim_rel_def relc RR reli p src tgt

   | elim_rel_spawn
      sk0 p src tgt f fn args ktrS ktrT
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
      (STB: stb sk0 fn = Some f)
      (KTR: forall x, reli true (ktrS x) (ktrT x))
      (EQS: src =  trigger (Spawn fn args) >>= ktrS)
      (EQT: tgt = HoareSpawnE (ginv sk0) f fn args >>= ktrT)
    :
    elim_rel_def relc RR reli p src tgt

  | elim_rel_yield
      sk0 tid p src tgt ktrS ktrT
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
      (KTR: forall x, reli true (ktrS x) (ktrT x))
      (EQS: src = trigger (Yield tid) >>= ktrS)
      (EQT: tgt = HoareYieldE (ginv sk0) tid >>= ktrT)
    :
    elim_rel_def relc RR reli p src tgt

  | elim_rel_progress
      src tgt
      (REL: relc X Y RR false src tgt)
    :
    elim_rel_def relc RR reli true src tgt 
  .
  
  Inductive _elim_rel relc {X Y} RR p src tgt: Prop :=
  | _elim_rel_intro (SAT: @elim_rel_def relc X Y RR (_elim_rel relc RR) p src tgt).

  Definition elim_rel: forall X Y (RR: X -> Y -> Prop),  bool -> itree hmodE X -> itree hmodE Y -> Prop :=
     paco6 _elim_rel bot6.

  Variant thread_rel sk0 (cid tid: nat) (fr: Σ) src tgt : Prop :=
  | thread_rel_init scopes fsp fbody m varg arg
      (NOC: ~ Nat.eq_dec tid cid)
      (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg)
      (SRC: src = 
        (interp_hp (HModSem.sandbox scopes (fbody varg)) ε)
        >>= hp_fun_tail)
      (TGT: tgt =
        (interp_hp
             (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0)
                  fsp.(precond) fsp.(postcond) fbody arg)) ε) 
        >>= hp_fun_tail)
  | thread_rel_body (Q: Any.t -> Any.t -> iProp) p itrS itrT
      (ELIM: @elim_rel _ _ eq p itrS itrT)
      (SRC: src = (interp_hp itrS ε) >>= hp_fun_tail)
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else trigger (Assume (ginv sk0 tid)));;;
              vret <- itrT;; 
              (interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                ( ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q vret ret));;;
                  Ret ret))) fr)
        >>= hp_fun_tail)
  .

  (* TODO: elim_rel bindC *)

  Lemma elim_rel_def_mon relc relc' X Y RR P P'
    (RELC: relc <6= relc')
    (RELI: P <3= P')
  :
  @elim_rel_def relc X Y RR P <3= elim_rel_def relc' RR P'.
  Proof.
    i. destruct PR; eauto using @elim_rel_def.
  Qed.

  Lemma elim_rel_tarski elim_rel 
      X Y RR
      P
      (REL: @elim_rel_def elim_rel X Y RR P <3= P)
    :
    _elim_rel elim_rel RR <3= P.
  Proof.
    fix IH 4. i. inv PR. 
    inv SAT; eapply REL; try (econs; i; eapply IH; eauto).
    - econs; eauto.
    - econs; try refl. i. eapply IH. eauto.
    - econs 6; eauto. 
    - econs 7; eauto. 
    - econs 8; eauto.
    - econs 9; eauto.
    - econs 10; eauto.  
  Qed. 

  Lemma _elim_rel_mon : monotone6 _elim_rel.
  Proof.
    ii. eapply elim_rel_tarski; eauto.
    econs; inv PR.
    - econs; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
    - econs 10; eauto.
  Qed.

  Hint Resolve cpn6_wcompat: paco.
  Hint Resolve _elim_rel_mon: paco.
  Hint Resolve elim_rel_def_mon: paco.

  Definition elim_rel_indC elim_rel {X Y} RR :=
    @elim_rel_def bot6 X Y RR (elim_rel X Y RR).
  
  Lemma elim_rel_indC_mon: monotone6 elim_rel_indC.
  Proof.
    ii. inv IN. 
    - econs. eauto.
    - econs. eauto.
    - econs. eauto.
    - econs. eauto.
    - econs; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
    - econs 10. eauto.
  Qed.

  Hint Resolve elim_rel_indC_mon: paco.

  Lemma elim_rel_indC_spec:
    elim_rel_indC <7= gupaco6 _elim_rel (cpn6 _elim_rel).
  Proof.
    eapply wrespect6_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs.
    - econs; eauto.
    - econs; eauto. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 6; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 7; eauto. 
    - econs 8; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 9; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - ss.
  Qed.

  Lemma _elim_rel_flag_mon X Y RR r (p p': bool) src tgt
    (REL: @_elim_rel r X Y RR p src tgt)
    (LE: p -> p')
    :
    @_elim_rel r X Y RR p' src tgt.
  Proof.
    move REL before r. revert_until REL.
    pattern p, src, tgt. eapply elim_rel_tarski, REL.
    i. econs. inv PR.
    - econs. eauto.
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
    - hexploit LE; eauto. i. destruct p'; try discriminate.
      econs 10; eauto.
  Qed.

  Lemma elim_rel_flag_mon X Y RR (p p': bool) src tgt
      (REL: @elim_rel X Y RR p src tgt)
      (LE: p -> p')
    :
    elim_rel RR p' src tgt.
  Proof.
    move REL before ms_tgt. revert_until REL. pcofix CIH. i.
    pstep. eapply _elim_rel_flag_mon; eauto.
    eapply paco6_mon_bot in REL; eauto. punfold REL.
  Qed. 

  Variant elim_rel_flagC
    (r: forall X Y (RR: X -> Y -> Prop) , bool -> itree hmodE X -> itree hmodE Y -> Prop)
    X Y RR p src tgt : Prop := 
  | elim_rel_flagC_intro
    p0
    (REL: r X Y RR p0 src tgt)
    (FLAG: p0 = true -> p = true)
  .

  Lemma elim_rel_flagC_mon r1 r2 (LE: r1 <6= r2) :
    elim_rel_flagC r1 <6= elim_rel_flagC r2.
  Proof.
    ii. destruct PR; econs; eauto.
  Qed.

  Hint Resolve elim_rel_flagC_mon.

  Lemma elim_rel_flagC_spec:
    elim_rel_flagC <7= gupaco6 _elim_rel (cpn6 _elim_rel).
  Proof.
    eapply wrespect6_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply _elim_rel_flag_mon; eauto.
    eapply _elim_rel_mon. 2: { i. econs. eauto. }
    eapply GF; eauto.
  Qed. 

  Variant elim_rel_bindC
    (r: forall X Y (RR: X -> Y -> Prop), bool -> itree hmodE X -> itree hmodE Y -> Prop)
    : forall X Y (RR: X -> Y -> Prop), bool -> itree hmodE X -> itree hmodE Y -> Prop
    :=
  | elim_rel_bindC_intro
      Q0 Q1 QQ p i_src i_tgt
      (REL: r Q0 Q1 QQ p i_src i_tgt)

      X Y RR k_src k_tgt
      (RELK: ∀vs vt (EQ: QQ vs vt), r X Y RR false (k_src vs) (k_tgt vt))
    :
    elim_rel_bindC r RR p (i_src >>= k_src) (i_tgt >>= k_tgt)
  .

  Lemma elim_rel_bindC_mon
        r1 r2 
        (LEr: r1 <6= r2)
    :
    elim_rel_bindC r1 <6= elim_rel_bindC r2
  .
  Proof.
    ii. destruct PR; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_wrespectful:
    wrespectful6 _elim_rel elim_rel_bindC.
  Proof.
    econs; eauto using elim_rel_bindC_mon. i.
    destruct PR. apply GF in REL.
    move REL before GF. revert_until REL.
    pattern p, i_src, i_tgt.
    eapply elim_rel_tarski, REL. i. 
    inv PR; grind. 
    (* eauto 7 using elim_rel_mon, elim_rel_def, rclo3. *)
    - eapply _elim_rel_mon; cycle 1.
      { i. econs. eauto. }
      eapply _elim_rel_flag_mon; eauto.
      discriminate.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs 5; eauto; cycle 1.
      { instantiate (1 := fun _v => _). refl.  }
      s; eauto.
    - econs. econs 6; eauto; cycle 1.
      { instantiate (1 := fun _v => _). refl.  }
      s; eauto.
    - econs. econs 7; eauto. 
    - econs. econs 8; eauto. i. s. eauto. 
    - econs. econs 9; eauto. i. s. eauto.
    - econs. econs 10; eauto. 
      econs 2; eauto. econs; i; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_spec:
    elim_rel_bindC <7= gupaco6 _elim_rel (cpn6 _elim_rel).
  Proof.
    i. eapply wrespect6_uclo; eauto with paco. eapply elim_rel_bindC_wrespectful.
  Qed.


  Lemma HoareSpawn_sandbox
      scopes ginv' f fn args
    :
    HModSem.sandbox scopes (HoareSpawn ginv' f fn args) = HoareSpawn ginv' f fn args.
  Proof.
    unfold HoareSpawn.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. f_equal. extensionalities.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. f_equal. extensionalities.
    rewrite/__ HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag. f_equal. extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed. 

  Lemma HoareSpawn_hpI
      prog ginv' f fn args ktr
    :
    interp_hpI prog (HoareSpawn ginv' f fn args >>= ktr)
    =
    x <- HoareSpawnE ginv' f fn args;; interp_hpI prog (ktr x).
  Proof.
    unfold HoareSpawn, HoareSpawnE. ired.
    rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_sch. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_ag. f_equal.
  Qed.
  
  Lemma HoareYield_sandbox
      scopes ginv' tid
    :
    HModSem.sandbox scopes (HoareYield ginv' tid) = HoareYield ginv' tid.
  Proof.
    unfold HoareYield.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag. f_equal. extensionalities.
    rewrite/__ HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite/__ HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite HModSB.transl_ag. ss.
  Qed. 

  Lemma HoareYield_hpI
      prog ginv' tid ktr
    :
    interp_hpI prog (HoareYield ginv' tid >>= ktr)
    =
    x <- HoareYieldE ginv' tid;; tau;; interp_hpI prog (ktr x).
  Proof. 
    unfold HoareYield, HoareYieldE. ired.
    rewrite HIRed.bind_ag. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_sch. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_sch. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_ag. f_equal.
  Qed.

  Lemma HoareCall_inline_aux
      sk0 scopes fn varg scp fsp fbody 
      (FIND: alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (scp, {|fsb_fspec := fsp; fsb_body := fbody|}))
    :
    interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (HModSem.sandbox scopes (HoareCall fsp fn varg))
    =
    (* head *)
    my_tid <- trigger Tid;; tau;;
    m <- trigger (Choose (meta fsp));; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (precond fsp my_tid m varg arg));;; tau;; tau;;
    my_tid' <- trigger Tid;; tau;;
    m' <- trigger (Take (meta fsp));; tau;;
    varg' <- trigger (Take Any.t);; tau;;
    trigger (Assume (precond fsp my_tid' m' varg' arg));;; tau;; 
    (* body *)
    vret' <- interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox scp (interp_smod (ginv sk0) (stb sk0) (fbody varg')));;
    (* tail *)
    ret <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (postcond fsp my_tid' m' vret' ret));;; tau;; tau;; tau;;
    vret <- trigger (Take Any.t);; tau;;
    trigger (Assume (postcond fsp my_tid m vret ret));;; tau;;
    Ret vret.
  Proof.
    unfold HoareCall.
    (* head *)
    rewrite/__ HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch. 
    f_equal. extensionality my_tid. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core.
    f_equal. extensionality m. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core.
    f_equal. extensionality arg. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag.
    f_equal. extensionalities. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_call HIRed.call.
    do 2 f_equal. ired.
    rewrite/__ alist_find_map_snd FIND. ired.
    unfold HModSem.sandbox_body, interp_sb_hp, HoareFun. s.
    rewrite/__ HModSB.transl_bind HModSB.transl_sch. ired. rewrite HIRed.bind_sch.
    f_equal. extensionality my_tid'. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. rewrite HIRed.bind_core.
    f_equal. extensionality m'. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. rewrite HIRed.bind_core.
    f_equal. extensionality varg'. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag. ired. rewrite HIRed.bind_ag.
    f_equal. extensionalities. do 2 f_equal. 
    (* body *)
    rewrite HModSB.transl_bind. ired. rewrite HIRed.bind.
    f_equal. extensionality vret'.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. rewrite HIRed.bind_core.
    f_equal. extensionality ret. do 2 f_equal. 
    rewrite/__ HModSB.transl_bind HModSB.transl_ag. ired. rewrite HIRed.bind_ag.
    f_equal. extensionalities. do 2 f_equal.
    rewrite HModSB.transl_ret. ired. rewrite HIRed.tau.
    do 4 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. rewrite HIRed.bind_core.
    f_equal. extensionality vret. do 2 f_equal.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag. ired. rewrite HIRed.bind_ag.
    f_equal. extensionalities. do 2 f_equal.
    rewrite/__ HModSB.transl_ret HIRed.ret. ss.
  Qed.

  Lemma HoareCall_inline
      sk0 scopes fn varg scp fsp fbody 
      (FIND: alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (scp, {|fsb_fspec := fsp; fsb_body := fbody|}))
    :
    interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (HModSem.sandbox scopes (HoareCall fsp fn varg))
    =
    (* head *)
    '((my_tid, x, my_tid', x'), varg') <- (@hmod_elim_head (meta fsp) (precond fsp) varg);;
    (* body *)
    vret' <- interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox scp (interp_smod (ginv sk0) (stb sk0) (fbody varg')));;
    (* tail *)
    @hmod_elim_tail (meta fsp) (postcond fsp) (my_tid, x, my_tid', x') vret'. 
  Proof.
    erewrite HoareCall_inline_aux; eauto.
    unfold hmod_elim_head, hmod_elim_tail. ired. 
    repeat (f_equal; extensionalities; ired; repeat f_equal). 
  Qed.

  Definition elim_head_body 
    sk0 scp fsp fbody varg
    :=
    ('((my_tid, x, my_tid', x'), varg') <- (@hmod_elim_head (meta fsp) (precond fsp) varg);;
    (* body *)
    vret' <- interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox scp (interp_smod (ginv sk0) (stb sk0) (fbody varg')));;
    Ret ((my_tid, x, my_tid', x'), vret')).

  Lemma HoareCall_inline2
      sk0 scopes fn varg scp fsp fbody 
      (FIND: alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (scp, {|fsb_fspec := fsp; fsb_body := fbody|}))
    :
    interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
        (HModSem.sandbox scopes (HoareCall fsp fn varg))
    =
    (* head *)
    RET <- elim_head_body sk0 scp fsp fbody varg;;
    (* tail *)
    (fun RET =>
      let '((my_tid, x, my_tid', x'), vret') := RET in
      @hmod_elim_tail (meta fsp) (postcond fsp) (my_tid, x, my_tid', x') vret') RET. 
  Proof.
    erewrite HoareCall_inline; eauto. unfold elim_head_body. grind.
  Qed.

  Lemma add_dummy_ret R (itr: itree hmodE R):
    itr = itr >>= (fun x => Ret x).
  Proof. grind. Qed.

  Lemma elim_rel_refl
      sk0 scopes p itr
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
    :
    @elim_rel _ _ eq p
      (interp_hpI (prog (SModSemElim.to_elim (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes itr))
      (interp_hpI (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes (interp_smod (ginv sk0) (stb sk0) itr))).
  Proof. 
    unfold elim_rel.
    ginit. revert p itr scopes. gcofix CIH. i.
    assert (CASE:= case_itrH _ itr). des; subst.
    - rewrite/__ SModRed.interp_ret HModSB.transl_ret !HIRed.ret.
      gstep. econs. econs; eauto.
    - rewrite/__ SModRed.interp_tau !HModSB.transl_tau !HIRed.tau.
      gstep. do 9 econs. econs 10. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite/__ !HIRed.bind_ag. gstep. do 6 econs.  
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite/__ !HIRed.bind_ag. gstep. do 6 econs. 
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_sch !HModSB.transl_bind HModSB.transl_sch. ired.
      unfold handle_schE_hmodE. depdes s.
      + destruct (stb sk0 fn) eqn:STB; ired; cycle 1.
        { 
          unfold triggerNB. ired. 
          rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. 
          rewrite HIRed.bind_core. gstep. econs. econs 7; ss.
        }
        rewrite/__ HoareSpawn_sandbox HoareSpawn_hpI HIRed.bind_sch.
        gstep. econs. econs 8; eauto. i. s. econs. econs. 
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
        rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
      + rewrite/__ HoareYield_sandbox HoareYield_hpI HIRed.bind_sch.
        gstep. econs. econs 9; eauto. i. s.
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
        rewrite HIRed.tau. do 9 econs. econs 10. gbase. eapply CIH; eauto.
      + rewrite/__ HModSB.transl_sch !HIRed.bind_sch.
        gstep. do 6 econs.
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired.
        rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_call.
      unfold handle_callE_hmodE. depdes c. 
      destruct (stb sk0 fn) eqn: STB; ired; cycle 1.
      { 
        unfold triggerNB. 
        rewrite/__ !HModSB.transl_bind HModSB.transl_core. ired. 
        rewrite HIRed.bind_core. gstep. econs. econs 7; ss.
      }
      do 2 rewrite HModSB.transl_bind. 
      rewrite/__ HModSB.transl_call HIRed.call HIRed.bind.
      guclo elim_rel_indC_spec. econs. s.
      assert (FIND := stb_in_alist_find).
      specialize (FIND sk0 fn f SKINCL SKWF STB). des.
      destruct (alist_find fn (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, fsb_body ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))) eqn: FINDS; cycle 1.
      { exfalso. rewrite/__ alist_find_map_snd FIND in FINDS. clarify.  }
      ired. destruct p0. rewrite/__ alist_find_map_snd FIND in FINDS. s in FINDS. inv FINDS.
      unfold HModSem.sandbox_body. s. rewrite HIRed.bind. 
      erewrite HoareCall_inline2; eauto. 
      rewrite bind_bind. guclo elim_rel_bindC_spec. econs.
      {
        instantiate (1:= fun vs vt => vs = vt.2).
        unfold elim_head_body. guclo elim_rel_indC_spec. econs 5; swap 1 3.
        { f_equal. instantiate (1:= fun _ => _). refl. }
        { instantiate (1:= fun _ => _). refl. }
        grind. rewrite/__ [interp_hpI _ _]add_dummy_ret. 
        guclo elim_rel_bindC_spec. econs.
        { gstep. econs. econs 10. gbase. eapply CIH; ss. }
        i. gstep. econs. econs. ss.
      }
      i. guclo elim_rel_indC_spec.
      destruct vt, p0, p0, p0. (* Should have "vs = t" in here, lost in bindC *)
      econs 6; swap 1 3.
      { f_equal. refl. }
      { refl. }
      i. ired. rewrite/__ HModSB.transl_tau !HIRed.tau. 
      gstep. do 9 econs. econs 10. gbase. ss. subst. eapply CIH; eauto.
    - depdes s.
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_put. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
        * rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_get. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
        * rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_core !HModSB.transl_bind HModSB.transl_core. ired.
      rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 10. gbase. eapply CIH; eauto.
  Qed.

  Ltac hide_l := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ ?it _] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ ?it _] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac hide_r := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ _ ?it] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ _ ?it] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac reveal ITR := unfold ITR; clear ITR.

  Ltac st := prep; guclo simg_indC_spec; econs; try instantiate (1:= smj_top).
  Ltac _iter := rewrite unfold_iter_eq; ired.
  Ltac _iterI := rewrite/__ [ITree.iter (Cancel.handle_callE _) _]unfold_iter_eq; ired.
  Ltac _tau := rewrite/__ !StRed.interp_tau.
  Ltac _core := rewrite/__ StRed.interp_bind StRed.interp_core; prep.
  Ltac _coreH := rewrite/__ HModSB.transl_bind HModSB.transl_core interp_hp_bind interp_hp_core; prep.
  Ltac _asm := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Assume /mget_res; prep.
  Ltac _grt := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Guarantee /mget_res; prep.
  Ltac _sget := rewrite/sGet !StRed.interp_bind [interp_stateE Any.t _ _]StRed.interp_st/handle_stateE. 
  Ltac __supd := rewrite/sPut /sGet !StRed.interp_bind [interp_stateE _ _ _]StRed.interp_st/handle_stateE. 
  Ltac _supd := __supd; grind; try rewrite list_insert_insert; _tau; st; st; hss; ired; hss; ired.
  Ltac _ub := rewrite/triggerUB !StRed.interp_bind StRed.interp_core; st; i; ss.
  Ltac iterL := _iter; rewrite/__ list_lookup_insert;[|auto]; ired.
  Ltac ls := rewrite !list_insert_insert.

  Ltac _coreA := _core; st; i; st; grind; _tau; st.
  Ltac _coreE x := _core; st; exists x; st; grind; _tau; st.


  Inductive Forall3i X Y Z (R: nat -> X -> Y -> Z -> Prop): nat -> list X -> list Y -> list Z -> Prop :=
  | Forall3i_nil i: Forall3i R i [] [] []
  | Forall3i_cons
      i x y z xs ys zs
      (REL: R i x y z)
      (TAIL: Forall3i R (S i) xs ys zs):
      Forall3i R i (x :: xs) (y :: ys) (z :: zs).

  Lemma Forall3i_len 
    X Y Z (R: nat -> X -> Y -> Z -> Prop) i xs ys zs
    (REL: Forall3i R i xs ys zs)
  :
    List.length xs = List.length ys /\ List.length xs = List.length zs.
  Proof.
    induction REL; s; eauto.
    des. esplits; eauto.
  Qed.

  Lemma Forall3i_nth
    X Y Z (R: nat -> X -> Y -> Z -> Prop) (i k: nat) 
    (xs: list X) (ys: list Y) (zs: list Z)
    (REL: Forall3i R i xs ys zs)
    (NTH: k < List.length xs)
  :
    ∃ x y z,
    xs !! k = Some x /\
    ys !! k = Some y /\
    zs !! k = Some z /\
    R (i + k) x y z.
  Proof.
    revert k NTH.
    induction REL; s; i; eauto.
    - nia.
    - destruct k; s.
      + replace (i + 0) with i by nia. eauto 7.
      + replace (i + S k) with (S i + k) by nia.
      eapply IHREL; nia.
  Qed.
  
  Lemma Forall3i_forall:
      ∀ X Y Z (R: nat -> X -> Y -> Z -> Prop) i xs ys zs
        (RELS: forall k x y z 
                (LKX: xs !! k = Some x)
                (LKY: ys !! k = Some y)
                (LKZ: zs !! k = Some z),
              R (i + k) x y z)
        (EQLEN1: List.length xs = List.length ys)
        (EQLEN2: List.length xs = List.length zs)
        ,
      @Forall3i X Y Z R i xs ys zs. 
  Proof. Admitted.

  (* Lemma wf_fold_lookup cid (mr fr: Σ) frs
        (LEN: cid < strings.length frs)
        (WF: URA.wf (mr ⋅ foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε frs))
        (LK: frs !! cid = Some fr)
      :
        URA.wf (mr ⋅ fr).
  Proof.
    exploit nth_split. { apply LEN. }
    instantiate (1:= fr). 
    i. des. symmetry in x1.
    exploit (list_lookup_middle l1 l2 fr cid). { apply x1. }
    i. eapply nth_lookup_Some in LK. rewrite LK in x0.
    rewrite/__ x0 in WF.
    assert (foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε (l1 ++ fr :: l2) = fr ⋅ foldl (λ r1 r2 : Σ, r1 ⋅ r2) (foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε l1) l2).
    {
      rewrite foldl_app. s. 
      Search URA.wf.
      
    }

    eapply URA.wf_mon.
    
    instantiate (1:= ).  *)

  (* Let progS sk0 r :=  ModSem.prog (HModSem.to_mod (SModSemElim.to_elim (SMod.modsem md sk0)) r). *)
  (* Let progT sk0 r :=  ModSem.prog (HModSem.to_mod (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)) r). *)



  
  Lemma cancel_aux sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs frs mr srcs tgts ps pt cid st
       (* progS progT
       (PRS: progS = ModSem.prog (HModSem.to_mod (SModSemElim.to_elim (SMod.modsem md sk0)) rs))
       (PRT: progT = ModSem.prog (HModSem.to_mod (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)) (rs ⋅ mr))) *)
       (WF: URA.wf rs)       
       (LEN: cid < List.length frs)
       (WF: URA.wf (rs ⋅ mr ⋅ (foldl (fun r1 r2 => r1 ⋅ r2) ε frs)))
       (* (RET: ∀fsp m vret ret (MAIN: stb sk0 "CCR_init" = Some fsp), (fsp.(postcond) 0 m vret ret -∗ ⌜vret = ret⌝)) *)
       (REL: Forall3i (thread_rel sk0 cid) 0 frs srcs tgts),
       gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
       (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (* (progS sk0 rs)) *)
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.to_elimI
                         (SModSemElim.to_elim (SMod.modsem md sk0))) rs)))
              (cid, srcs))
         (Any.pair st rs↑);; Ret x.2)
         (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                (* (progT sk0 (rs ⋅ mr))) *)
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.to_elimI
                         (SModSem.to_hmod (ginv sk0) 
                            (stb sk0) (SMod.modsem md sk0))) (rs ⋅ mr)))) 
              (cid, tgts))
         (Any.pair st (rs ⋅ mr)↑);; Ret x.2).
  Proof.
    gcofix CIH. i.
    exploit Forall3i_nth; eauto. i. des.
    rename x into fr, y into src, z into tgt.
    depdes x3.
    { exfalso. apply NOC. s. destruct Nat.eq_dec; eauto. nia. }
    hexploit REL. i. eapply Forall3i_len in H. des.
    assert (cid < List.length srcs). { rewrite <- H. eauto. }
    assert (cid < List.length tgts). { rewrite <- H0. eauto. }

    rewrite !unfold_iter_eq. unfold handle_schE_callE at 1 3.
    rewrite/__ x1 x2. s. grind.
    punfold ELIM. 
    pattern p, itrS, itrT. eapply elim_rel_tarski, ELIM. i.
    clear ELIM.
  Admitted.
    (* { *)
      (* hide_r. grind.  *)
      (* _core. st. exists (ε, ε, rs). st. ired. _tau. st. *)
      (* iterL. _supd. *)
      (* iterL. _core. st. assert (Own (ε ⋅ rs) -∗ |==> Own (ε ⋅ ε ⋅ rs)) by (r_solve; eauto). *)
      (* exists H3. st. ired. _tau. st. rewrite list_insert_insert. *)
      (* iterL. _core. st. assert (Own ε -∗ True) by auto.  *)
      (* exists H4. st. ired. rewrite list_insert_insert. _tau. st. *)
      (* iterL. _supd. iterL. _supd. iterL.   *)
      (* destruct (Nat.eq_dec cid 0); [|_ub]. ired. *)
      (* rewrite/__ StRed.interp_ret. ired. *)
(*  *)
      (* reveal ITREE. ired. *)
      (* _coreA. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. _tau. st. st. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. *)
      (* rewrite/__ StRed.interp_ret. grind. *)
      (* Q v x -> v = x *)
      (* admit. *)
    (* } *)
    (* {  *)
      (* grind. *)
      (* assert (CASE := case_itrH _ itr). des.  *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* {  *)
        (* subst. depdes c.  *)
        (* hide_l.  *)
        (*  *)
        (* grind. _coreA. *)
        (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert.  *)
        (* iterL. _coreA. rewrite list_insert_insert. *)
        (* iterL. _supd. iterL. _supd. *)
        (* iterL. rewrite list_insert_insert. _tau. st. *)
(*  *)
        (* assert (FINDT: alist_find fn *)
        (* (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body)) *)
           (* (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2))) *)
              (* (SModSem.fnsems (SMod.modsem md sk0)))) *)
        (* = *)
        (* Some ( *)
          (* (interp_hp_fun ∘ HModSem.sandbox_body) (l, interp_sb_hp (ginv sk0) (stb sk0) {| fsb_fspec := f; fsb_body := fbody |}) *)
        (* )). *)
        (* { rewrite/__ !alist_find_map_snd /o_map x4. ss. } *)
(*  *)
        (* admit. *)
      (* } *)
      (* admit. *)
    (* } *)
    (* { *)
      (* grind. *)
      (* hide_l. _tau. st. depdes Heq. eapply inj_pair2 in x. subst. ired. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. rewrite list_insert_insert. _tau. st. st.  *)
      (* iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st.  *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. rewrite list_insert_insert. _tau. st. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE x. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE v. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE c0. rewrite list_insert_insert. *)
      (* iterL. _supd. iterL.  *)
      (* assert (WFC: URA.wf (c0 ⋅ c1 ⋅ c)). { admit. }  *)
      (* _coreE WFC. rewrite list_insert_insert. *)
      (* iterL. _coreE x5. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* admit. *)
    (* } *)
    (* { admit. } *)

  (* Admitted. *)
  
  Lemma wf_mon_solve (a b c: Σ) :
    URA.wf a -> a = b ⋅ c -> URA.wf b.
  Proof.
    i. inv H0. eapply URA.wf_mon; eauto.
  Qed.

  Theorem cancellation Ps Pt
    (COND: forall sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), 
      exists fsp m rt,
        (stb sk0 "CCR_init" = Some fsp) /\
        (forall rs (WF: URA.wf rs) (SRC: Own rs -∗ (Ps sk0)), URA.wf (rs ⋅ rt)) /\ 
        (Own rt ⊢ (Pt sk0) ∗ (fsp.(precond) 0 m tt↑ tt↑)) /\
        (∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    )
  :
    refines (md_elim, Ps) (md_tgt, Pt).
  Proof.
    econs. { s. r. refl. }
    ii. ss. specialize (COND sk0 EQV SKWF). des.
    (* resoure *)
    specialize (COND0 rs WFR SRC).
    eapply iProp_sepconj in COND1; cycle 1. 
    { eapply (@wf_mon_solve (rs ⋅ rt) _ rs); [eauto|r_solve]. }
    des. subst.
    exists (rs ⋅ p). esplits; eauto. 
    { eapply (@wf_mon_solve (rs ⋅ (p ⋅ q)) _ q); [eauto|r_solve]. }
    { iIntros "[_ P]". iStopProof. eapply iProp_Own; eauto. }
    {
      inv WFM. econs; eauto.
      rewrite/SModSem.to_hmod !map_map_compose !fst_map_snd.
      rewrite/SModSemElim.to_elim !map_map_compose !fst_map_snd in wf_fns. 
      ss.
    }
    r. eapply adequacy_global_itree.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.initial_itr. s. unfold ITree.map.
    (* remember (alist_encode (SModSem.initial_st (SMod.modsem md sk0))) as st. *)
    destruct (alist_find "CCR_init" (SModSem.fnsems (SMod.modsem md sk0))) eqn:E; cycle 1.
    {
      rewrite/__ !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite/__ StRed.interp_bind. grind.
      destruct (resum IFun void (Choose void)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite/__ [interp_stateE _ _ _]StRed.interp_core. grind.
      ginit. guclo simg_indC_spec. econs. i. ss.
    }
    rewrite/__ !alist_find_map/o_map E. s. 
    erewrite !wrap_elimI_well_scoped; cycle 1.
    { unfold SModSem.to_hmod. s. rewrite alist_find_map_snd. rewrite E. ss. }
    { unfold SModSemElim.to_elim. s. rewrite alist_find_map_snd. rewrite E. ss. }
    ired.
    destruct p0. s.
    unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold interp_hpI_fun, interp_sb_hp, interp_hp_body. s.
    unfold HoareFun.
    
    unfold interp_modE, interp_schE_callE. 
    (* _coreH. *)
    destruct f.
    assert (SKINCL: incl sk sk0). { eapply Sk.equiv_incl. eauto. }
    pose proof (stb_find_fsb SKINCL SKWF COND E). subst.
    hide_l.
    ginit.
    rewrite/__ !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists m. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists q. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    assert (URA.wf (q ⋅ ε ⋅ (rs ⋅ p))). 
    { eapply wf_eq_solve; [eapply COND0|r_solve]. }
    exists H. ired. _tau. st. st. 
    _iter. _core. st.
    eapply iProp_Own in COND4. exists COND4. ired.
    _iter. _tau. do 4 st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CCR_main's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto.
    { instantiate (1:= [_]). ss. }
    { s. eapply wf_eq_solve; [eapply H|r_solve]. }
    econs; eauto using Forall3i.
    econs 2; s; eauto; cycle 1. 
    {
      rewrite/__ HModSB.transl_bind HIRed.bind. 
      instantiate (1:= postcond fsb_fspec 0 m).
      instantiate (1:= interp_hpI _ (HModSem.sandbox l (interp_smod (ginv sk0) (stb sk0) (fsb_body tt↑)))).
      ired. repeat f_equal; [|r_solve]. 
      extensionalities.
      rewrite/__ HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
      extensionalities.
      rewrite/__ HModSB.transl_bind HModSB.transl_ag. f_equal.
      extensionalities.
      rewrite HModSB.transl_ret. ss.
    }
    eapply elim_rel_refl; eauto.
    Unshelve. 
      { eapply smj_top. }
      { apply true. } 
  Qed.
  
  (*** Final Theorem ***)
  (* Theorem cancellation P: *)
    (* refines (md_src, (fun _ => emp)%I) (md_tgt, P). *)
  (* Proof. Admitted. *)

End CANCEL.

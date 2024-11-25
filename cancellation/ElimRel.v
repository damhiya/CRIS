Require Import Coqlib.
Require Import Behavior.
Require Import AList.
Require Import SMod2HMod SMod2HModAux.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim ISim HPSim.
Require Import CtxRefine CtxRefineFacts MainAdequacy ClosedAdequacy.
Require Import SimGlobal SimGlobalFacts.
Require Import SMod HMod Mod Events.
Require Import HModInline Cancel.

Section REL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.
  Variable md: SMod.t.
  Notation iProp := (iProp Σ).
  Let sk: Sk.t := SMod.sk md.

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
      (* itr shouldn't have 'Call' events. But how? 
         idea 1. Define event type without CallE
         idea 2. Manually add a relation for each event type as SimStrict before.
      *)
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
      (EQT: tgt = trigger (Choose False) >>= ktrT)
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
    elim_rel X Y RR p' src tgt.
  Proof.
    move REL before Y. revert_until REL. pcofix CIH. i.
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
    elim_rel_bindC r X Y RR p (i_src >>= k_src) (i_tgt >>= k_tgt)
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

End REL.

Hint Resolve cpn6_wcompat: paco.
Hint Resolve _elim_rel_mon: paco.


Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.
  Variable md: SMod.t.
  Notation iProp := (iProp Σ).
  Let sk: Sk.t := SMod.sk md.
  Let ms (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0) := 
    SMod.modsem md sk0.
  Let sbtb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspecbody) := 
    (ms sk0 SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb sk0 SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Lemma stb_in_alist_find
        (sk0: Sk.t) fn fsp
        (SKINCL: incl sk sk0) 
        (SKWF: Sk.wf sk0)
        (SOME: stb sk0 fn = Some fsp)
      :
        exists l fbody, 
          alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (l, {|fsb_fspec :=fsp; fsb_body := fbody|}).
  Proof.
    destruct (alist_find fn (_stb sk0 SKINCL SKWF)) eqn: FIND; cycle 1.
    { eapply STBSOUND in FIND. des. clarify. }
    unfold _stb, sbtb, ms in FIND.
    rewrite/__ alist_find_map_snd/o_map in FIND. des_ifs.
    destruct p0, f. exists l, fsb_body. repeat f_equal.
    assert (alist_find fn (_stb sk0 SKINCL SKWF) = Some (l, fsb_fspec)).
    { rewrite/_stb alist_find_map_snd /o_map /sbtb /ms Heq. ss. }
    eapply STBCOMPLETE in H. ss. rewrite SOME in H. inv H. ss.
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
    inline_hp prog (HoareSpawn ginv' f fn args >>= ktr)
    =
    x <- HoareSpawnE ginv' f fn args;; inline_hp prog (ktr x).
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
    inline_hp prog (HoareYield ginv' tid >>= ktr)
    =
    x <- HoareYieldE ginv' tid;; tau;; inline_hp prog (ktr x).
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
    inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (HModSem.sandbox scopes (HoareCall fsp fn varg))
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
    vret' <- inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
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
    inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (HModSem.sandbox scopes (HoareCall fsp fn varg))
    =
    (* head *)
    '((my_tid, x, my_tid', x'), varg') <- (hmod_elim_head (meta fsp) (precond fsp) varg);;
    (* body *)
    vret' <- inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox scp (interp_smod (ginv sk0) (stb sk0) (fbody varg')));;
    (* tail *)
    hmod_elim_tail (meta fsp) (postcond fsp) (my_tid, x, my_tid', x') vret'. 
  Proof.
    erewrite HoareCall_inline_aux; eauto.
    unfold hmod_elim_head, hmod_elim_tail. ired. 
    repeat (f_equal; extensionalities; ired; repeat f_equal). 
  Qed.

  Definition elim_head_body 
    sk0 scp fsp fbody varg
    :=
    ('((my_tid, x, my_tid', x'), varg') <- (hmod_elim_head (meta fsp) (precond fsp) varg);;
    (* body *)
    vret' <- inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox scp (interp_smod (ginv sk0) (stb sk0) (fbody varg')));;
    Ret ((my_tid, x, my_tid', x'), vret')).

  Lemma HoareCall_inline2
      sk0 scopes fn varg scp fsp fbody 
      (FIND: alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (scp, {|fsb_fspec := fsp; fsb_body := fbody|}))
    :
    inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
        (HModSem.sandbox scopes (HoareCall fsp fn varg))
    =
    (* head *)
    RET <- elim_head_body sk0 scp fsp fbody varg;;
    (* tail *)
    (fun RET =>
      let '((my_tid, x, my_tid', x'), vret') := RET in
      hmod_elim_tail (meta fsp) (postcond fsp) (my_tid, x, my_tid', x') vret') RET. 
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
    elim_rel ginv stb md _ _ eq p
      (inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes itr))
      (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
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
        { f_equal. }
        { instantiate (1:= fun _ => _). refl. }
        grind. rewrite/__ [inline_hp _ _]add_dummy_ret. 
        guclo elim_rel_bindC_spec. econs.
        { gstep. econs. econs 10. gbase. eapply CIH; ss. }
        i. gstep. econs. econs. ss.
      }
      i. guclo elim_rel_indC_spec.
      destruct vt, p0, p0, p0. (* Should have "vs = t" in here, lost in bindC *)
      econs 6; swap 1 3.
      { f_equal. }
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

End CANCEL.
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
      
  Definition HoareSpawnE ginv' (fsp: fspec) (fn: gname) (varg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    tid <- trigger (Spawn fn arg);; tau;;
    trigger (Guarantee (ginv' tid -∗ fsp.(precond) tid x varg arg));;; tau;;
    Ret tid.

  Definition HoareYieldE ginv' (tid: nat) : itree hmodE unit :=
    trigger (Guarantee (ginv' tid));;; tau;;
    trigger (Yield tid);;; tau;;
    my_tid <- trigger Tid;; tau;;
    trigger (Assume (ginv' my_tid)).


  Variant elim_rel_def {sk0 A}
    (self: list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop)
    : list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop
  :=
  | elim_rel_NB l itrS ktrT
    :
    elim_rel_def self l itrS (trigger (Choose False) >>= ktrT)

  | elim_rel_base v1 v2
    :
    elim_rel_def self [] (Ret v1) (Ret v2)

  | elim_rel_tau l itrS itrT
      (ITR: self l itrS itrT)
    :
    elim_rel_def self l (tau;; itrS) (tau;; itrT)

  | elim_rel_core {R} l (e: coreE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) (a <- trigger e;; (tau;; tau;; ktrT a))

  | elim_rel_pg {R} l (e: pgE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) (a <- trigger e;; (tau;; tau;; ktrT a))

  | elim_rel_asm P l ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Assume P) >>= ktrS) (a <- trigger (Assume P);; (tau;; tau;; ktrT a))

  | elim_rel_grt P l ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Guarantee P) >>= ktrS) (a <- trigger (Guarantee P);; (tau;; tau;; ktrT a))
  
  | elim_rel_tid l ktrS ktrT
      (KTR: forall (tid: nat), self l (ktrS tid) (ktrT tid))
    :
    elim_rel_def self l (trigger Tid >>= ktrS) (a <- trigger Tid;; (tau;; tau;; ktrT a))

  | elim_rel_head X P l varg ktrS ktrT
     (KTR: forall tid tid' m m' varg, 
            self ((tid, tid', existT X (m, m'))::l) (ktrS varg) (ktrT (tid, m, tid', m', varg)))
   :
   elim_rel_def self l (tau;; ktrS varg) (@hmod_elim_head X P varg >>= ktrT) 
   (* elim_rel_def self l (tau;; ktrS varg) ('(tid, m, tid', m', varg') <- @hmod_elim_head X P varg;; ktrT (tid, m, tid', m', varg'))  *)
  
  | elim_rel_tail X Q l tid m tid' m' vret src ktrS ktrT
      (SRC: src = ktrS vret)
      (KTR: forall vret, self l (ktrS vret) (ktrT vret))
    :
    elim_rel_def self ((tid, tid', existT X (m, m'))::l)
        src 
        (@hmod_elim_tail X Q (tid, m, tid', m') vret >>= ktrT)
        (* (vret' <- (@hmod_elim_tail X Q (tid, m, tid', m') vret);; (tau;; tau;; ktrT vret')) *)

  | elim_rel_spawn l f fn args ktrS ktrT
      (STB: stb sk0 fn = Some f)
      (KTR: forall x, self l (ktrS x) (ktrT x))
    :
    elim_rel_def self l (trigger (Spawn fn args) >>= ktrS)
                        (x <- HoareSpawnE (ginv sk0) f fn args;; (tau;; ktrT x))

  | elim_rel_yield tid l ktrS ktrT
      (KTR: forall x, self l (ktrS x) (ktrT x))
    :
    elim_rel_def self l (trigger (Yield tid) >>= ktrS)
                        (x <- HoareYieldE (ginv sk0) tid;; (tau;; tau;; ktrT x))
  .

  Definition elim_rel {sk0 A} :=
    paco3 (@elim_rel_def sk0 A) bot3.

  Definition thread_local_rel {sk0} itrS itrT : Prop :=
    @elim_rel sk0 Any.t [] itrS itrT.

  Lemma elim_rel_def_mon {sk0 A} r1 r2
    (REL: r1 <3= r2)
  :
  @elim_rel_def sk0 A r1 <3= @elim_rel_def sk0 A r2.
  Proof.
    i. destruct PR; eauto using @elim_rel_def.
  Qed.

  Variant elim_rel_bindC {A}
    (r: list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop)
    : list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop
    :=
  | elim_rel_bindC_intro
      itrS itrT
      (REL: r [] itrS itrT)

      l ktrS ktrT
      (RELK: ∀v, r l (ktrS v) (ktrT v))
      (* (RELK: ∀vs vt, r l (ktrS vs) (ktrT vt)) *)
    :
    elim_rel_bindC r l (itrS >>= ktrS) (itrT >>= ktrT)
  .

  Lemma elim_rel_bindC_mon {A}
        r1 r2 
        (LEr: r1 <3= r2)
    :
    @elim_rel_bindC A r1 <3= elim_rel_bindC r2
  .
  Proof.
    ii. destruct PR; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_spec {sk0 A}:
    elim_rel_bindC <4= gupaco3 (@elim_rel_def sk0 A) (cpn3 (@elim_rel_def sk0 A)).
  Proof. Admitted.

End REL.

Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.


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
      sk0 scopes itr
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
    :
    @elim_rel _ ginv stb sk0 _ []
      (inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes itr))
      (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes (interp_smod (ginv sk0) (stb sk0) itr))).
  Proof. 
    unfold elim_rel.
    ginit. revert itr scopes. gcofix CIH. i.
    assert (CASE:= case_itrH _ itr). des; subst.
    - rewrite SModRed.interp_ret HModSB.transl_ret !HIRed.ret.
      gstep. econs. 
    - rewrite SModRed.interp_tau !HModSB.transl_tau !HIRed.tau.
      gstep; econs. gstep; econs. eauto with paco.
    - rewrite SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite !HIRed.bind_ag. 
      set (fun _ => tau;; _) at 2. eassert (i = _).
      {
        unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
        extensionalities. do 2 f_equal.
        rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
      }
      rewrite H. gstep. econs. gstep. econs. eauto with paco.
    - rewrite/__ SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite/__ !HIRed.bind_ag. 
      set (fun _ => tau;; _) at 2. eassert (i = _).
      {
        unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
        extensionalities. do 2 f_equal.
        rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
      }
      rewrite H. gstep. econs. gstep. econs. eauto with paco.
    - rewrite/__ SModRed.interp_bind SModRed.interp_sch !HModSB.transl_bind HModSB.transl_sch. ired.
      unfold handle_schE_hmodE. depdes s.
      + destruct (stb sk0 fn) eqn:STB; ired; cycle 1.
        { 
          unfold triggerNB. ired. 
          rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. 
          rewrite HIRed.bind_core. gstep. econs. 
        }
        rewrite/__ HoareSpawn_sandbox HoareSpawn_hpI HIRed.bind_sch.
        set (HoareSpawnE _ _ _ _ >>= _). eassert (i = _).
        {
          unfold i. instantiate (1:= ITree.bind _ (fun _ => tau;; _)).
          f_equal. extensionalities.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. f_equal.
        }
        rewrite H. gstep. econs; eauto. i. gstep. econs. eauto with paco.
      + rewrite/__ HoareYield_sandbox HoareYield_hpI HIRed.bind_sch.
        set (fun _ => tau;; _) at 2. eassert (i = _).
        {
          unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
          extensionalities. do 2 f_equal.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
        }
        rewrite H. gstep. econs. i. gstep. econs. eauto with paco.
      + rewrite/__ HModSB.transl_sch !HIRed.bind_sch.
        set (fun _ => tau;; _) at 2. eassert (i = _).
        {
          unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
          extensionalities. do 2 f_equal.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
        }
        rewrite H. gstep. econs. i. gstep. econs. eauto with paco.
    - rewrite/__ SModRed.interp_bind SModRed.interp_call.
      unfold handle_callE_hmodE. depdes c. 
      destruct (stb sk0 fn) eqn: STB; ired; cycle 1.
      { 
        unfold triggerNB. 
        rewrite/__ !HModSB.transl_bind HModSB.transl_core. ired. 
        rewrite HIRed.bind_core. gstep. econs.
      }
      do 2 rewrite HModSB.transl_bind. 
      rewrite/__ HModSB.transl_call HIRed.call HIRed.bind.
      
      assert (FIND := stb_in_alist_find).
      specialize (FIND sk0 fn f SKINCL SKWF STB). des.
      destruct (alist_find fn (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, fsb_body ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))) eqn: FINDS; cycle 1.
      { exfalso. rewrite/__ alist_find_map_snd FIND in FINDS. clarify.  }
      ired. rewrite FINDS. destruct p. rewrite/__ alist_find_map_snd FIND in FINDS. s in FINDS. inv FINDS. 
      ired. unfold HModSem.sandbox_body. s. rewrite HIRed.bind.
      rewrite -bind_tau. guclo elim_rel_bindC_spec. econs.
      {
        erewrite HoareCall_inline; eauto.
        set (inline_hp _ _ ). eassert (i0 = _ args).
        {
          unfold i0. instantiate (1:= fun x => inline_hp _ (_ ( i x))).
          refl.
        }
        remember (λ x : Any.t, inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) (HModSem.sandbox l0 (i x))).
        rewrite H. gstep. econs. i. rewrite [i1 varg]add_dummy_ret.
        guclo elim_rel_bindC_spec. econs.
        { rewrite Heqi1. eauto with paco. }
        i. rewrite [hmod_elim_tail _ _ _ _]add_dummy_ret.

        gstep. econs.
        { instantiate (1:= fun x => Ret x). refl. }
        i. s. gstep. econs.
      }

      i. ired. rewrite HModSB.transl_tau !HIRed.tau.
      gstep. econs. gstep. econs. eauto with paco.

    - depdes s.
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_put. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg.
          set (fun _ => tau;; _) at 2. eassert (i = _).
          {
            unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
            extensionalities. do 2 f_equal.
            rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
          }
          rewrite H. gstep. econs. i. gstep. econs. eauto with paco. 
        * rewrite/__ !HIRed.bind_core.
          set (fun _ => tau;; _) at 2. eassert (i = _).
          {
            unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
            extensionalities. do 2 f_equal.
            rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
          } 
          rewrite H. gstep. econs. i. gstep. econs. eauto with paco. 
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_get. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg. 
          set (fun _ => tau;; _) at 2. eassert (i = _).
          {
            unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
            extensionalities. do 2 f_equal.
            rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
          } 
          rewrite H. gstep. econs. i. gstep. econs. eauto with paco.
        * rewrite/__ !HIRed.bind_core. 
          set (fun _ => tau;; _) at 2. eassert (i = _).
          {
            unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
            extensionalities. do 2 f_equal.
            rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
          } 
          rewrite H. gstep. econs. i. gstep. econs. eauto with paco. 
    - rewrite/__ SModRed.interp_bind SModRed.interp_core !HModSB.transl_bind HModSB.transl_core. ired.
      rewrite/__ !HIRed.bind_core. 
      set (fun _ => tau;; _) at 2. eassert (i = _).
      {
        unfold i. instantiate (1:= fun _ => tau;; (tau;; tau;; _)).
        extensionalities. do 2 f_equal.
        rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite HIRed.tau. f_equal.
      }   
      rewrite H. gstep. econs. i. gstep. econs. eauto with paco. 
  Qed.

End CANCEL.
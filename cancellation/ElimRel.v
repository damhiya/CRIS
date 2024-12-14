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
      
  Definition HoareYieldE ginv' (tid: nat) : itree hmodE unit :=
    trigger (Guarantee (ginv' tid));;; tau;;
    trigger (Yield tid);;; tau;;
    my_tid <- trigger Tid;; tau;;
    trigger (Assume (ginv' my_tid)).

  Definition HoareSpawnE ginv' (fsp: fspec) (fn: gname) (varg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    tid <- trigger (Spawn fn arg);; tau;;
    trigger (Guarantee (ginv' tid -∗ fsp.(precond) tid x varg arg));;; tau;;
    HoareYieldE ginv' tid;;; 
    Ret tid.

  Definition Spawn_CancelE (fn: gname) (varg: Any.t) : itree hmodE nat :=
    tid <- trigger (Spawn fn varg);; tau;;
    trigger (Yield tid);;;
    Ret tid.

  Variant elim_rel_def {sk0 A}
    (self: list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop)
    : list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop
  :=
  | elim_rel_NB l itrS ktrT
    :
    elim_rel_def self l itrS (trigger (Choose False) >>= ktrT)

  | elim_rel_base v
    :
    elim_rel_def self [] (Ret v) (Ret v)

  | elim_rel_tau l itrS itrT
      (ITR: self l itrS itrT)
    :
    elim_rel_def self l (tau;; itrS) (tau;; itrT)

  | elim_rel_core {R} l (e: coreE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

  | elim_rel_pg {R} l (e: pgE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

  | elim_rel_asm P l ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Assume P) >>= ktrS) (a <- trigger (Assume P);; ktrT a)

  | elim_rel_grt P l ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Guarantee P) >>= ktrS) (a <- trigger (Guarantee P);; ktrT a)
  
  | elim_rel_tid l ktrS ktrT
      (KTR: forall (tid: nat), self l (ktrS tid) (ktrT tid))
    :
    elim_rel_def self l (trigger Tid >>= ktrS) (a <- trigger Tid;; ktrT a)

  | elim_rel_head X P l varg src ktrS ktrT
     (SRC: src = ktrS varg)
     (KTR: forall tid tid' m m' varg, 
            self ((tid, tid', existT X (m, m'))::l) (ktrS varg) (ktrT (tid, m, tid', m', varg)))
   :
   elim_rel_def self l (tau;; src) (@hmod_elim_head X P varg >>= ktrT) 
  
  | elim_rel_tail X Q l tid m tid' m' vret src ktrS ktrT
      (SRC: src = ktrS vret)
      (KTR: forall vret, self l (ktrS vret) (ktrT vret))
    :
    elim_rel_def self ((tid, tid', existT X (m, m'))::l)
        (tau;; tau;; tau;; src) 
        (x <- @hmod_elim_tail X Q (tid, m, tid', m') vret;; tau;; ktrT x)

  | elim_rel_spawn l f fn args ktrS ktrT
      (STB: stb sk0 fn = Some f)
      (KTR: forall x, self l (ktrS x) (ktrT x))
    :
    elim_rel_def self l (Spawn_CancelE fn args >>= ktrS)
                        (x <- HoareSpawnE (ginv sk0) f fn args;; ktrT x)

  | elim_rel_yield tid l ktrS ktrT
      (KTR: forall x, self l (ktrS x) (ktrT x))
    :
    elim_rel_def self l (trigger (Yield tid) >>= ktrS)
                        (x <- HoareYieldE (ginv sk0) tid;; ktrT x)
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

  Hint Resolve cpn3_wcompat: paco.
  Hint Resolve elim_rel_def_mon: paco.
  
  Variant elim_rel_bindC {A}
    (r: list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop)
    : list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A -> itree hmodE A -> Prop
    :=
  | elim_rel_bindC_intro
      l1 l2 itrS itrT ktrS ktrT
      (REL: r l1 itrS itrT)
      (RELK: ∀v, r l2 (ktrS v) (ktrT v))
    :
    elim_rel_bindC r (l1++l2) (itrS >>= ktrS) (itrT >>= ktrT)
  .

  Lemma elim_rel_bindC_mon {A}:
    monotone3 (@elim_rel_bindC A).
  Proof.
    ii. destruct IN; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_spec {sk0 A}:
    elim_rel_bindC <4= gupaco3 (@elim_rel_def sk0 A) (cpn3 (@elim_rel_def sk0 A)).
  Proof.
    Local Opaque hmod_elim_tail.
    eapply wrespect3_uclo; eauto with paco.
    econs; [apply elim_rel_bindC_mon|].
    i. inv PR. apply GF in REL.
    inv REL; grind; eauto 7 using rclo3, elim_rel_def, elim_rel_bindC with paco.
    - econs.
      { instantiate (1:= fun varg => x <- ktrS0 varg;; ktrS x). eauto. }
      i. econs 2; cycle 1.
      + rewrite app_comm_cons. econs; [apply KTR|]; eauto.
      + eauto using rclo3.
    - eapply eq_ind.
      + eapply elim_rel_tail.
        { instantiate (2:= fun vret => x <- ktrS0 vret;; ktrS x). eauto. }
        i. s. econs 2; cycle 1.
        * econs; [apply KTR|]; eauto.
        * eauto using rclo3.
      + f_equal. extensionalities. grind.
  Qed.

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

  Lemma HoareSpawn_sandbox
      scopes ginv' f fn args
    :
    HModSem.sandbox scopes (HoareSpawn ginv' f fn args) = HoareSpawn ginv' f fn args.
  Proof.
    unfold HoareSpawn.
    rewrite HModSB.transl_bind HModSB.transl_core. f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_core. f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_ag. f_equal. extensionalities.
    rewrite HModSB.transl_bind HoareYield_sandbox. f_equal. extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed. 

  Lemma HoareSpawn_hpI
      prog ginv' f fn args ktr
    :
    inline_hp prog (HoareSpawn ginv' f fn args >>= ktr)
    =
    x <- HoareSpawnE ginv' f fn args;; tau;; inline_hp prog (ktr x).
  Proof.
    unfold HoareSpawn, HoareSpawnE. ired.
    rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_sch. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_ag. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HoareYield_hpI. f_equal. 
  Qed.

  Lemma Spawn_Cancel_sandbox
      scopes fn args
    :
    HModSem.sandbox scopes (Spawn_Cancel fn args) = Spawn_Cancel fn args.
  Proof.
    unfold Spawn_Cancel.
    rewrite HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_sch. f_equal. extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed. 

  Lemma Spawn_Cancel_hpI
      prog fn args ktr
    :
    inline_hp prog (Spawn_Cancel fn args >>= ktr)
    =
    x <- Spawn_CancelE fn args;; tau;; inline_hp prog (ktr x).
  Proof.
    unfold Spawn_Cancel, Spawn_CancelE. ired.
    rewrite HIRed.bind_sch. f_equal. extensionalities. ired. do 2 f_equal.
    rewrite HIRed.bind_sch. f_equal.
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

  Ltac set_l := let IT := fresh "ITREE" in
    match goal with  
      | [|- gpaco3 _ _ _ _ _ ?it _] => set (IT := it)
      end; try unfold IT at 2.

  Ltac set_r := let IT := fresh "ITREE" in
    match goal with  
      | [|- gpaco3 _ _ _ _ _ _ ?it] => set (IT := it)
      end; try unfold IT at 2.

  Lemma elim_rel_refl
      sk0 scopes itr
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
    :
    @elim_rel _ ginv stb sk0 _ []
      (inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes (interp_smod_aux itr)))
      (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes (interp_smod (ginv sk0) (stb sk0) itr))).
  Proof. 
    unfold elim_rel.
    ginit. revert itr scopes. gcofix CIH. i.
    assert (CASE:= case_itrH _ itr). des; subst.
    - rewrite SModRed.interp_ret SAuxRed.ret HModSB.transl_ret !HIRed.ret.
      gstep. econs. 
    - rewrite SModRed.interp_tau SAuxRed.tau !HModSB.transl_tau !HIRed.tau.
      gstep; econs. gstep; econs. eauto with paco.
    - rewrite SModRed.interp_bind SModRed.interp_ag SAuxRed.bind SAuxRed.ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite !HIRed.bind_ag. gstep. econs. gstep. econs.
      rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite !HIRed.tau.
      gstep. econs. gstep. econs. eauto with paco. 
    - rewrite SModRed.interp_bind SModRed.interp_ag SAuxRed.bind SAuxRed.ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. 
      rewrite HModSB.transl_tau HModSB.transl_ret. ired. rewrite !HIRed.tau.  
      gstep. econs. gstep. econs. eauto with paco.
    - rewrite SModRed.interp_bind SModRed.interp_sch SAuxRed.bind SAuxRed.sch. ired. 
      unfold handle_schE_hmodE, handle_schE_hmodE_aux. depdes s.
      + destruct (stb sk0 fn) eqn:STB; ired; cycle 1.
        { 
          unfold triggerNB. ired. 
          rewrite !HModSB.transl_bind HModSB.transl_core. ired. 
          rewrite HIRed.bind_core. gstep. econs. 
        }
        do 2 rewrite HModSB.transl_bind.
        rewrite HoareSpawn_sandbox HoareSpawn_hpI. 
        rewrite Spawn_Cancel_sandbox Spawn_Cancel_hpI. ired.
        gstep. econs; eauto. i. gstep. econs. ired.
        rewrite !HModSB.transl_tau !HIRed.tau.
        gstep. econs. gstep. econs. eauto with paco.
      + do 2 rewrite HModSB.transl_bind. 
        rewrite HoareYield_sandbox HoareYield_hpI HModSB.transl_sch HIRed.bind_sch.
        gstep. econs. i. gstep. econs. ired.
        rewrite !HModSB.transl_tau !HIRed.tau.
        gstep. econs. gstep. econs. eauto with paco.
      + rewrite !HModSB.transl_bind HModSB.transl_sch !HIRed.bind_sch.
        gstep. econs. gstep. econs. ired.
        rewrite !HModSB.transl_tau !HIRed.tau.
        gstep. econs. gstep. econs. eauto with paco.
    - rewrite SModRed.interp_bind SModRed.interp_call SAuxRed.bind SAuxRed.call.
      unfold handle_callE_hmodE. depdes c. 
      destruct (stb sk0 fn) eqn: STB; ired; cycle 1.
      { 
        unfold triggerNB. 
        rewrite/__ !HModSB.transl_bind HModSB.transl_core. ired. 
        rewrite HIRed.bind_core. gstep. econs.
      }
      do 2 rewrite HModSB.transl_bind. 
      rewrite HModSB.transl_call HIRed.call HIRed.bind.
      
      assert (FIND := stb_in_alist_find).
      specialize (FIND sk0 fn f SKINCL SKWF STB). des.
      destruct (alist_find fn (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_aux ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))) eqn: FINDS; cycle 1.
      { exfalso. rewrite/__ alist_find_map_snd FIND in FINDS. clarify.  }
      ired. rewrite FINDS. destruct p. rewrite alist_find_map_snd FIND in FINDS. s in FINDS. inv FINDS. 
      ired. unfold HModSem.sandbox_body. s. 
      set_l. 
      eassert (ITREE = tau;; x <- (a <- inline_hp _ (HModSem.sandbox l0 (x <- _ args;; tau;; Ret x));; tau;; Ret a);; tau;; _).
      {
        unfold ITREE. do 2 f_equal. 
        instantiate (3:= prog (SModSemAux.to_hmod (SMod.modsem md sk0))).
        ired. rewrite HModSB.transl_bind HIRed.bind. ired. f_equal.  
        extensionalities. rewrite HModSB.transl_tau !HIRed.tau. ired.
        do 4 f_equal.
        rewrite HModSB.transl_ret HIRed.ret. ired.
        rewrite HModSB.transl_tau HIRed.tau. do 4 f_equal.
      }
      set_r.
      eassert (ITREE0 = x <- (a <- inline_hp _ _;; tau;; Ret a);; tau;; _ x).
      {
        instantiate (2:= HModSem.sandbox scopes (HoareCall f fn args)).
        instantiate (2:= prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))).
        rewrite /ITREE0 !HIRed.bind. ired. f_equal.
        extensionalities. ired. rewrite HModSB.transl_tau HIRed.tau.
        repeat f_equal. 
        instantiate (1:= fun x => inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
        (HModSem.sandbox scopes (interp_smod (ginv sk0) (stb sk0) (ktrH' x)))).
        s. refl.
      }
      rewrite H H0. clear ITREE ITREE0 H H0.

      rewrite -bind_tau. guclo elim_rel_bindC_spec.    
      eapply elim_rel_bindC_intro with (l1 := []).
      {
        erewrite HoareCall_inline; eauto.
        rewrite HModSB.transl_bind HIRed.bind.
        set (inline_hp _ _ ). eassert (i = _ args).
        { unfold i. instantiate (1:= fun x => inline_hp _ (_ (_ x))). refl. }
        remember (λ x : Any.t, inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) (HModSem.sandbox l0 (_ x))).
        rewrite H. clear i H.
        ired. gstep. econs. 
        { 
          instantiate (1:= fun args => a <- i0 args;; tau;; tau;; tau;; Ret a). s. 
          f_equal. extensionalities.
          rewrite HModSB.transl_tau HModSB.transl_ret HIRed.tau HIRed.ret.
          ired. refl. 
        }
        i. ired. 
        (* rewrite [i1 varg]add_dummy_ret. *)
        guclo elim_rel_bindC_spec.
        eapply elim_rel_bindC_intro with (l1 := []).
        { rewrite Heqi0. unfold interp_sb_hp_aux. s. eauto with paco. }
        i.
        set_r. eassert (ITREE = a <- hmod_elim_tail (meta f) (postcond f) (tid, m, tid', m') v;; (tau;; Ret a)).
        { unfold ITREE, hmod_elim_tail. refl. }
        rewrite H.
        gstep. econs.
        { instantiate (1:= fun x => Ret x). refl. }
        i. s. gstep. econs.
      }
      i. gstep. econs. eauto with paco.

    - depdes s.
      + rewrite SModRed.interp_bind SModRed.interp_pg SAuxRed.bind SAuxRed.pg. 
        rewrite !HModSB.transl_bind HModSB.transl_put. ired.
        des_ifs.
        * rewrite !HIRed.bind_pg.
          gstep. econs. i. gstep. econs.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired.
          rewrite !HIRed.tau.
          gstep. econs. i. gstep. econs. eauto with paco. 
        * rewrite !HIRed.bind_core.
          gstep. econs. i. gstep. econs.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired.
          rewrite !HIRed.tau.
          gstep. econs. i. gstep. econs. eauto with paco.  
      + rewrite SModRed.interp_bind SModRed.interp_pg SAuxRed.bind SAuxRed.pg. 
        rewrite !HModSB.transl_bind HModSB.transl_get. ired.
        des_ifs.
        * rewrite !HIRed.bind_pg.
          gstep. econs. i. gstep. econs.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired.
          rewrite !HIRed.tau.
          gstep. econs. i. gstep. econs. eauto with paco. 
        * rewrite !HIRed.bind_core.
          gstep. econs. i. gstep. econs.
          rewrite HModSB.transl_tau HModSB.transl_ret. ired.
          rewrite !HIRed.tau.
          gstep. econs. i. gstep. econs. eauto with paco.  
    - rewrite SModRed.interp_bind SModRed.interp_core SAuxRed.bind SAuxRed.core. ired. 
      rewrite !HModSB.transl_bind HModSB.transl_core !HIRed.bind_core. 
      gstep. econs. i. gstep. econs. ired. 
      rewrite !HModSB.transl_tau !HIRed.tau.
      gstep. econs. i. gstep. econs. eauto with paco.
  Qed.

End CANCEL.

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
      trigger (Guarantee (P X my_tid x varg arg));;; tau;; tau;;
      my_tid' <- trigger Tid;; tau;;
      x' <- trigger (Take X);; tau;;
      varg' <- trigger (Take _);; tau;;
      trigger (Assume (P X my_tid' x' varg' arg));;; tau;;
      Ret ((my_tid, x, my_tid', x'), varg').

  Definition hmod_elim_tail X Q : (nat * X * nat * X) -> Any.t -> itree hmodE Any.t
    :=
    fun '(my_tid, x, my_tid', x') vret' =>
      ret <- trigger (Choose Any.t);; tau;;
      trigger (Guarantee (Q X my_tid' x' vret' ret));;; tau;; tau;; tau;;
      vret <- trigger (Take Any.t);; tau;;
      trigger (Assume (Q X my_tid x vret ret));;; tau;;
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

  | elim_rel_core {R} l scp (e: coreE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) ((a <- trigger e;; HModSem.sandbox scp (tau;; Ret a)) >>= ktrT)

  | elim_rel_pg {R} l scp (e: pgE R) ktrS ktrT
      (KTR: forall (v: R), self l (ktrS v) (ktrT v))
    :
    elim_rel_def self l (trigger e >>= ktrS) ((a <- trigger e;; HModSem.sandbox scp (tau;; Ret a)) >>= ktrT)

  | elim_rel_asm P l scp ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Assume P) >>= ktrS) ((a <- trigger (Assume P);; HModSem.sandbox scp (tau;; Ret a)) >>= ktrT)

  | elim_rel_grt P l scp ktrS ktrT
      (KTR: self l (ktrS tt) (ktrT tt))
    :
    elim_rel_def self l (trigger (Guarantee P) >>= ktrS) ((a <- trigger (Guarantee P);; HModSem.sandbox scp (tau;; Ret a)) >>= ktrT)
  
  | elim_rel_tid l scp ktrS ktrT
      (KTR: forall (tid: nat), self l (ktrS tid) (ktrT tid))
    :
    elim_rel_def self l (trigger Tid >>= ktrS) ((a <- trigger Tid;; HModSem.sandbox scp (tau;; Ret a)) >>= ktrT)

  | elim_rel_head X P l varg ktrS ktrT
     (KTR: forall tid tid' m m' varg, 
            self ((tid, tid', existT X (m, m'))::l) (ktrS varg) (ktrT (tid, m, tid', m', varg)))
   :
   elim_rel_def self l (ktrS varg) ( '(tid, m, tid', m', varg') <- @hmod_elim_head X P varg;; ktrT (tid, m, tid', m', varg')) 
  
  | elim_rel_tail X Q l tid m tid' m' vret ktrS ktrT
      (KTR: forall vret, self l (ktrS vret) (ktrT vret))
    :
    elim_rel_def self ((tid, tid', existT X (m, m'))::l)
        (ktrS vret) 
        (vret' <- (@hmod_elim_tail X Q (tid, m, tid', m') vret);; (tau;; tau;; ktrT vret'))

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
                        (x <- HoareYieldE (ginv sk0) tid;; (tau;; ktrT x))
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
      (RELK: ∀vs vt, r l (ktrS vs) (ktrT vt))
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

  Lemma elim_rel_bindC_wrespectful {sk0 A}:
    wrespectful3 (@elim_rel_def sk0 A) elim_rel_bindC.
  Proof.













    (* econs; eauto using elim_rel_bindC_mon. i.
    destruct PR. apply GF in REL.
    revert_until REL.
    pattern itrS, itrT. inv REL.
    - grind. econs.
    - grind. eapply elim_rel_def_mon.
      { i. econs. eauto. }
      eapply GF; eauto.
    - grind. econs. econs. *)



(* 
  Variant elim_rel_def {sk0 A} 
    (self: forall I, (I -> itree hmodE A) -> (I -> list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A) -> Prop)
    : forall I, (I -> itree hmodE A) -> (I -> list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A) -> Prop
  :=
  | elim_rel_NB I ktrS ktrT
    :
    elim_rel_def self I ktrS (fun i l => trigger (Choose False) >>= (ktrT i l))
  
  | elim_rel_base I r 
    :
    elim_rel_def self I (fun i => Ret (r i)) (fun i _ => Ret (r i))
    
  | elim_rel_tau I ktrS ktrT
      (KTR: self I ktrS ktrT)
    :
    elim_rel_def self _ (fun i => tau;; ktrS i) (fun i l => tau;; (ktrT i l))
  
  | elim_rel_core {I R} (e: I -> coreE R) ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self _ (fun i => a <- trigger (e i);; ktrS (i, a)) (fun i l => a <- trigger (e i);; tau;; ktrT (i, a) l)
  
  | elim_rel_pg {I R} (e: I -> pgE R) ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger (e i);; ktrS (i, a)) (fun i l => a <- trigger (e i);; tau;; ktrT (i, a) l)
  
  | elim_rel_asm I P ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger (Assume (P i));; ktrS (i, a)) (fun i l => a <- trigger (Assume (P i));; tau;; ktrT (i, a) l)
  
  | elim_rel_grt I P ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger (Guarantee (P i));; ktrS (i, a)) (fun i l => a <- trigger (Guarantee (P i));; tau;; ktrT (i, a) l)
  
  | elim_rel_tid I ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger Tid;; ktrS (i, a)) (fun i l => a <- trigger Tid;; tau;; ktrT (i, a) l)
  
  | elim_rel_spawn I fn args ktrS ktrT ktrT'
      (* (SKINCL: incl sk sk0) *)
      (* (SKWF: Sk.wf sk0) *)
      (* (STB: stb sk0 fn = Some f) *)
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger (Spawn (fn i) (args i));; ktrS (i, a)) 
    (fun i l => 
      match (stb sk0 (fn i)) with
      | None => a <- trigger (Choose False);; ktrT' (i, a) l
      | Some f => a <- HoareSpawnE (ginv sk0) f (fn i) (args i);; tau;; ktrT (i, a) l
      end)

  | elim_rel_yield I tid ktrS ktrT
      (* (SKINCL: incl sk sk0) *)
      (* (SKWF: Sk.wf sk0) *)
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self I (fun i => a <- trigger (Yield (tid i));; ktrS (i, a)) (fun i l => a <- HoareYieldE (ginv sk0) (tid i);; tau;; ktrT (i, a) l)

  | elim_rel_head X P ktrS ktrT
     (KTR: self _ ktrS ktrT)
   :
   elim_rel_def self Any.t (fun varg => ktrS varg) (fun varg l => '(tid, m, tid', m', varg') <- @hmod_elim_head X P varg;; ktrT varg' ((tid, tid', existT X (m, m'))::l))
  
  | elim_rel_tail Q a ktrS ktrT
      (KTR: self _ ktrS ktrT)
    :
    elim_rel_def self Any.t (fun vret => ktrS vret) 
    (fun vret l => 
      match l with
      | [] => trigger (Choose False);;; Ret a
      | (tid, tid', existT X (m, m'))::tl => vret' <- @hmod_elim_tail X Q (tid, m, tid', m') vret;; tau;; tau;; ktrT vret' tl
      end)
  . *)

    (* Variant elim_rel_def {sk0 A}
    (self: itree hmodE A -> (list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A) -> Prop)
    : itree hmodE A -> (list (nat * nat * {X: Type & (X * X)%type}) -> itree hmodE A) -> Prop
  :=
  | elim_rel_NB itrS ktrT
    :
    elim_rel_def self itrS (fun l => trigger (Choose False) >>= (ktrT l))
  
  | elim_rel_base v
    :
    elim_rel_def self (Ret v) (fun _ => Ret v)

  | elim_rel_tau itrS ktrT
      (KTR: self itrS ktrT)
    :
    elim_rel_def self (tau;; itrS) (fun l => tau;; (ktrT l))
  
  | elim_rel_core {R} (e: coreE R) ktrS ktrT
      (KTR: forall (v: R), self (ktrS v) (ktrT v))
    :
    elim_rel_def self (trigger e >>= ktrS) (fun l => a <- trigger e;; tau;; ktrT a l)
  
  | elim_rel_pg {R} (e: pgE R) ktrS ktrT
      (KTR: forall (v: R), self (ktrS v) (ktrT v))
    :
    elim_rel_def self (trigger e >>= ktrS) (fun l => a <- trigger e;; tau;; ktrT a l)

  | elim_rel_asm P ktrS ktrT
      (KTR: self (ktrS tt) (ktrT tt))
    :
    elim_rel_def self (trigger (Assume P) >>= ktrS) (fun l => a <- trigger (Assume P);; tau;; ktrT a l)

  | elim_rel_grt P ktrS ktrT
      (KTR: self (ktrS tt) (ktrT tt))
    :
    elim_rel_def self (trigger (Guarantee P) >>= ktrS) (fun l => a <- trigger (Guarantee P);; tau;; ktrT a l)
  
  | elim_rel_tid ktrS ktrT
      (KTR: forall (tid: nat), self (ktrS tid) (ktrT tid))
    :
    elim_rel_def self (trigger Tid >>= ktrS) (fun l => a <- trigger Tid;; tau;; ktrT a l)

  | elim_rel_spawn f fn args ktrS ktrT
      (STB: stb sk0 fn = Some f)
      (KTR: forall x, self (ktrS x) (ktrT x))
    :
    elim_rel_def self (trigger (Spawn fn args) >>= ktrS) 
    (fun l => x <- HoareSpawnE (ginv sk0) f fn args;; tau;; ktrT x l)

  | elim_rel_yield tid ktrS ktrT
      (KTR: forall x, self (ktrS x) (ktrT x))
    :
    elim_rel_def self (trigger (Yield tid) >>= ktrS) 
    (fun l => x <- HoareYieldE (ginv sk0) tid;; tau;; ktrT x l)

  | elim_rel_head X P varg ktrS ktrT
     (KTR: forall varg, self (ktrS varg) (fun l => ktrT varg l))
   :
   elim_rel_def self (ktrS varg) 
   (fun l => '(tid, m, tid', m', varg') <- 
      @hmod_elim_head X P varg;; ktrT varg' ((tid, tid', existT X (m, m'))::l))
  
  | elim_rel_tail Q vret ktrS ktrT ktrT0 X x
      (KTR: forall vret, self (ktrS vret) (ktrT vret))
    :
    elim_rel_def self (ktrS vret) 
    (fun l => 
      match l with
      | [] => vret' <- @hmod_elim_tail X Q x vret;; tau;; tau;; ktrT0 vret' l
      | (tid, tid', existT X (m, m'))::tl => vret' <- @hmod_elim_tail X Q (tid, m, tid', m') vret;; tau;; tau;; ktrT vret' tl
      end)
  .

  Definition elim_rel {sk0 A} :=
    paco2 (@elim_rel_def sk0 A) bot2.

  Definition thread_local_rel {sk0} itrS itrT : Prop :=
    @elim_rel sk0 Any.t itrS 
    (fun l => 
      match l with 
      | [] => itrT
      | hd::tl => trigger (Choose False);;; Ret tt↑
      end).   *)

   
  
  
  (* Variant elim_rel_def
    (self: forall X Y (RR: X -> Y -> Prop), bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop)
    {X Y}
    (RR: X -> Y -> Prop)
    (reli: bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop)
    : bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop
  :=
  | elim_rel_base v0 v1 ps pt
    (RET: RR v0 v1)
    :
    elim_rel_def self RR reli ps pt (Ret v0) (Ret v1)

  | elim_rel_tau_src ps pt itrS itrT
      (ITR: reli true pt itrS itrT)
    :
    elim_rel_def self RR reli ps pt (tau;; itrS) (itrT)

  | elim_rel_tau_tgt ps pt itrS itrT
      (ITR: reli ps true itrS itrT)
    :
    elim_rel_def self RR reli ps pt (itrS) (tau;; itrT)

  | elim_rel_asm P ps pt ktrS ktrT
      (KTR: reli true true (ktrS tt) (ktrT tt))
    :
    elim_rel_def self RR reli ps pt (trigger (Assume P) >>= ktrS) (trigger (Assume P) >>= ktrT)

  | elim_rel_grt P ps pt ktrS ktrT
      (KTR: reli true true (ktrS tt) (ktrT tt))
    :
    elim_rel_def self RR reli ps pt (trigger (Guarantee P) >>= ktrS) (trigger (Guarantee P) >>= ktrT)

  | elim_rel_pg {R} ps pt (e: pgE R) ktrS ktrT
      (KTR: forall (v: R), reli true true (ktrS v) (ktrT v))
    :
    elim_rel_def self RR reli ps pt (trigger e >>= ktrS) (trigger e >>= ktrT)
  
  | elim_rel_core {R} ps pt (e: coreE R) ktrS ktrT
      (KTR: forall (v: R), reli true true (ktrS v) (ktrT v))
    :
    elim_rel_def self RR reli ps pt (trigger e >>= ktrS) (trigger e >>= ktrT)

  | elim_rel_tid ps pt ktrS ktrT
      (KTR: forall (tid: nat), reli true true (ktrS tid) (ktrT tid))
    :
    elim_rel_def self RR reli ps pt (trigger Tid >>= ktrS) (trigger Tid >>= ktrT)

  | elim_rel_head X P ps pt v src tgt ktrS ktrT
      (KTR: forall m, reli true true (ktrS v) (ktrT (m, v)))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_head X P v) >>= ktrT)
    :
    elim_rel_def self RR reli ps pt src tgt
                  
  | elim_rel_tail X Q m v ps pt src tgt ktrS ktrT
      (KTR: reli true true (ktrS v) (ktrT v))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_tail X Q m v) >>= ktrT)
    :
    elim_rel_def self RR reli ps pt src tgt

  | elim_rel_NB
      ps pt src tgt itrS ktrT
      (EQS: src = itrS)
      (EQT: tgt = trigger (Choose False) >>= ktrT)
    :
    elim_rel_def self RR reli ps pt src tgt

   | elim_rel_spawn
      sk0 ps pt src tgt f fn args ktrS ktrT
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
      (STB: stb sk0 fn = Some f)
      (KTR: forall x, reli true true (ktrS x) (ktrT x))
      (EQS: src =  trigger (Spawn fn args) >>= ktrS)
      (EQT: tgt = HoareSpawnE (ginv sk0) f fn args >>= ktrT)
    :
    elim_rel_def self RR reli ps pt src tgt

  | elim_rel_yield
      sk0 tid ps pt src tgt ktrS ktrT
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
      (KTR: forall x, reli true true (ktrS x) (ktrT x))
      (EQS: src = trigger (Yield tid) >>= ktrS)
      (EQT: tgt = HoareYieldE (ginv sk0) tid >>= ktrT)
    :
    elim_rel_def self RR reli ps pt src tgt

  | elim_rel_progress
      src tgt
      (REL: self X Y RR false false src tgt)
    :
    elim_rel_def self RR reli true true src tgt 
  . *)
  
  Inductive _elim_rel self {X Y} RR ps pt src tgt: Prop :=
  | _elim_rel_intro (SAT: @elim_rel_def self X Y RR (_elim_rel self RR) ps pt src tgt).

  Definition elim_rel: forall X Y (RR: X -> Y -> Prop),  bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop :=
     paco7 _elim_rel bot7.

  Lemma elim_rel_def_mon self self' X Y RR P P'
    (self: self <7= self')
    (RELI: P <4= P')
  :
  @elim_rel_def self X Y RR P <4= elim_rel_def self' RR P'.
  Proof.
    i. destruct PR; eauto using @elim_rel_def.
  Qed.

  Lemma elim_rel_tarski elim_rel 
      X Y RR
      P
      (REL: @elim_rel_def elim_rel X Y RR P <4= P)
    :
    _elim_rel elim_rel RR <4= P.
  Proof.
    fix IH 5. i. inv PR. 
    inv SAT; eapply REL; try (econs; i; eapply IH; eauto).
    - econs; eauto.
    - econs; try refl. i. eapply IH. eauto.
    - econs 10; eauto. 
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto.  
    - econs 14; eauto.  
  Qed. 

  Lemma _elim_rel_mon : monotone7 _elim_rel.
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
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto.
    - econs 14; eauto.  
  Qed.

  Hint Resolve cpn7_wcompat: paco.
  Hint Resolve _elim_rel_mon: paco.
  Hint Resolve elim_rel_def_mon: paco.

  Definition elim_rel_indC elim_rel {X Y} RR :=
    @elim_rel_def bot7 X Y RR (elim_rel X Y RR).
  
  Lemma elim_rel_indC_mon: monotone7 elim_rel_indC.
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
    - econs 10; eauto.
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto.
    - econs 14; eauto.  
  Qed.

  Hint Resolve elim_rel_indC_mon: paco.

  Lemma elim_rel_indC_spec:
    elim_rel_indC <8= gupaco7 _elim_rel (cpn7 _elim_rel).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs.
    - econs; eauto.
    - econs; eauto. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 6; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 7; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 8; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 9; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 10; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 11; eauto. 
    - econs 12; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - econs 13; eauto. i. eapply _elim_rel_mon; eauto. i. econs; eauto.
    - ss.
  Qed.

  Lemma _elim_rel_flag_mon X Y RR r (ps pt ps' pt': bool) src tgt
    (REL: @_elim_rel r X Y RR ps pt src tgt)
    (LES: ps -> ps')
    (LET: pt -> pt')
    :
    @_elim_rel r X Y RR ps' pt' src tgt.
  Proof.
    move REL before r. revert_until REL.
    pattern ps, pt, src, tgt. eapply elim_rel_tarski, REL.
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
    - econs 10; eauto.
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto.
    - hexploit LES; eauto. i. hexploit LET; eauto. i.  
      destruct ps', pt'; try discriminate.
      econs 14; eauto.
  Qed.

  Lemma elim_rel_flag_mon X Y RR (ps pt ps' pt': bool) src tgt
      (REL: @elim_rel X Y RR ps pt src tgt)
      (LES: ps -> ps')
      (LET: pt -> pt')
    :
    elim_rel X Y RR ps' pt' src tgt.
  Proof.
    move REL before Y. revert_until REL. pcofix CIH. i.
    pstep. eapply _elim_rel_flag_mon; eauto.
    eapply paco7_mon_bot in REL; eauto. punfold REL.
  Qed. 

  Variant elim_rel_flagC
    (r: forall X Y (RR: X -> Y -> Prop) , bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop)
    X Y RR ps pt src tgt : Prop := 
  | elim_rel_flagC_intro
    ps0 pt0
    (REL: r X Y RR ps0 pt0 src tgt)
    (SRC: ps0 = true -> ps = true)
    (TGT: pt0 = true -> pt = true)
  .

  Lemma elim_rel_flagC_mon r1 r2 (LE: r1 <7= r2) :
    elim_rel_flagC r1 <7= elim_rel_flagC r2.
  Proof.
    ii. destruct PR; econs; eauto.
  Qed.

  Hint Resolve elim_rel_flagC_mon.

  Lemma elim_rel_flagC_spec:
    elim_rel_flagC <8= gupaco7 _elim_rel (cpn7 _elim_rel).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply _elim_rel_flag_mon; eauto.
    eapply _elim_rel_mon. 2: { i. econs. eauto. }
    eapply GF; eauto.
  Qed. 

  Variant elim_rel_bindC
    (r: forall X Y (RR: X -> Y -> Prop), bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop)
    : forall X Y (RR: X -> Y -> Prop), bool -> bool -> itree hmodE X -> itree hmodE Y -> Prop
    :=
  | elim_rel_bindC_intro
      Q0 Q1 QQ ps pt i_src i_tgt
      (REL: r Q0 Q1 QQ ps pt i_src i_tgt)

      X Y RR k_src k_tgt
      (RELK: ∀vs vt (EQ: QQ vs vt), r X Y RR false false (k_src vs) (k_tgt vt))
    :
    elim_rel_bindC r X Y RR ps pt (i_src >>= k_src) (i_tgt >>= k_tgt)
  .

  Lemma elim_rel_bindC_mon
        r1 r2 
        (LEr: r1 <7= r2)
    :
    elim_rel_bindC r1 <7= elim_rel_bindC r2
  .
  Proof.
    ii. destruct PR; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_wrespectful:
    wrespectful7 _elim_rel elim_rel_bindC.
  Proof.
    econs; eauto using elim_rel_bindC_mon. i.
    destruct PR. apply GF in REL.
    move REL before GF. revert_until REL.
    pattern ps, pt, i_src, i_tgt.
    eapply elim_rel_tarski, REL. i. 
    inv PR; grind. 
    (* eauto 7 using elim_rel_mon, elim_rel_def, rclo3. *)
    - eapply _elim_rel_mon; cycle 1.
      { i. econs. eauto. }
      eapply _elim_rel_flag_mon; eauto; discriminate.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs. eauto.
    - econs. econs 9; eauto; cycle 1.
      { instantiate (1 := fun _v => _). refl.  }
      s; eauto.
    - econs. econs 10; eauto; cycle 1.
      { instantiate (1 := fun _v => _). refl.  }
      s; eauto.
    - econs. econs 11; eauto. 
    - econs. econs 12; eauto. i. s. eauto. 
    - econs. econs 13; eauto. i. s. eauto.
    - econs. econs 14; eauto. 
      econs 2; eauto. econs; i; econs; eauto.
  Qed.

  Lemma elim_rel_bindC_spec:
    elim_rel_bindC <8= gupaco7 _elim_rel (cpn7 _elim_rel).
  Proof.
    i. eapply wrespect7_uclo; eauto with paco. eapply elim_rel_bindC_wrespectful.
  Qed.

End REL.

Hint Resolve cpn7_wcompat: paco.
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
      sk0 scopes ps pt itr
      (SKINCL: incl sk sk0)
      (SKWF: Sk.wf sk0)
    :
    elim_rel ginv stb md _ _ eq ps pt
      (inline_hp (prog (SModSemAux.to_hmod (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes itr))
      (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
          (HModSem.sandbox scopes (interp_smod (ginv sk0) (stb sk0) itr))).
  Proof. 
    unfold elim_rel.
    ginit. revert ps pt itr scopes. gcofix CIH. i.
    assert (CASE:= case_itrH _ itr). des; subst.
    - rewrite/__ SModRed.interp_ret HModSB.transl_ret !HIRed.ret.
      gstep. econs. econs; eauto.
    - rewrite/__ SModRed.interp_tau !HModSB.transl_tau !HIRed.tau.
      gstep. do 9 econs. econs 14. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite/__ !HIRed.bind_ag. gstep. do 6 econs.  
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_ag !HModSB.transl_bind HModSB.transl_ag. ired.
      rewrite/__ !HIRed.bind_ag. gstep. do 6 econs. 
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_sch !HModSB.transl_bind HModSB.transl_sch. ired.
      unfold handle_schE_hmodE. depdes s.
      + destruct (stb sk0 fn) eqn:STB; ired; cycle 1.
        { 
          unfold triggerNB. ired. 
          rewrite/__ HModSB.transl_bind HModSB.transl_core. ired. 
          rewrite HIRed.bind_core. gstep. econs. econs 11; ss.
        }
        rewrite/__ HoareSpawn_sandbox HoareSpawn_hpI HIRed.bind_sch.
        gstep. econs. econs 12; eauto. i. s. econs. econs. 
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
        rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
      + rewrite/__ HoareYield_sandbox HoareYield_hpI HIRed.bind_sch.
        gstep. econs. econs 13; eauto. i. s.
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
        rewrite HIRed.tau. do 9 econs. econs 14. gbase. eapply CIH; eauto.
      + rewrite/__ HModSB.transl_sch !HIRed.bind_sch.
        gstep. do 6 econs.
        rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired.
        rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_call.
      unfold handle_callE_hmodE. depdes c. 
      destruct (stb sk0 fn) eqn: STB; ired; cycle 1.
      { 
        unfold triggerNB. 
        rewrite/__ !HModSB.transl_bind HModSB.transl_core. ired. 
        rewrite HIRed.bind_core. gstep. econs. econs 11; ss.
      }
      do 2 rewrite HModSB.transl_bind. 
      rewrite/__ HModSB.transl_call HIRed.call HIRed.bind.
      guclo elim_rel_indC_spec. econs. s.
      assert (FIND := stb_in_alist_find).
      specialize (FIND sk0 fn f SKINCL SKWF STB). des.
      destruct (alist_find fn (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, fsb_body ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))) eqn: FINDS; cycle 1.
      { exfalso. rewrite/__ alist_find_map_snd FIND in FINDS. clarify.  }
      ired. destruct p. rewrite/__ alist_find_map_snd FIND in FINDS. s in FINDS. inv FINDS.
      unfold HModSem.sandbox_body. s. rewrite HIRed.bind. 
      erewrite HoareCall_inline2; eauto. 
      rewrite bind_bind. guclo elim_rel_bindC_spec. econs.
      {
        instantiate (1:= fun vs vt => vs = vt.2).
        unfold elim_head_body. guclo elim_rel_indC_spec. econs 9; swap 1 3.
        { f_equal. }
        { instantiate (1:= fun _ => _). refl. }
        grind. rewrite/__ [inline_hp _ _]add_dummy_ret. 
        guclo elim_rel_bindC_spec. econs.
        { gstep. econs. econs 14. gbase. eapply CIH; ss. }
        i. gstep. econs. econs. ss.
      }
      i. guclo elim_rel_indC_spec.
      destruct vt, p, p, p.
      
      set (hmod_elim_tail _ _ _ _ >>= _).
      eassert (i0 = hmod_elim_tail _ _ _ _ >>= (fun _ => tau;; tau;; _)).
      {
        unfold i0. f_equal. extensionalities.
        ired. rewrite HModSB.transl_tau HIRed.tau.
        f_equal.
      } 
      rewrite H. 
      (* Should have "vs = t" in here, lost in bindC *)
      econs 10; swap 1 3.
      { f_equal. }
      { refl. }
      i. ired. rewrite/__ HModSB.transl_tau !HIRed.tau. 
      gstep. do 9 econs. econs 14. gbase. ss. subst. eapply CIH; eauto.
    - depdes s.
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_put. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
        * rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
      + rewrite/__ SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_get. ired.
        des_ifs.
        * rewrite/__ !HIRed.bind_pg. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
        * rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
          rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
          rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
    - rewrite/__ SModRed.interp_bind SModRed.interp_core !HModSB.transl_bind HModSB.transl_core. ired.
      rewrite/__ !HIRed.bind_core. gstep. do 6 econs.  
      rewrite/__ HModSB.transl_tau HModSB.transl_ret. ired. 
      rewrite HIRed.tau. do 5 econs. econs 14. gbase. eapply CIH; eauto.
  Qed.

End CANCEL.
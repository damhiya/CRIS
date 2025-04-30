Require Import Common Sp.
Require Import SMod HMod SModTr.
Require Import SModCancel HModInline.

Definition sp_from `{Σ: GRA} md : string -> option fspec :=
  to_sp (List.map (map_snd (fsb_fspec ∘ snd)) md.(SMod.fnsems)).

Lemma sp_in_alist_find `{Σ: GRA} md
      fn fsp
      (SOME: sp_from md fn = Some fsp)
    :
    exists l fbody, 
      alist_find fn (SMod.fnsems md)
      = Some (l, {|fsb_fspec :=fsp; fsb_body := fbody|}).
Proof.
  unfold sp_from, to_sp in *. rewrite alist_find_map in SOME.
  destruct (alist_find fn _) eqn: FIND; ss.
  inv SOME. destruct p. destruct f. s. eauto.
Qed.

Definition hmod_elim_head `{Σ: GRA} X P : Any.t -> itree hmodE ((X * X) * Any.t)
  :=
  fun varg =>
    x <- trigger (Choose X);; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (P x varg arg));;; tau;; tau;;
    x' <- trigger (Take X);; tau;;
    varg' <- trigger (Take _);; tau;;
    trigger (Assume (P x' varg' arg));;; tau;;
    Ret ((x, x'), varg').

Definition hmod_elim_tail `{Σ: GRA} X Q : (X * X) -> Any.t -> itree hmodE Any.t
  :=
  fun '(x, x') vret' =>
    ret <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (Q x' vret' ret));;; tau;; tau;; tau;;
    vret <- trigger (Take Any.t);; tau;;
    trigger (Assume (Q x vret ret));;; tau;;
    Ret vret.
    
Definition HoareYieldE `{Σ: GRA} (tid: nat) : itree hmodE unit :=
  trigger (Yield tid).

Definition HoareSpawnE `{Σ: GRA} (fsp: fspec) (fn: string) (varg: Any.t) : itree hmodE nat :=
  x <- trigger (Choose fsp.(meta));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  tid <- trigger (Spawn fn arg);; tau;;
  trigger (Guarantee (fsp.(precond) x varg arg));;; tau;;
  HoareYieldE tid;;;
  Ret tid.

Definition SpawnCancelE `{Σ: GRA} (fn: string) (varg: Any.t) : itree hmodE nat :=
  tid <- trigger (Spawn fn varg);; tau;;
  trigger (Yield tid);;;
  Ret tid.

Variant elim_rel_def `{Σ: GRA} md {A}
  (self: list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop)
  : list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop
:=
| elim_rel_NB l itrS ktrT
  :
  elim_rel_def md self l itrS (trigger (Choose False) >>= ktrT)

| elim_rel_base v
  :
  elim_rel_def md self [] (Ret v) (Ret v)

| elim_rel_tau l itrS itrT
    (ITR: self l itrS itrT)
  :
  elim_rel_def md self l (tau;; itrS) (tau;; itrT)

| elim_rel_core {R} l (e: coreE R) ktrS ktrT
    (KTR: forall (v: R), self l (ktrS v) (ktrT v))
  :
  elim_rel_def md self l (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

| elim_rel_pg {R} l (e: pgE R) ktrS ktrT
    (KTR: forall (v: R), self l (ktrS v) (ktrT v))
  :
  elim_rel_def md self l (trigger e >>= ktrS) (a <- trigger e;; ktrT a)

| elim_rel_asm P l ktrS ktrT
    (KTR: self l (ktrS tt) (ktrT tt))
  :
  elim_rel_def md self l (trigger (Assume P) >>= ktrS) (a <- trigger (Assume P);; ktrT a)

| elim_rel_grt P l ktrS ktrT
    (KTR: self l (ktrS tt) (ktrT tt))
  :
  elim_rel_def md self l (trigger (Guarantee P) >>= ktrS) (a <- trigger (Guarantee P);; ktrT a)

| elim_rel_head X P l varg src ktrS ktrT
   (SRC: src = ktrS varg)
   (KTR: forall m varg,
          self ((existT X m)::l) (ktrS varg) (ktrT (m, m, varg)))
 :
 elim_rel_def md self l (tau;; src) (@hmod_elim_head _ X P varg >>= ktrT) 

| elim_rel_tail X Q l m vret src ktrS ktrT
    (SRC: src = ktrS vret)
    (KTR: forall vret, self l (ktrS vret) (ktrT vret))
  :
  elim_rel_def md self ((existT X m)::l)
      (tau;; tau;; src) 
      (x <- @hmod_elim_tail _ X Q (m, m) vret;; ktrT x)

| elim_rel_spawn l f fn args ktrS ktrT
    (STB: sp_from md fn = Some f)
    (KTR: forall x, self l (ktrS x) (ktrT x))
  :
  elim_rel_def md self l (SpawnCancelE fn args >>= ktrS)
                      (x <- HoareSpawnE f fn args;; ktrT x)

| elim_rel_yield tid l ktrS ktrT
    (KTR: forall x, self l (ktrS x) (ktrT x))
  :
  elim_rel_def md self l (trigger (Yield tid) >>= ktrS)
                      (x <- HoareYieldE tid;; ktrT x)
.

Definition elim_rel `{Σ: GRA} md {A} :=
  paco3 (@elim_rel_def _ md A) bot3.

Definition thread_local_rel `{Σ: GRA} md itrS itrT : Prop :=
  @elim_rel _ md Any.t [] itrS itrT.

Lemma elim_rel_def_mon `{Σ: GRA} md {A} r1 r2
  (REL: r1 <3= r2)
:
@elim_rel_def _ md A r1 <3= @elim_rel_def _ md A r2.
Proof.
  i. destruct PR; eauto using @elim_rel_def.
Qed.

Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Variant elim_rel_bindC `{Σ: GRA} {A}
  (r: list {X: Type & X } -> itree hmodE A -> itree hmodE A -> Prop)
  : list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop
  :=
| elim_rel_bindC_intro
    l1 l2 itrS itrT ktrS ktrT
    (REL: r l1 itrS itrT)
    (RELK: ∀v, r l2 (ktrS v) (ktrT v))
  :
  elim_rel_bindC r (l1++l2) (itrS >>= ktrS) (itrT >>= ktrT)
.

Lemma elim_rel_bindC_mon `{Σ: GRA} {A}:
  monotone3 (@elim_rel_bindC Σ A).
Proof.
  ii. destruct IN; econs; eauto.
Qed.

Local Opaque hmod_elim_tail.
Lemma elim_rel_bindC_spec `{Σ: GRA} md {A}:
  elim_rel_bindC <4= gupaco3 (@elim_rel_def _ md A) (cpn3 (@elim_rel_def _ md A)).
Proof.
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
    + f_equal.
Qed.
Transparent hmod_elim_tail.

Variant thread_rel `{Σ: GRA} md cid tid src tgt : Prop :=
| thread_rel_body X (meta: X) (Q: X -> Any.t -> Any.t -> iProp Σ) l itrS itrT
    (RET: ∀vret ret, 
          tid = 0 -> Q meta vret ret ⊢ ⌜vret = ret⌝)
    (REL: @elim_rel _ md _ l itrS itrT)
    (SRC: src =
            (if Nat.eq_dec tid cid then Ret tt else tau;; Ret tt);;;
            HModTr.trans itrS)
    (TGT: tgt =
            (if Nat.eq_dec tid cid then Ret tt else tau;; Ret tt);;;
            HModTr.trans
             (vret <- itrT;; 
              (inline_hp (prog (SMod.to_hmod (sp_from md) md))
               (ret <- trigger (Choose Any.t);;
                trigger (Guarantee (Q meta vret ret));;;
                Ret ret))))
.

(* CANCEL *)

Lemma HoareYield_sandbox `{Σ: GRA}
    scopes tid
  :
  HModTr.sandbox scopes (trigger (Yield tid)) = trigger (Yield tid).
Proof.
  rewrite SBRed.yield. eauto.
Qed. 

Lemma HoareYield_hpI `{Σ: GRA}
    prog tid ktr
  :
  inline_hp prog (trigger (Yield tid) >>= ktr)
  =
  x <- HoareYieldE tid;; tau;; inline_hp prog (ktr x).
Proof. 
  unfold HoareYieldE.
  rewrite HIRed.bind_yield. eauto.
Qed.

Lemma HoareSpawn_sandbox `{Σ: GRA}
    scopes f fn args
  :
  HModTr.sandbox scopes (SModTr.HoareSpawn f fn args) = SModTr.HoareSpawn f fn args.
Proof.
  unfold SModTr.HoareSpawn.
  rewrite SBRed.bind SBRed.core. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.core. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.spawn. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.ag. f_equal. extensionalities.
  rewrite SBRed.bind HoareYield_sandbox. f_equal. extensionalities.
  rewrite SBRed.ret. ss.
Qed.

Lemma HoareSpawn_hpI `{Σ: GRA}
    prog f fn args ktr
  :
  inline_hp prog (SModTr.HoareSpawn f fn args >>= ktr)
  =
  x <- HoareSpawnE f fn args;; tau;; inline_hp prog (ktr x).
Proof.
  unfold SModTr.HoareSpawn, HoareSpawnE. ired.
  rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_spawn. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_ag. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HoareYield_hpI. f_equal. 
Qed.

Lemma Spawn_cancel_sandbox `{Σ: GRA}
    scopes fn args
  :
  HModTr.sandbox scopes (SModCancel.HoareSpawn fn args) = SModCancel.HoareSpawn fn args.
Proof.
  unfold SModCancel.HoareSpawn.
  rewrite SBRed.bind SBRed.spawn. f_equal. extensionalities.
  rewrite SBRed.bind SBRed.yield. f_equal. extensionalities.
  rewrite SBRed.ret. ss.
Qed. 

Lemma Spawn_cancel_hpI `{Σ: GRA}
    prog fn args ktr
  :
  inline_hp prog (SModCancel.HoareSpawn fn args >>= ktr)
  =
  x <- SpawnCancelE fn args;; tau;; inline_hp prog (ktr x).
Proof.
  unfold SModCancel.HoareSpawn, SpawnCancelE. ired.
  rewrite HIRed.bind_spawn. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_yield. f_equal.
Qed.

Lemma HoareCall_inline_cancel `{Σ: GRA} md
  scopes fn varg sc fsp fbody 
  (FIND: alist_find fn (SMod.fnsems md) = Some (sc, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod (sp_from md) md)) (HModTr.sandbox scopes (SModTr.HoareCall fsp fn varg))
  =
  (* head *)
  m <- trigger (Choose (meta fsp));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (precond fsp m varg arg));;; tau;; tau;;
  m' <- trigger (Take (meta fsp));; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  trigger (Assume (precond fsp m' varg' arg));;; tau;; 
  (* body *)
  vret' <- inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
                     (HModTr.sandbox sc (SModTr.trans (sp_from md) (fbody varg')));;
  (* tail *)
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (postcond fsp m' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  trigger (Assume (postcond fsp m vret ret));;; tau;;
  Ret vret.
Proof.
  unfold SModTr.HoareCall.
  (* head *)
  rewrite SBRed.bind SBRed.core HIRed.bind_core.
  f_equal. extensionality m. do 2 f_equal.
  rewrite SBRed.bind SBRed.core HIRed.bind_core.
  f_equal. extensionality arg. do 2 f_equal.
  rewrite SBRed.bind SBRed.ag HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.bind SBRed.call HIRed.call.
  do 2 f_equal. ired.
  rewrite alist_find_map_snd FIND. ired.
  unfold HModTr.sandbox_body, SModTr.trans_ktree, SModTr.HoareFun. s.
  rewrite SBRed.bind SBRed.core. ired. rewrite HIRed.bind_core.
  f_equal. extensionality m'. do 2 f_equal.
  rewrite SBRed.bind SBRed.core. ired. rewrite HIRed.bind_core.
  f_equal. extensionality varg'. do 2 f_equal.
  rewrite SBRed.bind SBRed.ag. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal. 
  (* body *)
  rewrite SBRed.bind. ired. rewrite HIRed.bind.
  f_equal. extensionality vret'.
  rewrite SBRed.bind SBRed.core. ired. rewrite HIRed.bind_core.
  f_equal. extensionality ret. do 2 f_equal. 
  rewrite SBRed.bind SBRed.ag. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret. ired. rewrite HIRed.tau.
  do 4 f_equal.
  rewrite SBRed.bind SBRed.core. ired. rewrite HIRed.bind_core.
  f_equal. extensionality vret. do 2 f_equal.
  rewrite SBRed.bind SBRed.ag. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret HIRed.ret. ss.
Qed.

Lemma HoareCall_inline `{Σ: GRA} md
  scopes fn varg sc fsp fbody 
  (FIND: alist_find fn (SMod.fnsems md) = Some (sc, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod  (sp_from md) md)) (HModTr.sandbox scopes (SModTr.HoareCall fsp fn varg))
  =
  (* head *)
  '((x, x'), varg'):_ <- (hmod_elim_head (meta fsp) (precond fsp) varg);;
  (* body *)
  vret' <- inline_hp (prog (SMod.to_hmod  (sp_from md) md)) 
                     (HModTr.sandbox sc (SModTr.trans (sp_from md) (fbody varg')));;
  (* tail *)
  hmod_elim_tail (meta fsp) (postcond fsp) (x, x') vret'. 
Proof.
  erewrite HoareCall_inline_cancel; eauto.
  unfold hmod_elim_head, hmod_elim_tail. ired. 
  repeat (f_equal; extensionalities; ired; repeat f_equal). 
Qed.

Definition elim_head_body `{Σ: GRA} md
  sc fsp fbody varg
  :=
  ('((x, x'), varg'):_ <- (hmod_elim_head (meta fsp) (precond fsp) varg);;
  (* body *)
  vret' <- inline_hp (prog (SMod.to_hmod  (sp_from md) md)) 
                     (HModTr.sandbox sc (SModTr.trans (sp_from md) (fbody varg')));;
  Ret ((x, x'), vret')).

Lemma HoareCall_inline2 `{Σ: GRA} md
  scopes fn varg sc fsp fbody 
  (FIND: alist_find fn (SMod.fnsems md) = Some (sc, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
    (HModTr.sandbox scopes (SModTr.HoareCall fsp fn varg))
  =
  (* head *)
  RET <- elim_head_body md sc fsp fbody varg;;
  (* tail *)
  (fun RET =>
    let '((x, x'), vret') := RET in
    hmod_elim_tail (meta fsp) (postcond fsp) (x, x') vret') RET. 
Proof.
  erewrite HoareCall_inline; eauto. unfold elim_head_body. grind.
Qed.

Lemma add_dummy_ret `{Σ: GRA} R (itr: itree hmodE R):
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

Lemma elim_rel_refl `{Σ: GRA} md
    scopes itr
  :
  @elim_rel _ md _ []
    (inline_hp (prog (SModCancel.to_hmod md)) 
        (HModTr.sandbox scopes (SModCancel.trans itr)))
    (inline_hp (prog (SMod.to_hmod  (sp_from md) md)) 
        (HModTr.sandbox scopes (SModTr.trans (sp_from md) itr))).
Proof. 
  unfold elim_rel.
  ginit. revert itr scopes. gcofix CIH. i.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite SRed.ret SCancelRed.ret SBRed.ret !HIRed.ret.
    gstep. econs. 
  - rewrite SRed.tau SCancelRed.tau !SBRed.tau !HIRed.tau.
    gstep; econs. gstep; econs. eauto with paco.
  - rewrite SRed.bind SRed.ag SCancelRed.bind SCancelRed.ag !SBRed.bind SBRed.ag. ired.
    rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. gbase. eauto.
  - rewrite SRed.bind SRed.ag SCancelRed.bind SCancelRed.ag !SBRed.bind SBRed.ag. ired.
    rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. gbase. eauto.
  - depdes c; s.
    {
      rewrite SRed.bind SRed.call SCancelRed.bind SCancelRed.call.
      destruct (sp_from md fn) eqn: STB; ired; cycle 1.
      {
        unfold triggerNB. ired.
        rewrite !SBRed.tau !HIRed.tau.
        gstep. econs. gstep. econs.
        rewrite !SBRed.bind. ired. rewrite SBRed.core HIRed.bind_core.
        gstep. econs.
      }
      do 2 rewrite SBRed.tau HIRed.tau. do 2 (gstep; econs).
      do 2 rewrite SBRed.bind.
      rewrite SBRed.call HIRed.call HIRed.bind.
      
      assert (FIND := sp_in_alist_find).
      specialize (FIND md fn f STB). des.
      destruct (alist_find fn (List.map (map_snd (λ ksb, (ksb.1, SModCancel.trans_ktree ksb.2))) (SMod.fnsems md))) eqn: FINDS; cycle 1.
      { exfalso. rewrite alist_find_map_snd FIND in FINDS. clarify. }
      ired. rewrite FINDS. destruct p as [sc bd].
      rewrite alist_find_map_snd FIND in FINDS. s in FINDS. inv FINDS.
      ired. unfold HModTr.sandbox_body. s.

      set_l. eassert (EQ: ITREE = x <- (tau;; x' <- _;; tau;; tau;; Ret x');; _).
      { unfold ITREE. erewrite bind_tau. do 2 eapply f_equal.
        erewrite bind_bind. eapply f_equal. extensionalities.
        rewrite HIRed.tau. erewrite !bind_tau.
        do 4 eapply f_equal. erewrite bind_ret_l.
        rewrite subst_bind. rewrite bind_ret_l. refl.
      }
      rewrite EQ. clear EQ ITREE.

      rewrite HIRed.bind. guclo elim_rel_bindC_spec.    
      eapply elim_rel_bindC_intro with (l1 := []); cycle 1.
      { i. gbase. eauto. }

      erewrite HoareCall_inline; eauto.
      gstep. econs.
      { instantiate (1:= fun args => (_ (_ (_ args))) >>=  _). refl. }
      i. s.
      
      guclo elim_rel_bindC_spec.
      eapply elim_rel_bindC_intro with (l1 := []).
      { unfold SModCancel.trans_ktree. s. gbase. eauto. }
      
      i. rewrite -(bind_ret_r (_ >>= _)).
      gstep. econs.
      + instantiate (1:= fun x => Ret x). refl.
      + i. gstep. econs.
    }
    {
      rewrite SRed.bind SRed.spawn SCancelRed.bind SCancelRed.spawn. ired.
      destruct (sp_from md fn) eqn:STB; ired; cycle 1.
      { 
        unfold triggerNB. ired.
        rewrite !SBRed.tau !HIRed.tau.
        gstep. econs. gstep. econs.
        rewrite !SBRed.bind. ired. rewrite SBRed.core HIRed.bind_core.
        gstep. econs.
      }
      do 2 rewrite SBRed.tau HIRed.tau. gstep. econs. gstep. econs.
      do 2 rewrite SBRed.bind. rewrite HoareSpawn_sandbox Spawn_cancel_sandbox.
      rewrite HoareSpawn_hpI Spawn_cancel_hpI.
      gstep. econs; eauto. i. gstep. econs. gbase. et.
    }
    {
      rewrite SRed.bind SRed.yield SCancelRed.bind SCancelRed.yield.
      rewrite !SBRed.bind !SBRed.yield !HIRed.bind_yield.
      gstep. econs; eauto. i. gstep. econs; eauto. gbase. eauto.
    }
  - depdes s.
    + rewrite SRed.bind SRed.pg SCancelRed.bind SCancelRed.pg. 
      rewrite !SBRed.bind SBRed.put. ired.
      des_ifs.
      * rewrite !HIRed.bind_pg.
        gstep. econs. i. gstep. econs. gbase. eauto.
      * unfold triggerUB; ired.
        rewrite !HIRed.bind_core.
        gstep. econs. i. ss.
    + rewrite SRed.bind SRed.pg SCancelRed.bind SCancelRed.pg. 
      rewrite !SBRed.bind SBRed.get. ired.
      des_ifs.
      * rewrite !HIRed.bind_pg.
        gstep. econs. i. gstep. econs. gbase. eauto.
      * unfold triggerUB; ired.
        rewrite !HIRed.bind_core.
        gstep. econs. i. ss.
  - rewrite SRed.bind SRed.core SCancelRed.bind SCancelRed.core. ired. 
    rewrite !SBRed.bind SBRed.core !HIRed.bind_core. 
    gstep. econs. i. gstep. econs. gbase. eauto.
(*SLOW*)Qed.

Require Import Common Sp.
Require Import SMod HMod SModTr.
Require Import HModInline.

Section ELIM_REL.

Context `{Σ: GRA}.

Definition sp_from (md: SMod.t) : string -> option fspec :=
  to_sp (List.map (map_snd (o2flat ∘ fst ∘ snd)) md.(SMod.fnsems)).

Definition valid_params (md: SMod.t) msk scp fspo : Prop :=
  (∃ img bd, SMod.initial_code md = Some2 (msk, scp, (img, bd)) ∧ fspo = SModTr.b2s img) ∨
  (∃ fn bd, alist_find fn (SMod.fnsems md) = Some (msk, scp, (fspo, bd))).

Definition has_none_spec (md: SMod.t) (fn: string) : Prop :=
  ∃ msk scp, valid_params md msk scp None ∧ msk fn.

Variant sp_wf md sp : Prop :=
  | sp_wf_intro
      (REAL: ∀ fn (NS: has_none_spec md fn), sp_from md fn = None)
      (WEAK: sp_weaker sp (sp_from md))
.

Definition hmod_elim_head X P : Any.t -> itree hmodE ((X * X) * Any.t)
  :=
  fun varg =>
    x <- trigger (Choose X);; tau;;
    arg <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (P x varg arg));;; tau;; tau;;
    x' <- trigger (Take X);; tau;;
    varg' <- trigger (Take _);; tau;;
    trigger (Assume (P x' varg' arg));;; tau;;
    Ret ((x, x'), varg').

Definition hmod_elim_tail X Q : (X * X) -> Any.t -> itree hmodE Any.t
  :=
  fun '(x, x') vret' =>
    ret <- trigger (Choose Any.t);; tau;;
    trigger (Guarantee (Q x' vret' ret));;; tau;; tau;; tau;;
    vret <- trigger (Take Any.t);; tau;;
    trigger (Assume (Q x vret ret));;; tau;;
    Ret vret.
    
Definition HoareSpawnE (fn: string) (varg: Any.t) (fsp: _fspec) : itree hmodE nat :=
  x <- trigger (Choose (_meta fsp));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  tid <- trigger (Spawn fn arg);; tau;;
  trigger (Guarantee (_precond fsp x varg arg));;; tau;;
  trigger (Yield tid);;;
  Ret tid.

Variant elim_rel_def md {A}
  (self: list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop)
  : list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop
:=
  
| elim_rel_NB l itrS ktrT
  :
  elim_rel_def md self l itrS (trigger (Choose False) >>= ktrT)

| elim_rel_UB l itrS ktrT
  :
  elim_rel_def md self l (trigger (Take False) >>= itrS) ktrT
               
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

| elim_rel_asm_precise P l ktrS ktrT
    (KTR: self l (ktrS tt) (ktrT tt))
  :
  elim_rel_def md self l (trigger (AssumePrecise P) >>= ktrS) (a <- trigger (AssumePrecise P);; ktrT a)
               
| elim_rel_grt P l ktrS ktrT
    (KTR: self l (ktrS tt) (ktrT tt))
  :
  elim_rel_def md self l (trigger (Guarantee P) >>= ktrS) (a <- trigger (Guarantee P);; ktrT a)

| elim_rel_head X P l varg src ktrS ktrT
   (SRC: src = ktrS varg)
   (KTR: forall m varg,
          self ((existT X m)::l) (ktrS varg) (ktrT (m, m, varg)))
 :
 elim_rel_def md self l (tau;; src) (@hmod_elim_head X P varg >>= ktrT) 

| elim_rel_tail X Q l m vret src ktrS ktrT
    (SRC: src = ktrS vret)
    (KTR: forall vret, self l (ktrS vret) (ktrT vret))
  :
  elim_rel_def md self ((existT X m)::l)
      (tau;; tau;; src) 
      (x <- @hmod_elim_tail X Q (m, m) vret;; ktrT x)

| elim_rel_spawn l fsp fn args ktrS ktrT
    (STB: sp_from md fn = Some (Some fsp))
    (KTR: forall x, self l (ktrS x) (ktrT x))
  :
  elim_rel_def md self l (SModTr.NativeSpawn fn args >>= ktrS)
                      (x <- HoareSpawnE fn args fsp;; ktrT x)

| elim_rel_yield tid l ktrS ktrT
    (KTR: forall x, self l (ktrS x) (ktrT x))
  :
  elim_rel_def md self l (trigger (Yield tid) >>= ktrS)
                      (x <- trigger (Yield tid);; ktrT x)
.

Definition elim_rel md {A} :=
  paco3 (@elim_rel_def md A) bot3.

Definition thread_local_rel md itrS itrT : Prop :=
  @elim_rel md Any.t [] itrS itrT.

Lemma elim_rel_def_mon md {A} r1 r2
  (REL: r1 <3= r2)
:
@elim_rel_def md A r1 <3= @elim_rel_def md A r2.
Proof.
  i. destruct PR; eauto using @elim_rel_def.
Qed.

Hint Resolve cpn3_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Variant elim_rel_bindC {A}
  (r: list {X: Type & X } -> itree hmodE A -> itree hmodE A -> Prop)
  : list {X: Type & X} -> itree hmodE A -> itree hmodE A -> Prop
  :=
| elim_rel_bindC_intro
    l l1 l2 itrS itrT ktrS ktrT
    (REL: r l1 itrS itrT)
    (RELK: ∀v, r l2 (ktrS v) (ktrT v))
    (LAPP: l = l1++l2)
  :
  elim_rel_bindC r l (itrS >>= ktrS) (itrT >>= ktrT)
.

Lemma elim_rel_bindC_mon {A}:
  monotone3 (@elim_rel_bindC A).
Proof.
  ii. destruct IN; econs; eauto.
Qed.

Local Opaque hmod_elim_tail.
Lemma elim_rel_bindC_spec md {A}:
  elim_rel_bindC <4= gupaco3 (@elim_rel_def md A) (cpn3 (@elim_rel_def md A)).
Proof.
  eapply wrespect3_uclo; eauto with paco.
  econs; [apply elim_rel_bindC_mon|].
  i. inv PR. apply GF in REL.
  inv REL; grind; eauto 7 using rclo3, elim_rel_def, elim_rel_bindC with paco.
  - econs.
    { instantiate (1:= fun varg => x <- ktrS0 varg;; ktrS x). eauto. }
    i. econs 2; cycle 1.
    + rewrite app_comm_cons. econs; try refl; try apply KTR; et.
    + eauto using rclo3.
  - eapply eq_ind.
    + eapply elim_rel_tail.
      { instantiate (2:= fun vret => x <- ktrS0 vret;; ktrS x). eauto. }
      i. s. econs 2; cycle 1.
      * econs; try refl; try apply KTR; et.
      * eauto using rclo3.
    + f_equal.
Qed.
Transparent hmod_elim_tail.

Variant thread_rel md tid src tgt : Prop :=
| thread_rel_body X (meta: X) (Q: X -> Any.t -> Any.t -> iProp Σ) l itrS itrT
    (RET: ∀vret ret, tid = 0 -> Q meta vret ret ⊢ ⌜vret = ret⌝)
    (REL: elim_rel md l itrS itrT)
    (SRC: src = HModTr.trans itrS)
    (TGT: tgt = HModTr.trans
                  (vret <- itrT;; 
                   (inline_hp (prog (SMod.to_hmod (sp_from md) md))
                      (ret <- trigger (Choose Any.t);;
                       trigger (Guarantee (Q meta vret ret));;;
                       Ret ret))))
.

(* CANCEL *)

Lemma HoareYield_sandbox `{Σ: GRA}
  img mask scopes tid
  :
  SB.sandbox img mask scopes (trigger (Yield tid)) = trigger (Yield tid).
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
  img mask scopes fn args fsp
  :
  SB.sandbox img mask scopes (SModTr.HoareSpawn fn args fsp) =
    if mask fn
    then SModTr.HoareSpawn fn args fsp
    else
      x <- trigger (Choose (_meta fsp));;
      arg <- trigger (Choose Any.t);;
      tid <- triggerUB;;
      trigger (Guarantee (_precond fsp x args arg));;;
      trigger (Yield tid);;;
      Ret tid.
Proof.
  unfold SModTr.HoareSpawn. des_ifs.
  - rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.spawn Heq. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
    rewrite SBRed.bind HoareYield_sandbox. f_equal. extensionalities.
    rewrite SBRed.ret. ss.
  - rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.choose. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.spawn Heq. f_equal. extensionalities.
    rewrite SBRed.bind SBRed.Guarantee. f_equal. extensionalities.
    rewrite SBRed.bind HoareYield_sandbox. f_equal. extensionalities.
    rewrite SBRed.ret. ss.
Qed. 

Lemma HoareSpawn_hpI `{Σ: GRA}
  prog fsp fn args ktr
  :
  inline_hp prog (SModTr.HoareSpawn fn args fsp >>= ktr)
  =
  x <- HoareSpawnE fn args fsp;; tau;; inline_hp prog (ktr x).
Proof.
  unfold SModTr.HoareSpawn, HoareSpawnE. ired.
  rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_core. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_spawn. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_ag. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HoareYield_hpI. f_equal. 
Qed.

Lemma Spawn_cancel_sandbox `{Σ: GRA}
  img mask scopes fn args
  :
  SB.sandbox img mask scopes (SModTr.NativeSpawn fn args) =
    if mask fn
    then SModTr.NativeSpawn fn args
    else tid <- triggerUB;;
         trigger (Yield tid);;;
         Ret tid.
Proof.
  unfold SModTr.NativeSpawn.
  rewrite SBRed.bind SBRed.spawn. des_ifs.
  - f_equal. extensionalities. rewrite SBRed.bind SBRed.yield SBRed.ret. et.
  - f_equal. extensionalities. rewrite SBRed.bind SBRed.yield SBRed.ret. et.
Qed.

Lemma Spawn_cancel_hpI `{Σ: GRA}
  prog fn args ktr
  :
  inline_hp prog (SModTr.NativeSpawn fn args >>= ktr)
  =
  x <- SpawnCancelE fn args;; tau;; inline_hp prog (ktr x).
Proof.
  unfold SModTr.NativeSpawn, SpawnCancelE. ired.
  rewrite HIRed.bind_spawn. f_equal. extensionalities. ired. do 2 f_equal.
  rewrite HIRed.bind_yield. f_equal.
Qed.

Lemma HoareCall_inline_cancel md
  (mask:_→bool) scopes fn varg msk sc fsp fbody
  (IN: mask fn)
  (FIND: alist_find fn (SMod.fnsems md) = Some (msk, sc, {|fsb_fspec := Some fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod (sp_from md) md)) (SB.sandbox true mask scopes (SModTr.HoareCall fn varg fsp))
  =
  (* head *)
  m <- trigger (Choose (_meta fsp));; tau;;
  arg <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (_precond fsp m varg arg));;; tau;; tau;;
  m' <- trigger (Take (_meta fsp));; tau;;
  varg' <- trigger (Take Any.t);; tau;;
  trigger (Assume (_precond fsp m' varg' arg));;; tau;; 
  (* body *)
  vret' <- inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
                     (SB.sandbox true msk sc (SModTr.trans (sp_from md) (fbody varg')));;
  (* tail *)
  ret <- trigger (Choose Any.t);; tau;;
  trigger (Guarantee (_postcond fsp m' vret' ret));;; tau;; tau;; tau;;
  vret <- trigger (Take Any.t);; tau;;
  trigger (Assume (_postcond fsp m vret ret));;; tau;;
  Ret vret.
Proof.
  unfold SModTr.HoareCall.
  (* head *)
  rewrite SBRed.bind SBRed.choose HIRed.bind_core.
  f_equal. extensionality m. do 2 f_equal.
  rewrite SBRed.bind SBRed.choose HIRed.bind_core.
  f_equal. extensionality arg. do 2 f_equal.
  rewrite SBRed.bind SBRed.Guarantee HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.bind SBRed.call. des_ifs. rewrite HIRed.call.
  do 2 f_equal. ired. rewrite alist_find_map_snd FIND. ired.
  unfold SB.sandbox_body, SModTr.trans_ktree, SModTr.HoareFun. s.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.bind_core.
  f_equal. extensionality m'. do 2 f_equal.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.bind_core.
  f_equal. extensionality varg'. do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal. 
  (* body *)
  rewrite SBRed.bind. ired. rewrite HIRed.bind.
  f_equal. extensionality vret'.
  rewrite SBRed.bind SBRed.choose. ired. rewrite HIRed.bind_core.
  f_equal. extensionality ret. do 2 f_equal. 
  rewrite SBRed.bind SBRed.Guarantee. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret. ired. rewrite HIRed.tau.
  do 4 f_equal.
  rewrite SBRed.bind SBRed.take. s. ired. rewrite HIRed.bind_core.
  f_equal. extensionality vret. do 2 f_equal.
  rewrite SBRed.bind SBRed.Assume. ired. rewrite HIRed.bind_ag.
  f_equal. extensionalities. do 2 f_equal.
  rewrite SBRed.ret HIRed.ret. ss.
Qed.

Lemma HoareCall_inline md
  (mask:_→bool) scopes fn varg msk sc fsp fbody
  (IN: mask fn)
  (FIND: alist_find fn (SMod.fnsems md) = Some (msk, sc, {|fsb_fspec := Some fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod  (sp_from md) md)) (SB.sandbox true mask scopes (SModTr.HoareCall fn varg fsp))
  =
  (* head *)
  '((x, x'), varg'):_ <- (hmod_elim_head (_meta fsp) (_precond fsp) varg);;
  (* body *)
  vret' <- inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
                     (SB.sandbox true msk sc (SModTr.trans (sp_from md) (fbody varg')));;
  (* tail *)
  hmod_elim_tail (_meta fsp) (_postcond fsp) (x, x') vret'. 
Proof.
  erewrite HoareCall_inline_cancel; eauto.
  unfold hmod_elim_head, hmod_elim_tail. ired. 
  repeat (f_equal; extensionalities; ired; repeat f_equal). 
Qed.

Definition elim_head_body md
  img msk sc fbody varg fsp
  :=
  ('((x, x'), varg'):_ <- (hmod_elim_head (_meta fsp) (_precond fsp) varg);;
  (* body *)
  'vret' : Any.t <- inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
                     (SB.sandbox img msk sc (SModTr.trans (sp_from md) (fbody varg')));;
  Ret ((x, x'), vret')).

Lemma HoareCall_inline2 md
  (mask:_→bool) scopes fn varg msk sc fsp fbody
  (IN: mask fn)
  (FIND: alist_find fn (SMod.fnsems md) = Some (msk, sc, {|fsb_fspec := Some fsp; fsb_body := fbody|}))
  :
  inline_hp (prog (SMod.to_hmod (sp_from md) md)) 
    (SB.sandbox true mask scopes (SModTr.HoareCall fn varg fsp))
  =
  (* head *)
  RET <- elim_head_body md true msk sc fbody varg fsp;;
  (* tail *)
  (fun RET =>
    let '((x, x'), vret') := RET in
    hmod_elim_tail (_meta fsp) (_postcond fsp) (x, x') vret') RET. 
Proof.
  erewrite HoareCall_inline; eauto. unfold elim_head_body. grind.
Qed.

Ltac set_l := let IT := fresh "ITREE" in
  match goal with  
    | [|- gpaco3 _ _ _ _ _ ?it _] => set (IT := it)
    end; try unfold IT at 2.

Ltac set_r := let IT := fresh "ITREE" in
  match goal with  
    | [|- gpaco3 _ _ _ _ _ _ ?it] => set (IT := it)
    end; try unfold IT at 2.

Lemma elim_rel_refl (md: SMod.t) sp img mask scopes itr
  (WF: sp_wf md sp)
  :
  @elim_rel _ md _ []
    (inline_hp (prog (SMod.to_hmod sp_none (SMod.cancel md))) 
        (SB.sandbox img mask scopes (SModTr.trans sp_none itr)))
    (inline_hp (prog (SMod.to_hmod sp md)) 
        (SB.sandbox img mask scopes (SModTr.trans (if img then sp else sp_none) itr))).
Proof.
  unfold elim_rel.
  ginit. revert itr img mask scopes. gcofix CIH. i.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SBRed.ret !HIRed.ret. gstep. econs.
  - rewrite !SRed.tau !SBRed.tau !HIRed.tau.
    gstep; econs. gstep; econs. eauto with paco.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Assume. des_ifs; ired.
    + rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. gbase. eauto.
    + rewrite !HIRed.bind_core. gstep; econs.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.AssumePrecise.
    rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. gbase. eauto.
  - rewrite !SRed.bind !SRed.ag !SBRed.bind SBRed.Guarantee. ired.
    rewrite !HIRed.bind_ag. gstep. econs. gstep. econs. gbase. eauto.
  - depdes c; s.
    {
      assert (MAIN:
        gpaco3 (elim_rel_def md) (cpn3 (elim_rel_def md)) r r []
          (inline_hp (prog (SMod.to_hmod sp_none (SMod.cancel md)))
             (a <- trigger (Call fn args);; (SB.sandbox img mask scopes (SModTr.trans sp_none (ktrH' a)))))
          (inline_hp (prog (SMod.to_hmod sp md))
             (a <- trigger (Call fn args);; (SB.sandbox img mask scopes (SModTr.trans (if img then sp else sp_none) (ktrH' a)))))).
      {
        rewrite !HIRed.call. rewrite {2 4}/prog. s. gstep; econs.
        rewrite !alist_find_map_snd.
        destruct (alist_find _ _) eqn: E; cycle 1.
        { s. ired. rewrite HIRed.bind_core. gstep. econs. }
        destruct p as [[msk scp] [fsp bd]]. s.
        rewrite /SModTr.trans_ktree /SB.sandbox_body !HIRed.bind. s. ired.
        

        
        destruct fsp eqn: E0; s; cycle 1.
        { guclo elim_rel_bindC_spec. econs.
          - gbase. et.
          - i. rewrite !HIRed.tau. do 2 (gstep; econs). grind. gbase. et.
          - et.
        }

        
        

        
        

        

        gstep; econs. rewrite !HIRed.bind.
        guclo elim_rel_bindC_spec. econs.
        - gbase. Unset Printing Notations.

      }


      
      rewrite !SRed.bind !SRed.call. s.
      destruct (sp fn) eqn: STB; ired; cycle 1.
      {
        rewrite !SBRed.tau !HIRed.tau. gstep. econs.
        destruct img eqn: IMG.
        - rewrite STB. s. ired. rewrite !SBRed.bind SBRed.choose HIRed.bind_core.
          gstep. econs. gstep. econs.
        - s. ired. gstep; econs. rewrite !SBRed.bind !SBRed.call. des_ifs.
          
          

          replace (trigger (Call fn args)) with (SModTr.trans sp_none (trigger (Call fn args))).
          + rewrite -SRed.bind. gbase. et.
          + rewrite SRed.call.

          Unset Printing Notations.

          s. ired. hexploit CIH. instantiate (1:= _ >>= _). rewrite SRed.bind. i.

          { eapply H.


          rewrite !SBRed.bind !SBRed.call. des_ifs.
          + rewrite !HIRed.call. gstep; econs. ired.

          HIRed.bind_core.
          gstep. econs.
      }
      do 2 rewrite SBRed.tau HIRed.tau. do 2 (gstep; econs).
      do 2 rewrite SBRed.bind.
      rewrite SBRed.call. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite HIRed.bind_core. gstep. econs. }
      rewrite HIRed.call HIRed.bind.

      destruct WF. exploit WEAK; et. i; des. rewrite /sp_from /to_sp in FINDSRC.
      destruct (alist_find fn (SMod.fnsems md))
        as [[[msk sc] [fsp bd]] | ] eqn: E; cycle 1.
      { rewrite !alist_find_map_snd E in FINDSRC. ss. }
      rewrite !alist_find_map_snd E in FINDSRC. ss. depdes FINDSRC.
      rewrite !alist_find_map_snd E; s.
      ired. unfold SB.sandbox_body. s.

      set_l. eassert (EQ: ITREE = x <- (tau;; x' <- _;; tau;; tau;; Ret x');; _).
      { unfold ITREE. erewrite bind_tau. do 2 eapply f_equal.
        erewrite bind_bind. eapply f_equal. extensionalities.
        rewrite HIRed.tau. erewrite !bind_tau.
        do 4 eapply f_equal. erewrite bind_ret_l.
        rewrite subst_bind. rewrite bind_ret_l. refl.
      }
      rewrite EQ. clear EQ ITREE.

      rewrite HIRed.bind. guclo elim_rel_bindC_spec.    
      eapply elim_rel_bindC_intro with (l1 := []); et; cycle 1.
      { i. gbase. eauto. }

      destruct f; s; cycle 1.
      { destruct fsp1; ss.
        rewrite SBRed.call. des_ifs.
        rewrite -(bind_ret_r (trigger (Call fn args))) HIRed.call.
        gstep; econs. rewrite {3}/prog. s.
        rewrite !alist_find_map_snd E. s. ired.
        rewrite /SB.sandbox_body /SModTr.trans_ktree. s.
        rewrite !HIRed.bind.
        guclo elim_rel_bindC_spec. econs.
        - gbase. Unset Printing Notations.

          gbase. et.
        - i. rewrite HIRed.tau subst_bind. ired.
          rewrite HIRed.ret. do 3 (gstep; econs).
        - et.
      }

      destruct img; cycle 1.
      { 

      }

      
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
      des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite HIRed.bind_core. gstep. econs. }
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
        gstep. econs.
    + rewrite SRed.bind SRed.pg SCancelRed.bind SCancelRed.pg. 
      rewrite !SBRed.bind SBRed.get. ired.
      des_ifs.
      * rewrite !HIRed.bind_pg.
        gstep. econs. i. gstep. econs. gbase. eauto.
      * unfold triggerUB; ired.
        rewrite !HIRed.bind_core.
        gstep. econs.
  - rewrite SRed.bind SRed.core SCancelRed.bind SCancelRed.core. ired. 
    rewrite !SBRed.bind SBRed.core !HIRed.bind_core. 
    gstep. econs. i. gstep. econs. gbase. eauto.
(*SLOW*)Qed.

End ELIM_REL.

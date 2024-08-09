Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Require Import ModuleInternal Mod EventsRed Events.
Require Import SimGlobal SimGlobalFacts SimInitial SimModSem.
Require Import Red IRed.

Set Implicit Arguments.

Local Open Scope nat_scope.


Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.

Section SIMMOD.

  Context {CONF: EMSConfig}.

  Lemma Mod_add_fnsems md0 md1 sk
    :
      (ModSem.fnsems (Mod.get_modsem (Mod.add md0 md1) sk)) =
      ModSem.add_fnsems (Mod.get_modsem md0 sk) (Mod.get_modsem md1 sk).
  Proof.
    ss.
  Qed.

  Lemma Mod_add_sk md0 md1
    :
      Mod.sk (Mod.add md0 md1) = Mod.sk md0 ++ Mod.sk md1.
  Proof.
    ss.
  Qed.
  
End SIMMOD.



(**** Contextual Refinement on Simulation level ****)
Section SIMCTX.
Import ModSem.

Definition wf_lift {world} wf  :=
  fun (w:world) => 
  (fun '(src, tgt) => 
    match (Any.split src), (Any.split tgt) with
    | Some (l1, r1), Some (l2, r2) => ( wf w (l1, l2) /\ r1 = r2)
    | _, _ => False
    end
  ).

Definition addf f1 f2 : alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l f1) ++ (List.map trans_r f2).


Lemma sim_ctx_aux {world}
      w wf le
      a b c
      fa fb fc 
      ol or stl str itl itr

      (SRC: Any.split stl = Some (b, a))
      (TGT: Any.split str = Some (c, a))

      (SIM: sim_itree wf le fb fc ol or w (b, itl) (c, itr))
:
      @sim_itree world (wf_lift wf) le (addf fb fa) (addf fc fa) ol or w (stl, translate (emb_ run_l) itl) 
                                              (str, translate (emb_ run_l) itr)
.
Proof.
  ginit.

  revert_until wf.

  gcofix CIH. i.

  hexploit SIM. intros SIM'.

  remember (b, itl) eqn:PL.
  remember (c, itr) eqn:PR.
  remember w eqn:Weq.
  unfold sim_itree in SIM'.
  rewrite Weq in SIM' at 2.
  revert a b c stl str itl itr SRC TGT PL PR Weq SIM.
  pattern ol, or, w, p, p0.
  match goal with
  | |- ?P ol or w p p0 => set P
  end.
  eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify.

  - rr in RET. des. clarify.
    rewrite translate_emb_ret.
    gstep. apply sim_itree_ret.
    econs; et. esplits; et.
    unfold wf_lift. rewrite SRC, TGT. split; et.

  - remember (` x : _ <- trigger (Call fn varg);; k_src x). 
    remember (` x : _ <- trigger (Call fn varg);; k_tgt x). 
    remember (b, ` x : _ <- trigger (Call fn varg);; k_src x) eqn:PL.
    remember (c, ` x : _ <- trigger (Call fn varg);; k_tgt x) eqn:PR.
    remember w1 eqn:Weq.
    hexploit SIM. intros SIM0.
    unfold sim_itree in SIM0.
    rewrite Weq in SIM0 at 2.

    revert a b c stl str i i0 WF SRC TGT PL PR Weq SIM SIM0 Heqi Heqi0.
    pattern ol, or, w, p, p0.
    match goal with
    | |- ?P ol or w p p0 => set P
    end.
    eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify;
    rewrite ! translate_emb_bind, translate_emb_callE; gstep; econs;
    try (match goal with
    | |- wf_lift _ _ (_, _) =>  unfold wf_lift; rewrite SRC, TGT; et
    end).
    all: ii; econs; gfinal; left; ss; des_ifs; try rename WF0 into WF1; inv WF1; eapply CIH; et;
         specialize (K _ vret _ _ WLE H); pclearbot; apply sim_itree_bot_flag_up; apply K.
    
  - punfold SIM. inv SIM; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
    + apply inj_pair2 in H0, H1.
      rewrite ! translate_emb_bind, translate_emb_coreE.
      gstep. econs. i. econs. 
      gfinal. left. eapply CIH; et.
      apply sim_itree_bot_flag_up. pfold. apply K0. 

    + pclearbot. punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
      apply inj_pair2 in H0, H1.
      rewrite ! translate_emb_bind, translate_emb_coreE.
      gstep. econs. ii. econs.
      gfinal. left. eapply CIH; et.
      apply sim_itree_bot_flag_up. pfold. apply K0.

  - rewrite ! translate_emb_bind, translate_emb_callE.
    guclo sim_itree_indC_spec.
    econs; et.
    { 
      unfold addf. apply alist_find_app.
      unfold trans_l. rewrite alist_find_map. unfold o_map.
      rewrite FUN. et.
    }
    ss. rewrite <- ! translate_emb_bind.
    eapply IH; et. 
  - rewrite ! translate_emb_bind, translate_emb_callE.
    guclo sim_itree_indC_spec. econs; et.
    { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
    ss. rewrite <- ! translate_emb_bind.
    eapply IH; et. 
  - rewrite ! translate_emb_tau. 
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_tau. 
    guclo sim_itree_indC_spec. econs; et.    
  - rewrite ! translate_emb_bind, translate_emb_coreE.
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_bind, translate_emb_coreE.
    guclo sim_itree_indC_spec. econs; et.
    i. specialize (K x). des. et.
  - rewrite ! translate_emb_bind, translate_emb_coreE.
    guclo sim_itree_indC_spec. econs; et.
    i. specialize (K x). des. et.    
  - rewrite ! translate_emb_bind, translate_emb_coreE.
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_bind, translate_emb_sE.
    guclo sim_itree_indC_spec. econs; et.
    unfold run_l. rewrite SRC. des_ifs; ss. 
    eapply IH; et. rewrite Any.pair_split; et.
  - rewrite ! translate_emb_bind, translate_emb_sE.
    guclo sim_itree_indC_spec. econs; et.
    unfold run_l. rewrite TGT. des_ifs; ss. 
    eapply IH; et. rewrite Any.pair_split; et. 
  - remember (true) as o_src.
    remember (true) as o_tgt.
    rewrite Heqo_src at 2.
    rewrite Heqo_src in SIM0 at 2.
    rewrite Heqo_tgt in Heqo_src.
    remember (b, itl) eqn:PL.
    remember (c, itr) eqn:PR.
    remember w1 eqn:Weq.
    hexploit SIM0. intros SIM0'.
    unfold sim_itree in SIM0'.
    rewrite Weq in SIM0' at 2.

    revert a b c stl str itl itr SRC TGT PL PR Weq Heqo_src Heqo_tgt SIM0.
    pattern o_src, o_tgt, w1, p1, p2.
    match goal with
    | |- ?P o_src o_tgt w1 p1 p2 => set P
    end.
    eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify.
    + rr in RET. des. clarify.
      rewrite ! translate_emb_ret.
      gstep. apply sim_itree_ret.
      econs; et. esplits; et.
      unfold wf_lift. rewrite SRC, TGT. split; et.
    + remember (` x : _ <- trigger (Call fn varg);; k_src x). 
      remember (` x : _ <- trigger (Call fn varg);; k_tgt x). 
      remember (b, ` x : _ <- trigger (Call fn varg);; k_src x) eqn:PL.
      remember (c, ` x : _ <- trigger (Call fn varg);; k_tgt x) eqn:PR.
      remember w2 eqn:Weq.
      hexploit SIM. intros SIM''.
      unfold sim_itree in SIM''.
      rewrite Weq in SIM'' at 2.

      revert a b c stl str i i0 WF SRC TGT PL PR Weq SIM SIM0 SIM'' Heqi Heqi0.
      pattern ol, or, w, p, p0.
      match goal with
      | |- ?P ol or w p p0 => set P
      end.
      eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify;
      rewrite ! translate_emb_bind, translate_emb_callE; gstep; econs; 
      try (match goal with 
          | |- wf_lift _ _ _ => unfold wf_lift; rewrite SRC, TGT; et
          end
      ).
      all: ii; econs; gfinal; left; ss; des_ifs; try rename WF0 into WF1; inv WF1; eapply CIH; et;
      specialize (K _ vret _ _ WLE H); pclearbot; apply sim_itree_bot_flag_up; apply K.
    + punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
      * apply inj_pair2 in H0, H1.
        rewrite ! translate_emb_bind, translate_emb_coreE.
        gstep. econs. i. econs.
        gfinal. left. eapply CIH; et.
        apply sim_itree_bot_flag_up. pfold. eapply K0.

      * pclearbot. punfold SIM1. inv SIM1; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
        apply inj_pair2 in H0, H1.
        rewrite ! translate_emb_bind, translate_emb_coreE.
        gstep. econs. i. econs.
        gfinal. left. eapply CIH; et.
        apply sim_itree_bot_flag_up. pfold. eapply K0.
    + rewrite ! translate_emb_bind, translate_emb_callE.
      guclo sim_itree_indC_spec. econs; et.
      { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
      ss. rewrite <- ! translate_emb_bind.
      eapply IH; et.
    + rewrite ! translate_emb_bind, translate_emb_callE.
      guclo sim_itree_indC_spec. econs; et.
      { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
      ss. rewrite <- ! translate_emb_bind.
      eapply IH; et.
    + rewrite ! translate_emb_tau. 
      guclo sim_itree_indC_spec. econs. et. 
    + rewrite ! translate_emb_tau. 
      guclo sim_itree_indC_spec. econs. et. 
    + rewrite ! translate_emb_bind, translate_emb_coreE.
      guclo sim_itree_indC_spec. econs. et.
    + rewrite! translate_emb_bind, translate_emb_coreE.
      guclo sim_itree_indC_spec. econs. et.
      i. specialize (K x). des. et.
    + rewrite! translate_emb_bind, translate_emb_coreE.
      guclo sim_itree_indC_spec. econs. et.
      i. specialize (K x). des. et.    
    + rewrite ! translate_emb_bind, translate_emb_coreE.
      guclo sim_itree_indC_spec. econs. et.
    + rewrite ! translate_emb_bind, translate_emb_sE.
      guclo sim_itree_indC_spec. econs; et.
      unfold run_l. rewrite SRC. des_ifs; ss.
      eapply IH; et. rewrite Any.pair_split. et.
    + rewrite ! translate_emb_bind, translate_emb_sE.
      guclo sim_itree_indC_spec. econs; et.
      unfold run_l. rewrite TGT. des_ifs; ss.
      eapply IH; et. rewrite Any.pair_split. et.      
    + gstep. econs; et.
      gfinal. left. eapply CIH; et.
Qed.

Theorem sim_ctx
      ctx ms1 ms2
      (SIM: ModSemPair.sim ms1 ms2)
    :
      ModSemPair.sim (add ms1 ctx) (add ms2 ctx)
.
Proof.
 (* Admitted. *)
  inv SIM.
  econs; et; cycle 1.
  { 
    s. ginit. { eapply cpn7_wcompat. eapply simT_mon. }
    guclo tbindC_spec. econs.
    { gfinal. right. eauto. }
    i. subst.
    guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT; ss. }
    i. subst.
    gstep. econs; ss. inv SIM.
    instantiate (1:= wf_lift wf0). exists x.
    ss. rewrite! Any.pair_split. eauto.
  }
   
  s. unfold add_fnsems, trans_l, trans_r.
  apply Forall2_app; eapply Forall2_apply_Forall2; et; cycle 1.
  - instantiate (1:= eq). induction (fnsems ctx); et.
  - i. clarify. econs; et. ii; clarify.
    destruct b. ss.
    destruct (Any.split mrs_src) eqn: SRC; destruct (Any.split mrs_tgt) eqn:TGT; clarify.
    2: { destruct p. clarify. }
    destruct p, p0. des. clarify.
    assert (exists w1, le w w1 /\ wf0 w1 (t0, t2)).
    { exists w. splits; et. refl. }
    clear SIMMRS.
    des.
    ginit.
    revert_until w1.
    revert w1 w.
    
    revert SRC TGT.
    revert t0 t2 t3.
    revert mrs_src mrs_tgt.
    
    generalize (i y) as it.
    revert_until wf0.
    gcofix CIH. i.
    apply Any.split_pair in SRC. 
    apply Any.split_pair in TGT.
    des. clarify.  
    ides it.
    + rewrite ! translate_emb_ret.
      gstep. apply sim_itree_ret.
      unfold lift_rel. esplits; et.
      s. rewrite ! Any.pair_split. et.     
    + rewrite ! translate_emb_tau.
      gstep. 
      apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
      eapply sim_itree_progress; et.
      gfinal. left. 
      eapply CIH; et; des; clarify; rewrite ! Any.pair_split; et.
    + erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      rewrite <- ! bind_trigger.
      destruct e as [c|[s'|e']].
      * (* callE *)
        gstep. destruct c.
        eapply sim_itree_call; clarify.
        { s. rewrite ! Any.pair_split. esplits; et. }
        i. econs. gfinal. left.
        ss. destruct (Any.split st_src0) eqn: SPL1; destruct (Any.split st_tgt0) eqn: SPL2; clarify.
        2: { destruct p. clarify. }
        destruct p, p0, WF.
        eapply CIH.
        9: { etrans; et. }
        all: clarify; et. 
      * (* sE *)
         gstep. destruct s'.
         apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
         eapply sim_itree_progress; et.
         unfold run_r. rewrite ! Any.pair_split.
         gfinal. left. destruct (run t3). ss. eapply CIH; et; rewrite ! Any.pair_split; et.
      * (* coreE *)
        gstep. destruct e'.
        -- (* Choose *)
           apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
           eapply sim_itree_progress; et.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
        -- (* Take *)
           apply sim_itree_take_src. i. eapply sim_itree_take_tgt. 
           eapply sim_itree_progress; et.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
        -- (* Syscall *)
           apply sim_itree_io. i. econs.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
  - i. destruct H. r in H. rr in H0. 
    destruct a, b. econs; et. ss.
    ii; clarify. ss. 
    destruct (Any.split mrs_src) eqn: SRC; destruct (Any.split mrs_tgt) eqn:TGT; clarify.
    2: { destruct p. clarify. }
    destruct p, p0. des. clarify.
    specialize H0 with (x:=y) (y:=y) (w:=w) (mrs_src := t0) (mrs_tgt := t2).
    specialize (H0 eq_refl SIMMRS).
    eapply sim_ctx_aux; et.
Qed.

End SIMCTX.


(* Adequacy - Part 1. ( Divided to resolve the dependency issue. ) *)
Section SEMPAIR.
  Variable ms_src: ModSem.t.
  Variable ms_tgt: ModSem.t.
  Definition fl_src := ms_src.(ModSem.fnsems).
  Definition fl_tgt := ms_tgt.(ModSem.fnsems).
  Variable world: Type.
  Variable wf: world -> Any.t * Any.t -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.
  
  Hypothesis fnsems_find_iff:
    forall fn,
      (<<NONE: alist_find fn ms_src.(ModSem.fnsems) = None>>) \/
      (exists (f_src f_tgt: _ -> itree _ _),
          (<<SRC: alist_find fn ms_src.(ModSem.fnsems) = Some f_src>>) /\
          (<<TGT: alist_find fn ms_tgt.(ModSem.fnsems) = Some f_tgt>>) /\
          (<<SIM: sim_fsem wf le fl_src fl_tgt f_src f_tgt>>)).
          
  Variant g_lift_rel
          (w0: world) st_src st_tgt: Prop :=
  | g_lift_rel_intro
      w1
      (LE: le w0 w1)
      (MN: wf w1 (st_src, st_tgt))
  .

  Variant my_r0:
    forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree coreE R0) -> (itree coreE R1) -> Prop :=
  | my_r0_intro
      w0
      (itr_src itr_tgt: itree modE Any.t)
      st_src st_tgt o_src o_tgt
      (SIM: sim_itree wf le fl_src fl_tgt o_src o_tgt w0 (st_src, itr_src) (st_tgt, itr_tgt))
      (* (STATE: forall mn' (MN: mn <> mn'), Any.t mn' = Any.t mn') *)
    :
      my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
            o_src o_tgt
            (interp_modE (ModSem.prog ms_src) (itr_src) st_src)
            (interp_modE (ModSem.prog ms_tgt) (itr_tgt) st_tgt)
  .

  Let sim_lift: my_r0 <7= simg.
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. destruct PR.
    unfold sim_itree in SIM.
    remember (st_src, itr_src).
    remember (st_tgt, itr_tgt).
    remember w0 in SIM at 2.
    revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw.
    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern o_src, o_tgt, w, p, p0.
    match goal with
    | |- ?P o_src o_tgt w p p0 => set P
    end.
    revert o_src o_tgt w p p0 SIM.
    eapply (@sim_itree_ind world wf le fl_src fl_tgt Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; clarify.
    - rr in RET. des. step. splits; auto. econs; et.
    - hexploit (fnsems_find_iff fn). i. des.
      { steps. rewrite NONE. unfold unwrapU, triggerUB. grind. step. ss. }

      { hexploit (SIM (varg) (varg)); et. i. des. ired_both. 
        steps. grind. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
        apply simg_progress_flag.
        guclo bindC_spec. econs.
        { gbase. eapply CIH. econs; ss. grind. et. }
        { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
          hexploit K; et. i. des. pclearbot. ired_both.
          steps. gbase. eapply CIH. econs; et.
          eapply sim_itree_bot_flag_up. et.           
        }
      }
    - step. i. subst. apply simg_progress_flag.
      hexploit (K x_tgt). i. des. pclearbot.
      steps. gbase. eapply CIH. econs; et.
    - steps. unfold fl_src in FUN. rewrite FUN. grind.
      rewrite <- interp_modE_bind.
      eapply IH; et.
    - steps. unfold fl_tgt in FUN. rewrite FUN. grind.
      rewrite <- interp_modE_bind.
      eapply IH; et.
    - steps.
    - steps. 
    - des. force. exists x. steps. eapply IH; eauto. 
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. destruct run. steps. eapply IH; eauto.
    - steps. destruct run. steps. eapply IH; eauto.
    - eapply simg_progress_flag. gbase. eapply CIH. econs; eauto.
  Qed.
  (* Admitted. *)


  Context `{CONF: EMSConfig}.

  Hypothesis INIT:
    simT (fun x y => exists w, wf w (x, y)) false false ms_src.(ModSem.initial_st) ms_tgt.(ModSem.initial_st).

  Lemma adequacy_local_aux (P Q: Prop)
        (* (wf: world -> W -> Prop)  *)
        (WF: Q -> P)
    :
      (Beh.of_program (ModSem.compile ms_tgt (Some P)))
      <1=
      (Beh.of_program (ModSem.compile ms_src (Some Q))).
  Proof. 
    eapply adequacy_global_itree; ss.
    (* inv INIT.  *)
    des. ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSem.initial_itr, assume. generalize "main" as fn. i.
    hexploit (fnsems_find_iff fn). i. des.
    { 
      esplits. guclo bindC_spec. econs.
      { steps. force. exists (WF x). steps. ss. }
      i. grind. 
      unfold ITree.map, unwrapU, triggerUB.
      steps. guclo bindC_spec. econs.
      { gfinal. right. eapply adequacy_initial. eapply INIT. }
      i. rewrite NONE. steps. ss.
    }
    {
      esplits. guclo bindC_spec. econs.
      { steps. force. exists (WF x). steps. ss. }
      i. grind.
      unfold ITree.map. steps. guclo bindC_spec. econs.
      { gfinal. right. eapply adequacy_initial. eapply INIT. }
      i. unfold unwrapU. rewrite SRC, TGT. grind.
      inv SIM0.
      guclo bindC_spec. econs.
      {
        hexploit (SIM (initial_arg) (initial_arg)); et; cycle 1. i.
        gfinal. right. eapply sim_lift. econs; eauto.
      }  
      { i. destruct vret_src0, vret_tgt1. des; clarify. steps. }
    }
  Qed.

End SEMPAIR.

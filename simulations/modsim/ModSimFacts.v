Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import Behavior.
Require Import CtxRefine.
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

Require Import Mod EventsRed Events.
Require Import SimGlobal SimGlobalFacts ModSim.
Require Import Red IRed.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Adequacy - Part 1. ( Divided to resolve the dependency issue. ) *)

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

Lemma itree_modE_inv R (itr: itree modE R):
  (exists r, itr = Ret r) \/
  (exists itr', itr = tau;; itr') \/
  (exists V (e: coreE V) ktr, itr = v <- trigger e;; ktr v) \/
  (exists fn args ktr, itr = v <- trigger (Call fn args);; ktr v) \/
  (exists V run ktr, itr = v <- trigger (@SUpdate V run);; ktr v).
Proof.
  ides itr; eauto.
  right. right. destruct e as [c|[s'|e']].
  - destruct c. right. left.
    esplits. rewrite bind_trigger. eauto.
  - destruct s'. right. right.
    esplits. rewrite bind_trigger. eauto.
  - left. esplits. rewrite bind_trigger. eauto.
Qed.

Section WF.
  
  Lemma ModSemR_sim_wf
    ms_src ms_tgt
    (SIM : ModSemR.sim ms_src ms_tgt)
    (WF : ModSem.wf ms_src)
    :
    ModSem.wf ms_tgt.
  Proof.
    destruct SIM, WF. econs.
    eapply in_eqlen_nodup_rev; try apply wf_fnsems.
    { rewrite !map_length. eauto. }
    i. destruct (alist_find x (ModSem.fnsems ms_src)) eqn: EQS; cycle 1.
    { apply alist_find_fst_none in EQS. ss. }
    apply sim_fnsems in EQS. des; subst.
    apply alist_find_fst_some in EQS. eauto.
  Qed.
  
  Lemma ModR_sim_wf
    md_src md_tgt
    (SIM : ModR.sim md_src md_tgt)
    (WF : Mod.wf md_src)
    :
    Mod.wf md_tgt.
  Proof.
    destruct WF, SIM, md_src, md_tgt. ss. des. subst.
    split; eauto.
    eapply ModSemR_sim_wf; eauto.
    eapply sim_modsem; eauto using Sk.sort_incl, Sk.sort_wf.
  Qed.

End WF.




(**** Contextual Refinement on Simulation level ****)
Section SIMCTX.
Import ModSem.

Definition wf_lift {world} wf  :=
  fun (w: world) '(src, tgt) => exists st1S st1T st2,
    src = Any.pair st1S st2 /\ tgt = Any.pair st1T st2 /\
    wf w (st1S, st1T).

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
  @sim_itree world (wf_lift wf) le (addf fb fa) (addf fc fa) ol or w
    (stl, translate (emb_ run_l) itl) 
    (str, translate (emb_ run_l) itr)
.
Proof.
  ginit. revert_until wf.
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
    eapply Any.split_pair in SRC, TGT. des. subst.
    r. esplits; eauto.
    
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

    all: eapply Any.split_pair in SRC, TGT; des; subst; rr; esplits; eauto.
    all: ii; econs; gfinal; left; ss; des; subst; eapply CIH;
      try rewrite Any.pair_split; eauto;
      eapply sim_itree_bot_flag_up, K; eauto.

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
      apply Any.split_pair in SRC, TGT. des; subst.
      r. esplits; eauto.
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
      all: eapply Any.split_pair in SRC, TGT; des; subst; rr; esplits; eauto.
      all: ii; econs; gfinal; left; ss; des; subst; eapply CIH;
        try rewrite Any.pair_split; eauto;
        eapply sim_itree_bot_flag_up, K; eauto.
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

Lemma self_sim_r
  world le wf fl fr w st1S st1T st2 i
  (ORD: PreOrder le)
  (WF: wf w (st1S, st1T): Prop)
  :
  sim_itree (@wf_lift world wf) le fl fr false false w
    (Any.pair st1S st2, translate (emb_ run_r) i)
    (Any.pair st1T st2, translate (emb_ run_r) i).
Proof.
  ginit.
  assert (exists w1, le w w1 /\ wf w1 (st1S, st1T)).
  { esplits; eauto. refl. }
  des. clear WF. revert_until fr.
  gcofix CIH. i.

  assert (INV := itree_modE_inv i). des; subst.
  - rewrite translate_emb_ret. gstep. econs.
    r; esplits; eauto. r; esplits; eauto.
  - rewrite translate_emb_tau. gstep. do 3 econs.
    gbase. eauto.
  - rewrite translate_emb_bind, translate_emb_coreE.
    destruct e.
    + gstep. eapply sim_itree_choose_tgt. i. econs. econs. gbase. eauto.
    + gstep. econs. i. econs. econs. gbase. eauto.
    + gstep. econs. i. econs. gbase. eauto.
  - rewrite translate_emb_bind, translate_emb_callE.
    gstep. econs.
    { r. esplits; eauto. }
    i. r in WF. des; subst.
    econs. gbase. eapply CIH, WF1; eauto.
    etrans; eauto.
  - rewrite translate_emb_bind, translate_emb_sE.
    gstep. econs. econs. econs. gbase.
    unfold run_r. rewrite !Any.pair_split. grind.
    eapply CIH, H1; eauto.
Qed.

Theorem sim_ctx
      ctx ms1 ms2
      (SIM: ModSemR.sim ms1 ms2)
    :
      ModSemR.sim (add ms1 ctx) (add ms2 ctx)
.
Proof.
  inv SIM.
  econs; et.
  { instantiate (1:= wf_lift wf0).
    unfold add. s. i. des. subst.
    edestruct sim_initial; eauto. des.
    esplits; eauto.
  }
  { s. unfold add_fnsems.
    rewrite !app_length, !map_length, sim_length. eauto.
  }
  { s. unfold add_fnsems, trans_l, trans_r. intros fn.
    rewrite !alist_find_app_o, !alist_find_map. unfold o_map in *.
    des_ifs. i. eapply sim_miss in Heq1. rewrite Heq1 in Heq2. ss.
  }

  s. unfold add_fnsems, trans_l, trans_r. i.
  rewrite !alist_find_app_o in FIND. des_ifs.
  - rewrite alist_find_map in Heq. unfold o_map in *. des_ifs.
    exploit sim_fnsems; eauto. i; des.
    eexists. split.
    + rewrite alist_find_app_o, alist_find_map, x0. s. eauto.
    + ii. r in SIMMRS. des; subst.
      exploit x1; eauto. intro SIM.
      eapply sim_ctx_aux; try rewrite Any.pair_split; eauto.
  - rewrite alist_find_map in Heq, FIND. unfold o_map in *. des_ifs.
    eexists. split.
    + rewrite alist_find_app_o, alist_find_map.
      apply sim_miss in Heq1. rewrite Heq1. s.
      rewrite alist_find_map, Heq0. s. eauto.
    + ii. r in SIMMRS. des; subst.
      eapply self_sim_r; eauto.
Qed.

Lemma sim_ctx_mod
  ctx md_src md_tgt
  (SIM: ModR.sim md_src md_tgt)
  :
  ModR.sim (Mod.add md_src ctx) (Mod.add md_tgt ctx).
Proof.
  inv SIM.
  econs; et; cycle 1.
  { r. ss. unfold Sk.add. ss. rewrite sim_sk. et. }
  
  i. ss. hexploit (sim_modsem sk); et.
  - unfold Sk.incl, Sk.add in *. i. ss.
    apply SKINCL. rewrite in_app_iff. et.
  - ii. des. apply sim_ctx; et.
Qed.

End SIMCTX.

Section SEMR.
  Variable ms_src: ModSem.t.
  Variable ms_tgt: ModSem.t.
  Definition fl_src := ms_src.(ModSem.fnsems).
  Definition fl_tgt := ms_tgt.(ModSem.fnsems).
  Variable world: Type.
  Variable wf: world -> Any.t * Any.t -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.
  Hypothesis sim_initial:
    forall stS (SAT: ModSem.initial_st ms_src stS),
    exists w stT, ModSem.initial_st ms_tgt stT /\ wf w (stS, stT).
  Hypothesis sim_miss : forall fn,
      alist_find fn (ModSem.fnsems ms_src) = None ->
      alist_find fn (ModSem.fnsems ms_tgt) = None.
  Hypothesis sim_fnsems : forall fn fs,
      alist_find fn (ModSem.fnsems ms_src) = Some fs ->
      exists ft, alist_find fn (ModSem.fnsems ms_tgt) = Some ft /\
      sim_fsem wf le (ModSem.fnsems ms_src) (ModSem.fnsems ms_tgt) fs ft.
    
  Variant g_lift_rel
          (w0: world) st_src st_tgt: Prop :=
  | g_lift_rel_intro
      w1
      (LE: le w0 w1)
      (MN: wf w1 (st_src, st_tgt))
  .

  Lemma sim_itree_simg
    w0 itr_src itr_tgt st_src st_tgt o_src o_tgt
    (SIM: sim_itree wf le fl_src fl_tgt o_src o_tgt w0 (st_src, itr_src) (st_tgt, itr_tgt))
    :
    simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
    o_src o_tgt
    (interp_modE (ModSem.prog ms_src) itr_src st_src)
    (interp_modE (ModSem.prog ms_tgt) itr_tgt st_tgt).
  Proof.
    ginit. revert_until sim_initial.
    gcofix CIH. i.
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
    - destruct (alist_find fn fl_src) eqn: EQ; cycle 1.
      { steps. fold fl_src fl_tgt.
        rewrite EQ. unfold unwrapU, triggerUB. grind. step. ss. }
      hexploit sim_fnsems; eauto. i; des.
      hexploit (H0 (varg) (varg)); et. i.
      steps. fold fl_src fl_tgt in *. rewrite EQ, H. unfold unwrapU. steps.
      apply simg_progress_flag.
      guclo bindC_spec. econs.
      { gbase. eapply CIH; et. }
      i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM.
      hexploit K; et. i. steps.
      gbase. eapply CIH; et. 
      eapply sim_itree_bot_flag_up. et.           
    - step. i. subst. apply simg_progress_flag.
      hexploit (K x_tgt). i. des. pclearbot.
      steps. gbase. eapply CIH; et.
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
    - eapply simg_progress_flag. gbase. eapply CIH; eauto.
  Qed.

  Lemma adequacy_local_aux (P Q: Prop)
    (LE: Q -> P)
    :
    (Beh.of_program (ModSem.compile ms_tgt P))
    <1=
    (Beh.of_program (ModSem.compile ms_src Q)).
  Proof. 
    eapply adequacy_global_itree; ss.
    ginit.
    unfold ModSem.initial_itr, assume. generalize "CCR_init" as fn. i.

    guclo bindC_spec. econs.
    { step. force. eexists; eauto. step. ss. }
    i. subst. ss. unfold ITree.map. grind.

    steps. hexploit sim_initial; eauto. i; des.
    force. eexists. force. eexists; eauto. steps.

    fold fl_src fl_tgt.
    destruct (alist_find fn fl_src) eqn: EQ; cycle 1.
    { grind. unfold triggerUB. grind. steps. ss. }

    hexploit sim_fnsems; eauto. i; des.
    fold fl_src fl_tgt in *.
    rewrite H1. grind.
    guclo bindC_spec. econs.
    { gstep. econs; eauto. gfinal. right.
      eapply sim_itree_simg. eapply H2; eauto. }
    i. steps.
    destruct vret_src, vret_tgt0. des; subst; eauto.
  Qed.

End SEMR.

Section ADEQUACY.

  Lemma adequacy_modsem
    ms_src ms_tgt (Q P: Prop)
    (SIM: ModSemR.sim ms_src ms_tgt)
    (WF : ModSem.wf ms_src)
    (LE: Q -> P)
    :
    <<REF: Beh.of_program (ModSem.compile ms_tgt P) <1= Beh.of_program (ModSem.compile ms_src Q) >>.
  Proof.
    ii. destruct SIM. eapply adequacy_local_aux; eauto.
  Qed.
  
  Lemma adequacy_mod
    md_src md_tgt
    (SIM: ModR.sim md_src md_tgt)
    :
    <<REF: Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src) >>
    .
  Proof.
    destruct (classic (Mod.wf md_src)) as [WF|]; cycle 1.
    { intros x.
      eapply adequacy_global_itree.
      unfold ModSem.initial_itr, assume.
      ginit. grind. gstep. econs; eauto. i. ss.
    }

    assert (SIM0 := SIM).
    destruct WF, SIM0, md_src, md_tgt. ss. des. subst.
    apply Sk.sort_wf in H0.
    hexploit sim_modsem; eauto using Sk.sort_incl; try reflexivity.
    ii. eapply adequacy_modsem, PR; eauto using ModR_sim_wf.
  Qed.

  Theorem adequacy_local md_src md_tgt
          (SIM: ModR.sim md_src md_tgt)
    :
    <<CR: (ctx_refines md_tgt md_src)>>.
  Proof.
    ii. apply sim_ctx_mod with (ctx:=ctx) in SIM.
    pose (Mod.add md_src ctx) as mds.
    pose (Mod.add md_tgt ctx) as mdt.
    fold mds. fold mdt in PR.
    apply adequacy_mod with (md_src := mds) in PR; et.
  Qed.
    
End ADEQUACY.

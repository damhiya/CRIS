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

Require Import Mod2STS Mod Events.
Require Import SimGlobal SimGlobalFacts ModSim.
Require Import Red IRed.
Require Import Permutation.

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

Lemma itree_modE_inv R (itr: itree modE R):
  (exists r, itr = Ret r) \/
  (exists itr', itr = tau;; itr') \/
  (exists V (e: coreE V) ktr, itr = v <- trigger e;; ktr v) \/
  (exists fn args ktr, itr = v <- trigger (Call fn args);; ktr v) \/
  (exists V run ktr, itr = v <- trigger (@SUpdate V run);; ktr v) \/
  (exists V (e: schE V) ktr, itr = v <- trigger e;; ktr v).
Proof.
  ides itr; eauto.
  right. right. destruct e as [s | [c|[s'|e']]].
  - do 3 right. exists X, s, k. rewrite bind_trigger. eauto.
  - destruct c. right. left.
    esplits. rewrite bind_trigger. eauto.
  - destruct s'. right. right. left.
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
  
End WF.

Section SEMR.
  Variable ms_src: ModSem.t.
  Variable ms_tgt: ModSem.t.
  Definition fl_src := ms_src.(ModSem.fnsems).
  Definition fl_tgt := ms_tgt.(ModSem.fnsems).
  Variable world: Type.
  Variable wf: world -> nat * Any.t * Any.t -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_refl: Reflexive le.
  Hypothesis le_trans: Transitive le.
  Hypothesis sim_initial:
    exists w, wf w (1, ModSem.initial_st ms_src, ModSem.initial_st ms_tgt).
  (* Hypothesis sim_miss : forall fn, *)
  (*     alist_find fn (ModSem.fnsems ms_src) = None -> *)
  (*     alist_find fn (ModSem.fnsems ms_tgt) = None. *)
  Hypothesis sim_fnsems : forall fn fs,
      alist_find fn (ModSem.fnsems ms_src) = Some fs ->
      exists ft, alist_find fn (ModSem.fnsems ms_tgt) = Some ft /\
      forall my_tid, sim_fsem wf le (ModSem.fnsems ms_src) (ModSem.fnsems ms_tgt) my_tid fs ft.
    
  Lemma sim_itree_simg
    w tid nths itrs_src itrs_tgt st_src st_tgt ps pt
    (EQS: nths = List.length itrs_src)
    (EQT: nths = List.length itrs_tgt)
    (SIM: forall my_tid itr_src itr_tgt ps0 pt0 w0 nths0 st_src0 st_tgt0
                 (INS: base.lookup my_tid itrs_src = Some itr_src)
                 (INT: base.lookup my_tid itrs_tgt = Some itr_tgt)
                 (FLAG: if Nat.eq_dec my_tid tid then ps0 = ps /\ pt0 = pt else ps0 = true /\ pt0 = true)
                 (NTHS: my_tid < nths0)
                 (WLE: if Nat.eq_dec my_tid tid then w0 = w else le w w0)
                 (WF: if Nat.eq_dec my_tid tid then nths0 = nths /\ st_src0 = st_src /\ st_tgt0 = st_tgt else wf w0 (nths0, st_src0, st_tgt0))
      ,
      sim_itree wf le fl_src fl_tgt my_tid ps0 pt0 w0 nths0 (st_src0, itr_src) (st_tgt0, itr_tgt))
    :
    simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) => ret_src = ret_tgt) ps pt
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_src)) (tid, itrs_src)) st_src)
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_tgt)) (tid, itrs_tgt)) st_tgt).
  Proof.

    (* Revised up to here *)
    
  Qed.
  
  Lemma sim_itree_simg
    w0 itr_src itr_tgt ths st_src st_tgt cur_tid o_src o_tgt
    (SIM: sim_itree wf le fl_src fl_tgt cur_tid o_src o_tgt w0 ths (st_src, itr_src) (st_tgt, itr_tgt))
    :
    simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
    o_src o_tgt
    (interp_modE (ModSem.prog ms_src) itr_src st_src)
    (interp_modE (ModSem.prog ms_tgt) itr_tgt st_tgt).
  Proof.
    ginit. revert_until sim_fnsems.
    gcofix CIH. i.
    unfold sim_itree in SIM.
    remember (st_src, itr_src).
    remember (st_tgt, itr_tgt).
    remember w0 in SIM at 2.
    revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw.
    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern o_src, o_tgt, w, ths, p, p0.
    match goal with
    | |- ?P o_src o_tgt w ths p p0 => set P
    end.
    revert o_src o_tgt w ths p p0 SIM.
    eapply (@sim_itree_ind world wf le fl_src fl_tgt cur_tid Any.t Any.t (final_rel wf le w0) P); subst P; ss; i; clarify.
    - rr in RET. des. subst.
      unfold interp_stateE. unfold interp_schE_callE.
      rewrite !unfold_iter_eq. s.
      
      
      
      Check interp_state_ret.
      
      Search interp_state.
      

      
      Search ITree.iter.
      grind.
      Search ITree.iter.

      step. splits; auto. econs; et.
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

  Lemma adequacy_local_aux
    :
    (Beh.of_program (ModSem.compile ms_tgt))
    <1=
    (Beh.of_program (ModSem.compile ms_src)).
  Proof.
    destruct sim_initial.
    eapply adequacy_global_itree; ss.
    ginit.
    unfold ModSem.initial_itr, assume. generalize "CCR_init" as fn. i.

    ss. unfold ITree.map.
    fold fl_src fl_tgt.
    destruct (alist_find fn fl_src) eqn: EQ; cycle 1.
    { s. unfold triggerUB. grind. steps. ss. }

    hexploit sim_fnsems; eauto. i; des.
    fold fl_src fl_tgt in *.
    rewrite H0. grind.
    guclo bindC_spec. econs.
    { gfinal. right. eapply sim_itree_simg. eapply H1; eauto. }
    i. steps.
    destruct vret_src, vret_tgt. des; subst; eauto.
  Qed.

End SEMR.

Section ADEQUACY.

  Lemma adequacy_modsem
    ms_src ms_tgt
    (SIM: ModSemR.sim ms_src ms_tgt)
    (WF : ModSem.wf ms_src)
    :
    <<REF: Beh.of_program (ModSem.compile ms_tgt) <1= Beh.of_program (ModSem.compile ms_src) >>.
  Proof.
    ii. destruct SIM. eapply adequacy_local_aux; eauto.
  Qed.
  
  Lemma adequacy_mod
    md_src md_tgt sk
    (WF: Mod.wf md_src)
    (SIM: ModR.sim md_src md_tgt)
    (SK: Sk.equiv md_tgt.(Mod.sk) sk)
    :
    <<REF: Beh.of_program (Mod.compile md_tgt sk) <1= Beh.of_program (Mod.compile md_src sk) >>
    .
  Proof.
    assert (SIM0 := SIM).
    destruct WF, SIM0, md_src, md_tgt. ss. des.
    ii. eapply adequacy_modsem; eauto.
    - eapply sim_modsem.
      + eapply Sk.equiv_incl. eauto.
      + eapply Sk.equiv_wf, H.
        etrans; eauto.
    - s. eapply H0. symmetry. etrans; eauto.
  Qed.

End ADEQUACY.

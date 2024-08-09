Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Import STS Behavior.
Require Import ModuleInternal Mod EventsRed Events.
Require Import SimGlobal SimGlobalFacts SimInitial.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Red IRed.
Require Import SimModSem SimModSemFacts0.

Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault
     TranslateFacts.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.


Set Implicit Arguments.

Module ModSemFacts.
Import ModSem.
Section COMM.

  Inductive comm_emb : IFun modE modE -> IFun modE modE -> Prop := 
    |comm_emb_1 : comm_emb emb_l emb_r
    |comm_emb_2 : comm_emb emb_r emb_l
  .

  Inductive comm_ems : itree modE Any.t -> itree modE Any.t -> Prop := 
    | comm_ems_intro emb_l emb_r it (EMB: comm_emb emb_l emb_r) :
        comm_ems (translate emb_l it) (translate emb_r it).    

  Definition comm_st (stp: Any.t * Any.t) : Prop :=
    exists a b, fst stp = Any.pair a b /\ 
    snd stp = Any.pair b a.

  Lemma simT_comm (itr0 itr1: itree takeE Any.t) :
      simT (fun x y : Any.t => exists _ : (), comm_st (x, y)) false false 
        (` st1 : Any.t <- itr1;; ` st2 : Any.t <- itr0;; Ret (Any.pair st1 st2))
        (` st1 : Any.t <- itr0;; ` st2 : Any.t <- itr1;; Ret (Any.pair st1 st2)).
  Proof. 
    ginit. { eapply cpn7_wcompat. eapply simT_mon. }
     
  Admitted.

  Lemma add_comm_aux
        fl fr itl itr stl str (w: unit)
        (COMM: comm_ems itl itr)
        (STATE: comm_st (stl, str))
  :
      sim_itree (fun _ => comm_st) top2 fl fr false false w (stl, itl) (str, itr).
  Proof.   
    destruct COMM, STATE. des. ss.
    (* unfold assoc_st. *)
    ginit. 
    generalize it as itr. 
    clarify.
    generalize x as a0.
    generalize b as b0.
    gcofix CIH. i.
    rewrite (itree_eta_ itr).
    destruct (observe itr).
    - erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
      gstep. apply sim_itree_ret.
      unfold lift_rel. 
      eexists; et. splits; et.
      unfold comm_st. exists a0, b0; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
      gstep. 
      apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      rewrite <- ! bind_trigger.
      destruct e as [c|[s|e]].
      + (* callE *)
        gstep. destruct c, EMB. 
        (* SIMPLIFY BELOW *)
        * apply sim_itree_call; clarify.
          -- exists a0, b0; et.
          -- i. unfold comm_st in WF. des. ss. clarify.
             econs. gfinal. left. eapply CIH.
        * apply sim_itree_call; clarify.
          -- eexists a0, b0; et.
          -- i. unfold comm_st in WF. des. ss. clarify.
             econs. gfinal. left. eapply CIH.
      + (* sE *)
        gstep. destruct s, EMB.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run a0). eapply CIH.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run b0). eapply CIH.  
      + (* eventE *)
        gstep. destruct e, EMB.
        (* Choose *)
        * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        (* Take *)
        * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH. 
        * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH. 
        (* Syscall *)
        * apply sim_itree_io. i.
          econs. gfinal. left. eapply CIH. 
        * apply sim_itree_io. i.
          econs. gfinal. left. eapply CIH.
  Qed. 

  Theorem add_comm
    ms0 ms1
    (P0 P1: Prop) (IMPL: P1 -> P0)
    (WF: wf (add ms1 ms0))
  :
  <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
  .
  Proof.
    destruct (classic (P1)); cycle 1.
    { ii. eapply initial_itr_not_wf;et. }
    replace P0 with P1.
    2: { eapply prop_ext. split; auto. }
    unfold compile. red. eapply adequacy_local_aux; et; cycle 1.
    - eapply simT_comm.
    - i. s.
      unfold add_fnsems. rewrite ! alist_find_app_o.
      destruct (alist_find fn (fnsems ms1)) eqn:MS1; destruct (alist_find fn (fnsems ms0)) eqn: MS0.
      + right. unfold trans_l.
        exists (fun args => translate emb_l (i args)).
        exists (fun args => translate emb_r (i args)).
        rewrite ! alist_find_map.
        esplits; et.
        * rewrite MS1. et.
        * inv WF. ss. unfold add_fnsems in wf_fnsems0. 
          rewrite ! List.map_app in *. rewrite ! List.map_map in *.
          apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0.
          -- clarify.
          -- replace fn with (fst (fn, i)); et.
             rewrite fun_fst_trans_l.
             apply in_map. apply alist_find_some in MS1. et. 
          -- replace fn with (fst (fn, i0)); et.
             rewrite fun_fst_trans_r.
             apply in_map. apply alist_find_some in MS0. et.
        * instantiate (1:= top2). 
          unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H0. econs. econs.
      + right. unfold trans_l.
        exists (fun args => translate emb_l (i args)).
        exists (fun args => translate emb_r (i args)).          
        rewrite ! alist_find_map.
        esplits; et.
        * rewrite MS1. et.
        * rewrite MS0. s. unfold trans_r. rewrite alist_find_map.
          unfold o_map. rewrite MS1. et.
        * unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H0. econs. econs.

      + right. unfold trans_l.
        exists (fun args => translate emb_r (i args)).
        exists (fun args => translate emb_l (i args)).          
        rewrite ! alist_find_map.
        esplits; et.        
        * rewrite MS1. s. unfold trans_r. rewrite alist_find_map.
          unfold o_map. rewrite MS0. et.
        * rewrite MS0. et.
        * unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H0. econs. econs.
      + left. unfold trans_l, trans_r.
        rewrite ! alist_find_map. rewrite MS1, MS0. et.
  Qed.

End COMM.

Section ASSOC.

  Inductive assoc_emb : IFun modE modE -> IFun modE modE -> Prop := 
    |assoc_emb_1 : assoc_emb emb_l (emb_l >>> emb_l)
    |assoc_emb_2 : assoc_emb (emb_l >>> emb_r ) (emb_r >>> emb_l)
    |assoc_emb_3 : assoc_emb (emb_r >>> emb_r) emb_r
  .

  Inductive assoc_ems : itree modE Any.t -> itree modE Any.t -> Prop := 
    | assoc_ems_intro emb_l emb_r it (EMB: assoc_emb emb_l emb_r) :
        assoc_ems (translate emb_l it) (translate emb_r it).
     
  Definition assoc_st (stp: Any.t * Any.t) : Prop :=
    exists a b c, fst stp = Any.pair a (Any.pair b c) /\ 
    snd stp = Any.pair (Any.pair a b) c
  .

  Definition assoc_rev_st (stp: Any.t * Any.t) : Prop :=
    exists a b c, fst stp = Any.pair (Any.pair a b) c /\ 
    snd stp = Any.pair a (Any.pair b c)
  .

  Lemma add_assoc_aux
        fl fr itl itr stl str (w: unit)
        (ASSOC: assoc_ems itl itr)
        (STATE: assoc_st (stl, str))
    :
      sim_itree (fun _ => assoc_st) top2 fl fr false false w (stl, itl) (str, itr).
  Proof.
    destruct ASSOC, STATE. des. ss.
    (* unfold assoc_st. *)
    ginit. 
    generalize it as itr. 
    clarify.
    generalize x as a0.
    generalize b as b0.
    generalize c as c0.
    gcofix CIH. i.
    rewrite (itree_eta_ itr).
    destruct (observe itr).
    - erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
      gstep. apply sim_itree_ret.
      unfold lift_rel. 
      exists tt. splits; et.
      unfold assoc_st. exists a0, b0, c0; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
      gstep. 
      apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      rewrite <- ! bind_trigger.
      destruct e as [c'|[s|e]].
      + (* callE *)
        gstep. destruct c', EMB. 
        (* SIMPLIFY BELOW *)
        * apply sim_itree_call; clarify.
          -- exists a0, b0, c0; et.
          -- i. destruct WF, H, H, H. ss. clarify.
          econs. gfinal. left. eapply CIH.
        * apply sim_itree_call; clarify.
          -- eexists a0, b0, c0; et.
          -- i. unfold assoc_st in WF. des. ss. clarify.
            econs. gfinal. left. eapply CIH.
        * apply sim_itree_call; clarify.
          -- eexists a0, b0, c0; et.
          -- i. unfold assoc_st in WF. des. ss. clarify.
            econs. gfinal. left. eapply CIH. 
      + (* sE *)
        gstep. destruct s, EMB.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run a0). eapply CIH.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run b0). eapply CIH.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run c0). eapply CIH.        
      + (* eventE *)
        gstep. destruct e, EMB.
        (* Choose *)
        * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        (* Take *)
        * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH. 
        * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH. 
        * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        (* Syscall *)
        * apply sim_itree_io. i.
          econs. gfinal. left. eapply CIH. 
        * apply sim_itree_io. i.
          econs. gfinal. left. eapply CIH.
        * apply sim_itree_io. i.
          econs. gfinal. left. eapply CIH.
  Qed. 

Lemma add_assoc_rev_aux
        fl fr itl itr stl str (w: unit)
        (ASSOC: assoc_ems itr itl)
        (STATE: assoc_rev_st (stl, str))

  :
      sim_itree (fun _ => assoc_rev_st) top2 fl fr false false w (stl, itl) (str, itr)
.
Proof.
destruct ASSOC, STATE. des. ss.
ginit. 
generalize it as itr. 
clarify.
generalize x as a0.
generalize b as b0.
generalize c as c0.
gcofix CIH. i.
rewrite (itree_eta_ itr).
destruct (observe itr).
- erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
  gstep. apply sim_itree_ret.
  unfold lift_rel. 
  exists tt. splits; et.
  unfold assoc_st. exists a0, b0, c0; et.
- erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
  gstep. 
  apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
  eapply sim_itree_progress; et.
  gfinal. left. eapply CIH; et.
- erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
  rewrite <- ! bind_trigger.
  destruct e as [c'|[s|e]].
  + (* callE *)
    gstep. destruct c', EMB. 
    (* SIMPLIFY BELOW *)
    * apply sim_itree_call; clarify.
      -- exists a0, b0, c0; et.
      -- i. destruct WF, H, H, H. ss. clarify.
         econs. gfinal. left. eapply CIH.
    * apply sim_itree_call; clarify.
      -- eexists a0, b0, c0; et.
      -- i. unfold assoc_rev_st in WF. des. ss. clarify.
         econs. gfinal. left. eapply CIH.
    * apply sim_itree_call; clarify.
      -- eexists a0, b0, c0; et.
      -- i. unfold assoc_rev_st in WF. des. ss. clarify.
         econs. gfinal. left. eapply CIH. 
  + (* sE *)
    gstep. destruct s, EMB.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a0). eapply CIH.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run b0). eapply CIH.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run c0). eapply CIH.        
  + (* eventE *)
    gstep. destruct e, EMB.
    (* Choose *)
    * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src. 
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src. 
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    (* Take *)
    * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH. 
    * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH. 
    * apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    (* Syscall *)
    * apply sim_itree_io. i.
      econs. gfinal. left. eapply CIH. 
    * apply sim_itree_io. i.
      econs. gfinal. left. eapply CIH.
    * apply sim_itree_io. i.
      econs. gfinal. left. eapply CIH.
Qed. 

Theorem add_assoc
        ms0 ms1 ms2
        (P0 P1: Prop) (IMPL: P1 -> P0)
        (WF: wf (add ms0 (add ms1 ms2)))
  :
    <<COMM: Beh.of_program (compile (add (add ms0 ms1) ms2) (Some P0)) <1=
            Beh.of_program (compile (add ms0 (add ms1 ms2)) (Some P1))>>
.
Proof. 
  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  unfold compile. red. 
  eapply adequacy_local_aux; et; cycle 1.
  {
    instantiate (1:= fun _ => assoc_st). instantiate (1:= unit).
    s. ginit. { eapply cpn7_wcompat. eapply simT_mon. }
    i. rewrite bind_bind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. gstep. econs. exists tt. econs; eauto.
  }

  i. s.
  unfold add_fnsems, trans_l, trans_r. s. unfold add_fnsems, trans_l, trans_r. 
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  destruct (alist_find fn (fnsems ms0)) eqn: MS0; destruct (alist_find fn (fnsems ms1)) eqn:MS1; destruct (alist_find fn (fnsems ms2)) eqn: MS2.
  - inv WF. ss. unfold add_fnsems in wf_fnsems0. ss. unfold add_fnsems in wf_fnsems0.
    rewrite ! List.map_app in *. rewrite ! List.map_map in *.
    apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0; ss.
    + replace fn with (fst (fn, i)); et.
      rewrite fun_fst_trans_l.
      apply in_map. apply alist_find_some in MS0. et.
    + replace fn with (fst (fn, i0)); et.
      rewrite fun_fst_trans_r_l.
      apply in_app_iff. left. 
      apply in_map. apply alist_find_some in MS1. et.
  - inv WF. ss. unfold add_fnsems in wf_fnsems0. ss. unfold add_fnsems in wf_fnsems0.
    rewrite ! List.map_app in *. rewrite ! List.map_map in *.
    apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0; ss.
    + replace fn with (fst (fn, i)); et.
      rewrite fun_fst_trans_l.
      apply in_map. apply alist_find_some in MS0. et.
    + replace fn with (fst (fn, i0)); et.
      rewrite fun_fst_trans_r_l.
      apply in_app_iff. left. apply in_map.
      apply alist_find_some in MS1. et.
  - inv WF. ss. unfold add_fnsems in wf_fnsems0. ss. unfold add_fnsems in wf_fnsems0.
    rewrite ! List.map_app in *. rewrite ! List.map_map in *.
    apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0; ss.
    + replace fn with (fst (fn, i)); et.
      rewrite fun_fst_trans_l.
      apply in_map. apply alist_find_some in MS0. et.
    + replace fn with (fst (fn, i0)); et.
      rewrite fun_fst_trans_r_r.
      apply in_app_iff. right. apply in_map.
      apply alist_find_some in MS2. et.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H0. 
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - inv WF. ss. unfold add_fnsems in wf_fnsems0. ss. unfold add_fnsems in wf_fnsems0.
    rewrite ! List.map_app in *. rewrite ! List.map_map in *.
    rewrite List.app_assoc in *.
    apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0; ss.
    + replace fn with (fst (fn, i)); et.
      rewrite fun_fst_trans_r_l.
      apply in_app_iff. right. 
      apply in_map. apply alist_find_some in MS1. et.
    + replace fn with (fst (fn, i0)); et.
      rewrite fun_fst_trans_r_r.
      apply in_map. apply alist_find_some in MS2. et.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H0.
    erewrite <- ! (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H0.
    erewrite <- ! (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - s. et. 
Qed.

Theorem add_assoc_rev
        ms0 ms1 ms2
        (P0 P1: Prop) (IMPL: P1 -> P0)
        (WF: wf (add (add ms0 ms1) ms2))
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) (Some P0)) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) (Some P1))>>
.
Proof.
  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  unfold compile. red. 
  eapply adequacy_local_aux; et; cycle 1.
  {
    instantiate (1:= fun _ => assoc_rev_st). instantiate (1:= unit).
    s. ginit. { eapply cpn7_wcompat. eapply simT_mon. }
    i. rewrite bind_bind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. guclo tbindC_spec. econs.
    { gfinal. right. eapply self_simT. i. refl. }
    i. grind. gstep. econs. exists tt. econs; eauto.
  }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s. unfold add_fnsems, trans_l, trans_r. 
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 

  destruct (alist_find fn (fnsems ms0)) eqn: MS0; 
  destruct (alist_find fn (fnsems ms1)) eqn:MS1; 
  destruct (alist_find fn (fnsems ms2)) eqn: MS2;
  ( ss; et; right; esplits; et; s; et; unfold sim_fsem, "==>"; i; eapply add_assoc_rev_aux; et; rewrite H0;
    erewrite <- ! (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)); econs; econs).
Qed.

End ASSOC.

Section EMPTY.

Inductive empty_emb : IFun modE modE -> Prop := 
  | empty_emb_intro : empty_emb emb_l
.

Inductive empty_ems : itree modE Any.t -> itree modE Any.t -> Prop := 
  | empty_ems_intro emb_l it (EMB: empty_emb emb_l) :
      empty_ems it (translate emb_l it).    

Definition empty_st (stp: Any.t * Any.t) : Prop :=
  exists a, fst stp = a /\ 
  snd stp = Any.pair a tt↑
.

Definition empty_rev_st (stp: Any.t * Any.t) : Prop :=
  exists a, fst stp = Any.pair a tt↑ /\ 
  snd stp = a
.


Lemma add_empty_aux
        fl fr itl itr stl str (w: unit)
        (EMPTY: empty_ems itl itr)
        (STATE: empty_st (stl, str))

  :
      sim_itree (fun _ => empty_st) top2 fl fr false false w (stl, itl) (str, itr)
.
Proof.
  destruct EMPTY, STATE. des. ss.
  unfold empty_st.
  ginit. 
  generalize it as itr. 
  clarify.
  generalize x as a.
  gcofix CIH. i.
  rewrite (itree_eta_ itr).
  destruct (observe itr).
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists tt. splits; et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c|[s|e]].
    + (* callE *)
      gstep. destruct c, EMB. 
      apply sim_itree_call; clarify.
      -- exists a; et.
      -- i. destruct WF, H. ss. clarify.
         econs. gfinal. left. eapply CIH.
    + (* sE *)
      gstep. destruct s, EMB.
      apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a). eapply CIH.
    + (* eventE *)
      gstep. destruct e, EMB.
      * (* Choose *)
        apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src. 
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * (* Take *)
        apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      * (* Syscall *)
        apply sim_itree_io. i.
        econs. gfinal. left. eapply CIH. 
Qed.

Lemma add_empty_rev_aux
        fl fr itl itr stl str (w: unit)
        (EMPTY: empty_ems itr itl)
        (STATE: empty_rev_st (stl, str))
  :
      sim_itree (fun _ => empty_rev_st) top2 fl fr false false w (stl, itl) (str, itr)
.
Proof.
  destruct EMPTY, STATE. des. ss.
  unfold empty_rev_st.
  ginit. 
  generalize it as itr. 
  clarify.
  generalize x as a.
  gcofix CIH. i.
  ides itr.
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists tt. splits; et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c|[s|e]].
    + (* callE *)
      gstep. destruct c, EMB. 
      apply sim_itree_call; clarify.
      -- exists a; et.
      -- i. destruct WF, H. ss. clarify.
         econs. gfinal. left. eapply CIH.
    + (* sE *)
      gstep. destruct s, EMB.
      apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a). eapply CIH.
    + (* eventE *)
      gstep. destruct e, EMB.
      * (* Choose *)
        apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * (* Take *)
        apply sim_itree_take_src. i. eapply sim_itree_take_tgt.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      * (* Syscall *)
        apply sim_itree_io. i.
        econs. gfinal. left. eapply CIH. 
Qed.


Theorem add_empty
      ms
      (P0 P1: Prop) (IMPL: P1 -> P0)
      (WF: wf ms)
:
  <<EMPTY: Beh.of_program (compile (add ms empty) (Some P0)) <1=
          Beh.of_program (compile ms (Some P1))>>
.
Proof. 
  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  unfold compile. red. 
  eapply adequacy_local_aux; et; cycle 1.
  {
    instantiate (1:= (fun _ => empty_st)). instantiate (1:= unit).
    s. ginit. { eapply cpn7_wcompat. eapply simT_mon. }
    generalize (initial_st ms).
    gcofix CIH. i.
    ides i.
    { grind. stepT. exists tt. econs; eauto. }
    { grind. stepT. stepT. }
    rewrite <- bind_trigger. destruct e. grind.
    stepT. stepT. gstep. econs; eauto. instantiate (1:= x).
    gbase. eauto.
  }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  destruct (alist_find fn (fnsems ms)) eqn: MS; cycle 1.
  - left. et.
  - ss. right. esplits; et.
    unfold sim_fsem, "==>". i. apply add_empty_aux; et.
    rewrite H0. econs. econs.
Qed.

Theorem add_empty_rev
      ms
      (P0 P1: Prop) (IMPL: P1 -> P0)
      (WF: wf ms)
:
  <<EMPTY: Beh.of_program (compile ms (Some P0)) <1=
          Beh.of_program (compile (add ms empty) (Some P1))>>
.
Proof. 
  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  unfold compile. red. 
  eapply adequacy_local_aux; et; cycle 1.
  {
    instantiate (1:= (fun _ => empty_rev_st)). instantiate (1:= unit).
    s. ginit. { eapply cpn7_wcompat. eapply simT_mon. }
    generalize (initial_st ms).
    gcofix CIH. i.
    ides i.
    { grind. stepT. exists tt. econs; eauto. }
    { grind. stepT. stepT. }
    rewrite <- bind_trigger. destruct e. grind.
    stepT. stepT. gstep. econs; eauto. instantiate (1:= x).
    gbase. eauto.
  }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  destruct (alist_find fn (fnsems ms)) eqn: MS; cycle 1.
  - left. et.
  - ss. right. esplits; et.
    unfold sim_fsem, "==>". i. apply add_empty_rev_aux; et.
    rewrite H0. econs. econs.
Qed.
End EMPTY.


End ModSemFacts.

Module ModFacts.
Import Mod.
Section BEH.

Context `{Sk.ld}.

Theorem add_comm
        md0 md1
  :
    <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
.

Proof.
  ii. unfold compile in *.
  destruct (classic (ModSem.wf (enclose (add md1 md0)) /\ Sk.wf (sk (add md1 md0)))).
  2: { eapply ModSem.initial_itr_not_wf. ss. }
  ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
  { apply Sk.wf_comm. auto. }
  rewrite Sk.add_comm; et.
  eapply ModSemFacts.add_comm; [| |et].
  { i. split; auto. unfold enclose. ss. rewrite Sk.add_comm; et.
    inv H2. inv H3. econs; ss.
    unfold ModSem.add_fnsems in *.
    rewrite ! List.map_app in *.
    rewrite ! List.map_map in *.
    rewrite fun_fst_trans_l in *.
    rewrite fun_fst_trans_r in *.
    eapply nodup_comm. et.
  }
  { rewrite Sk.add_comm; et. }
Qed.

Theorem add_assoc
        md0 md1 md2
  :
    <<ASSOC: Beh.of_program (compile (add (add md0 md1) md2)) <1=
            Beh.of_program (compile (add md0 (add md1 md2)))>>
.
Proof. 
  ii. unfold compile in *.
  destruct (classic (ModSem.wf (enclose (add md0 (add md1 md2))) /\ Sk.wf (sk (add md0 (add md1 md2))))).
  2: { eapply ModSem.initial_itr_not_wf. ss. }
  ss. des. assert (SK: Sk.wf (Sk.add (Sk.add (sk md0) (sk md1)) (sk md2))).
  { rewrite <- Sk.add_assoc. apply H1. }
  eapply ModSemFacts.add_assoc; [ |et|rewrite Sk.add_assoc;et].
  i. split; et. unfold enclose. ss.
  rewrite <- Sk.add_assoc.
  inv H2. inv H3. econs.
  repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in *).
  rewrite fun_fst_trans_l in *.
  rewrite fun_fst_trans_r in *.
  rewrite fun_fst_trans_l_l in *.
  rewrite fun_fst_trans_l_r in *.
  rewrite fun_fst_trans_r_l in *.
  rewrite fun_fst_trans_r_r in *.
  rewrite <- app_assoc. apply wf_fnsems.
Qed.

Theorem add_assoc_rev
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) <1=
            Beh.of_program (compile (add (add md0 md1) md2))>>
.
Proof.
  ii. unfold compile in *.
  destruct (classic (ModSem.wf (enclose (add (add md0 md1) md2)) /\ Sk.wf (sk (add (add md0 md1) md2)))).
  2: { eapply ModSem.initial_itr_not_wf. ss. }
  ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (Sk.add (sk md1) (sk md2)))).
  { rewrite Sk.add_assoc. apply H1. }
  eapply ModSemFacts.add_assoc_rev; [ |et|rewrite <- Sk.add_assoc;et].
  i. split; et. unfold enclose. ss.
  rewrite Sk.add_assoc.
  inv H2. inv H3. econs.
  repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in *).
  rewrite fun_fst_trans_l in *.
  rewrite fun_fst_trans_r in *.
  rewrite fun_fst_trans_l_l in *.
  rewrite fun_fst_trans_l_r in *.
  rewrite fun_fst_trans_r_l in *.
  rewrite fun_fst_trans_r_r in *.
  rewrite app_assoc. apply wf_fnsems.
Qed.

Lemma add_empty_r 
      md
  : 
    << EMPTY: Beh.of_program (compile (add md empty)) <1=
              Beh.of_program (compile md)>>
.
Proof.
  ii. unfold compile in *.
  destruct (classic (ModSem.wf (enclose md) /\ Sk.wf (sk md))).
  2: { eapply ModSem.initial_itr_not_wf. ss. }
  ss. des. assert (SK: Sk.wf (Sk.add (sk md) Sk.unit)).
  { rewrite Sk.add_unit_r. et.  }
  eapply ModSemFacts.add_empty; [|et|].
  - instantiate (1:= wf (add md empty)). i.
    unfold wf. esplits; et. ss.
    inv H0. econs. 
    rewrite Sk.add_unit_r.
    unfold ModSem.add, ModSem.add_fnsems. ss.
    rewrite List.map_app. rewrite List.map_map.
    ss. rewrite app_nil_r.
    rewrite fun_fst_trans_l.
    ss.

  - unfold ModSem.compile, ModSem.empty, enclose.
    rewrite Sk.add_unit_r in PR. et.
Qed.

Lemma add_empty_l 
      md
  : 
    << EMPTY: Beh.of_program (compile (add empty md)) <1=
              Beh.of_program (compile md)>>
.
Proof.
  ii. apply add_empty_r. apply add_comm. et.
Qed.

Lemma add_empty_rev_r
      md
  : 
    << EMPTY: Beh.of_program (compile md) <1=
              Beh.of_program (compile (add md empty))>>
.
Proof.
  ii. unfold compile in *.
  destruct (classic (ModSem.wf (enclose (add md empty)) /\ Sk.wf (sk (add md empty)))).
  2: { eapply ModSem.initial_itr_not_wf. ss. }
  des. assert (SK: Sk.wf (sk md)).
  { ss. rewrite Sk.add_unit_r in H1. et.  }

  eapply ModSemFacts.add_empty_rev.
  
  2: { ss. rewrite Sk.add_unit_r in *. inv H0. econs. 
       unfold ModSem.add in wf_fnsems. ss.
       unfold ModSem.add_fnsems in wf_fnsems. ss.
       rewrite List.map_app in wf_fnsems.
       rewrite List.map_map in wf_fnsems.
       rewrite fun_fst_trans_l in wf_fnsems. ss.
       eapply nodup_app_l in wf_fnsems. ss. }
  - instantiate (1:= wf md). i.
    unfold wf. esplits; et. ss.
    inv H0. econs. 
    rewrite Sk.add_unit_r in wf_fnsems.
    unfold ModSem.add, ModSem.add_fnsems in *. ss.
    rewrite List.map_app, List.map_map in wf_fnsems.
    ss. rewrite app_nil_r in wf_fnsems.
    rewrite fun_fst_trans_l in wf_fnsems.
    ss.

  - unfold ModSem.compile, ModSem.empty, enclose. ss.
    rewrite Sk.add_unit_r. et.
Qed.

Lemma add_empty_rev_l
      md
  : 
    << EMPTY: Beh.of_program (compile md) <1=
              Beh.of_program (compile (add empty md))>>
.
Proof. 
  ii. apply add_comm. apply add_empty_rev_r. et. 
Qed.



(* Do we still add by list? (and refines2, refines_proper, etc.) *)
(* Definition add_list (xs: list t): t :=
  fold_right add empty xs
. *)

Lemma add_list_single: forall (x: t), add_list [x] = x.
Proof. ii; cbn. refl. Qed.


Lemma add_list_cons
          x xs
          (A: xs <> [])
        :
          (add_list (x::xs) = (add x (add_list xs)))
.
Proof. ss. destruct xs; ss. Qed.

  Lemma add_list_sk (mdl: list t)
  :
    Mod.sk (add_list mdl)
    =
    fold_right Sk.add Sk.unit (List.map sk mdl).
  Proof.
    induction mdl; ss. rewrite <- IHmdl.
    destruct mdl; ss.
    rewrite Sk.add_unit_r. et.
  Qed.

  Fixpoint add_mrs_list (xs: list (itree coreE Any.t)): itree coreE Any.t :=
    match xs with
    | [] => Ret tt↑
    | x::[] => x
    | x::l => st1 <- x;; st2 <- (add_mrs_list l);; Ret (Any.pair st1 st2)
    end.

  (* Fixpoint add_mrs_list (xs: list Any.t): Any.t :=
    match xs with
    | [] => tt↑
    | x::[] => x
    | x::l => Any.pair x (add_mrs_list l)
    end. *)


  (* Lemma add_list_initial_mrs (mdl: list t) (ske: Sk.t)
     :
       ModSem.initial_st (Mod.get_modsem (add_list mdl) ske)
       =
       add_mrs_list ((List.map (fun md => ModSem.initial_st (get_modsem md ske)) mdl)).
   Proof.
     induction mdl; ss.
     destruct mdl; ss.
     rewrite <- IHmdl; ss.
   Qed.


  Lemma add_list_fns (mdl: list t) (ske: Sk.t)
  :
    List.map fst (ModSem.fnsems (Mod.get_modsem (add_list mdl) ske))
    =
    fold_right (@app _) [] (List.map (fun md => List.map fst (ModSem.fnsems (get_modsem md ske))) mdl).
Proof.
  induction mdl.
  { auto. }
  transitivity ((List.map fst (ModSem.fnsems (get_modsem a ske)))++(fold_right (@app _) [] (List.map (fun md => List.map fst (ModSem.fnsems (get_modsem md ske))) mdl))); auto.
  rewrite <- IHmdl. clear.
  ss. destruct mdl; ss. 
  - rewrite app_nil_r. ss.
  - unfold ModSem.add_fnsems. 
    rewrite ! map_app. rewrite ! List.map_map.
    rewrite fun_fst_trans_l, fun_fst_trans_r. 
    f_equal.
Qed. *)


End BEH.
End ModFacts.

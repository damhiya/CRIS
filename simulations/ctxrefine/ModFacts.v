Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Import STS Behavior.
Require Import Mod EventsRed Events.
Require Import SimGlobal SimGlobalFacts.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Red IRed.
Require Import ModSim ModSimFacts.

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

Import TAC.

Module ModSemFacts.
Import ModSem.

Section EMPTY.

  Inductive empty_emb : IFun modE modE -> Prop := 
    | empty_emb_intro : empty_emb emb_l
  .

  Inductive empty_ems : itree modE Any.t -> itree modE Any.t -> Prop := 
    | empty_ems_intro emb_l it (EMB: empty_emb emb_l) :
        empty_ems it (translate emb_l it).    

  Definition empty_st (stp: Any.t * Any.t) : Prop :=
    exists a, fst stp = a /\ snd stp = Any.pair a tt↑.

  Definition empty_rev_st (stp: Any.t * Any.t) : Prop :=
    exists a, fst stp = Any.pair a tt↑ /\ snd stp = a.
                              
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
    ModSemR.sim ms (add ms empty)
  .
  Proof.
    econs.
    { instantiate (1:= fun (_:()) _ => True). econs; ii; subst; eauto. }
    { instantiate (1:= fun _ => empty_st).
      i. esplits; rr; esplits; rr; eauto. exact tt.
    }
    { s. unfold add_fnsems. rewrite !app_length, !map_length. s. nia. }
    { i. apply alist_find_fst_none in MISS. apply alist_find_fst_notin.
      ss. unfold add_fnsems in *. ii. apply MISS. clear MISS.
      ss. rewrite app_nil_r, List.map_map, fun_fst_trans_l in *. eauto.
    }

    s. unfold add_fnsems. ss. i. rewrite app_nil_r.
    unfold trans_l at 1. rewrite !alist_find_map, FIND. s.
    esplits; eauto.
    ii. subst. rr in SIMMRS. des; ss; subst.
    eapply add_empty_aux; eauto.
    - econs. econs.
    - econs. s; esplits; eauto.
  Qed.

  Theorem add_empty_rev
        ms
        (P0 P1: Prop) (IMPL: P1 -> P0)
        (WF: wf ms)
    :
    ModSemR.sim (add ms empty) ms
  .
  Proof.
    econs.
    { instantiate (1:= fun (_:()) _ => True). econs; ii; subst; eauto. }
    { instantiate (1:= fun _ => empty_rev_st).
      i. rr in SAT. des; subst. rr in SAT1; subst.
      esplits; rr; esplits; rr; eauto. exact tt.
    }
    { s. unfold add_fnsems. rewrite !app_length, !map_length. s. nia. }
    { i. apply alist_find_fst_none in MISS. apply alist_find_fst_notin.
      ss. unfold add_fnsems in *. ii. apply MISS. clear MISS.
      ss. rewrite app_nil_r, List.map_map, fun_fst_trans_l in *. eauto.
    }

    s. unfold add_fnsems. ss. i. rewrite app_nil_r in *.
    unfold trans_l in FIND. rewrite !alist_find_map in FIND.
    unfold o_map in *. des_ifs. esplits; eauto.
    ii. subst. rr in SIMMRS. des; ss; subst.
    eapply add_empty_rev_aux; eauto.
    - econs. econs.
    - econs. s; esplits; eauto.
  Qed.
  
End EMPTY.


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

  Lemma add_comm_aux
        fl fr itl itr stl str (w: unit)
        (COMM: comm_ems itl itr)
        (STATE: comm_st (stl, str))
  :
      sim_itree (fun _ => comm_st) top2 fl fr false false w (stl, itl) (str, itr).
  Proof.   
    destruct COMM, STATE. des. ss.
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
    ModSemR.sim (add ms1 ms0) (add ms0 ms1).
  Proof.
    econs.
    { instantiate (1:= fun (_:()) _ => True). econs; ii; subst; eauto. }
    { instantiate (1:= fun _ => comm_st).
      i. rr in SAT. des. subst.
      esplits; rr; esplits; eauto. exact tt.
    }
    { s. unfold add_fnsems. rewrite !app_length, !map_length. nia. }
    { i. apply alist_find_fst_none in MISS. apply alist_find_fst_notin.
      ss. unfold add_fnsems in *. ii. apply MISS. clear MISS.
      rewrite !map_app, !List.map_map, fun_fst_trans_l, fun_fst_trans_r in *.
      apply in_or_app. apply in_app_or in H. des; eauto.
    }

    s. unfold add_fnsems, trans_l, trans_r. intros fn.
    rewrite ! alist_find_app_o, ! alist_find_map.
    destruct (alist_find fn (fnsems ms0)) eqn:MS0;
      destruct (alist_find fn (fnsems ms1)) eqn: MS1; s; i; ss.
    + inv FIND. exfalso.
      apply alist_find_fst_some in MS0, MS1.
      eapply NoDup_app_disjoint; [|apply MS1|apply MS0].
      destruct WF. ss. unfold add_fnsems in *.
      rewrite !map_app, !List.map_map, fun_fst_trans_l, fun_fst_trans_r in *; ss.
    + inv FIND. esplits; eauto.
      ii. subst. hexploit add_comm_aux; eauto. econs. econs.
    + inv FIND. esplits; eauto.
      ii. subst. hexploit add_comm_aux; eauto. econs. econs.
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

  Theorem add_assoc
          ms0 ms1 ms2
          (P0 P1: Prop) (IMPL: P1 -> P0)
          (WF: wf (add ms0 (add ms1 ms2)))
    :
    ModSemR.sim (add ms0 (add ms1 ms2)) (add (add ms0 ms1) ms2).
  Proof. 
    econs.
    { instantiate (1:= fun (_:()) _ => True). econs; ii; subst; eauto. }
    { instantiate (1:= fun _ => assoc_st).
      i. rr in SAT. des. subst. rr in SAT1. des; subst.
      esplits; eauto.
      - exact tt.
      - rr. esplits; eauto. rr. esplits; eauto.
      - rr. esplits; eauto.
    }
    { s. unfold add_fnsems. rewrite !app_length, !map_length.
      s. unfold add_fnsems. rewrite !app_length, !map_length. nia.
    }
    { i. apply alist_find_fst_none in MISS. apply alist_find_fst_notin.
      ss. unfold add_fnsems in *. ss. unfold add_fnsems in *. 
      ii. apply MISS. clear MISS.
      rewrite !map_app, !List.map_map in *.
      apply in_app_or in H. des.
      - apply in_app_or in H. des.
        + apply in_or_app. left.
          rewrite fun_fst_trans_l, fun_fst_trans_l_l in *. eauto.
        + apply in_or_app. right. apply in_or_app. left.
          rewrite !fun_fst_trans_l_r, !fun_fst_trans_r_l in *. eauto.
      - apply in_or_app. right. apply in_or_app. right.
        rewrite !fun_fst_trans_r, !fun_fst_trans_r_r in *. eauto.
    }

    s. unfold add_fnsems, trans_l, trans_r. intros fn.
    rewrite ! alist_find_app_o, ! alist_find_map.
    destruct (alist_find fn (fnsems ms0)) eqn:MS0;
      destruct (alist_find fn (fnsems ms1)) eqn: MS1; s; i; ss.
    + inv FIND. exfalso.
      apply alist_find_fst_some in MS0, MS1.
      eapply NoDup_app_disjoint; [|apply MS0|apply MS1].
      destruct WF. do 2 (ss; unfold add_fnsems in *).
      rewrite !map_app, !List.map_map in *.
      rewrite app_assoc in wf_fnsems0. apply nodup_app_l in wf_fnsems0.
      rewrite fun_fst_trans_l, fun_fst_trans_r_l in *. eauto.
    + inv FIND. unfold add_fnsems, trans_l.
      rewrite alist_find_app_o, alist_find_map, MS0. s.
      esplits; eauto.
      ii. subst. hexploit add_assoc_aux; eauto.
      erewrite <- !(@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
      econs. econs.
    + unfold add_fnsems, trans_l, trans_r in *.
      rewrite !alist_find_app_o, !alist_find_map, !MS0, !MS1 in *. ss.
      inv FIND. esplits; eauto.
      ii. subst. hexploit add_assoc_aux; eauto.
      erewrite <- !(@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
      econs. econs.
    + unfold add_fnsems, trans_l, trans_r in *.
      rewrite !alist_find_app_o, !alist_find_map, !MS0, !MS1 in *. ss.
      destruct (alist_find fn (fnsems ms2)) eqn: MS2; ss.
      inv FIND. esplits; eauto.
      ii. subst. hexploit add_assoc_aux; eauto.
      erewrite <- !(@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
      econs. econs.
  Qed.

End ASSOC.

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

Section PROPERTIES.
  Context `{Sk.ld}.

  (*** horizontal composition ***)
  Theorem refines_add
        (md0_src md0_tgt md1_src md1_tgt: Mod.t)
        (SIM0: ctx_refines md0_tgt md0_src)
        (SIM1: ctx_refines md1_tgt md1_src)
    :
        <<SIM: ctx_refines (Mod.add md0_tgt md1_tgt) (Mod.add md0_src md1_src)>>
  .
  Proof. 
    ii. r in SIM0. r in SIM1. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc as ASSOC. 
    pose proof ModFacts.add_assoc_rev as ASSOC'. 
    r in COMM. r in ASSOC. r in ASSOC'.
    apply ASSOC'. 
    apply SIM0.
    apply ASSOC. apply COMM. apply ASSOC. apply COMM.
    apply SIM1.
    apply ASSOC. apply COMM. apply ASSOC.
    apply PR.
  Qed.

  Theorem refines_proper_r
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: ctx_refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: ctx_refines (Mod.add (Mod.add_list mds0_tgt) (ctx)) (Mod.add (Mod.add_list mds0_src) (ctx))>>
  .
  Proof.
    ii. r in SIM0.
    apply ModFacts.add_assoc_rev. apply ModFacts.add_assoc in PR.
    apply SIM0. apply PR. 
  Qed.

  Theorem refines_proper_l
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: ctx_refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: ctx_refines (Mod.add ctx (Mod.add_list mds0_tgt)) (Mod.add ctx (Mod.add_list mds0_src))>>
  .

  Proof.
    ii. r in SIM0.
    pose proof ModFacts.add_comm as COMM.
    apply COMM. apply COMM in PR.
    apply ModFacts.add_assoc. apply ModFacts.add_assoc_rev in PR.
    apply COMM. apply COMM in PR.
    apply SIM0. apply PR.  
  Qed.

  Lemma refines_close: ctx_refines <2= refines_closed.
  Proof. 
    ii. specialize (PR Mod.empty). ss.
    pose proof ModFacts.add_empty_r as EMP.
    r in EMP.
    apply EMP with (x0 := x2) in PR.
    2: { apply ModFacts.add_empty_rev_r. et. } 
    apply PR.
  Qed.

  Lemma refines_empty 
    (md: Mod.t)
  :
    <<SIM: ctx_refines md (Mod.add md Mod.empty)>>
  .
  Proof. 
    ii. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc as ASSOC. 
    apply COMM. apply COMM in PR. apply ModFacts.add_empty_rev_r in PR.
    apply ASSOC. et.
  Qed.

  Lemma refines_empty_rev
  (md: Mod.t)
  :
  <<SIM: ctx_refines (Mod.add md Mod.empty) md>>
  .
  Proof. 
    ii. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc_rev as ASSOC'. 
    apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR.
    et.
  Qed.

  (*** horizontal composition ***)
   Theorem refines_list_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: ctx_refines_list t0 s0)
         (SIM1: ctx_refines_list t1 s1)
     :
       <<SIM: ctx_refines_list [Mod.add (Mod.add_list t0) (Mod.add_list t1)] [Mod.add (Mod.add_list s0) (Mod.add_list s1)]>>
   .
   Proof.
    r. unfold ctx_refines_list. eapply refines_add; et.
   Qed.

   Corollary refines_list_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => ctx_refines_list [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       ctx_refines_list mds0_src mds0_tgt.
   Proof.
    induction FORALL; ss.
    hexploit refines_list_add.
    { eapply H0. }
    { eapply IHFORALL. }
    r. i.
    induction l, l'; et.
    { r in H1. unfold ctx_refines_list in H1. ii. apply refines_empty in PR. apply H1. unfold Mod.add_list.
      unfold Mod.add_list in PR. apply PR. }
    { r in H1. unfold ctx_refines_list in H1. ii. unfold Mod.add_list in H1 at 2 5 6. apply H1 in PR.
      unfold Mod.add_list in PR. apply refines_empty_rev in PR. apply PR. }
   Qed.

   Lemma refines_list_eq (mds0 mds1: list Mod.t)
     :
       ctx_refines_list mds0 mds1 <-> ctx_refines (Mod.add_list mds0) (Mod.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

End PROPERTIES.
          

Section ADEQUACY.

  Corollary adequacy_local_list
            mds_src mds_tgt
            (FORALL: List.Forall2 ModR.sim mds_src mds_tgt)
    :
      <<CR: ctx_refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    r. induction FORALL; ss.

    destruct l eqn: L, l' eqn: L'.
    - apply adequacy_local; et.
    - etrans.
      + instantiate (1:= Mod.add x (Mod.add_list [])). apply refines_add.
        * apply adequacy_local. apply H.
        * apply IHFORALL.
      + s. ii.
        pose proof ModFacts.add_comm as COMM. 
        pose proof ModFacts.add_assoc_rev as ASSOC'.
        apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR.
        apply PR.
    - etrans.
      + apply adequacy_local. apply H.
      + etrans.
        * instantiate (1:= Mod.add x (Mod.add_list [])). s. ii.
          pose proof ModFacts.add_comm as COMM. 
          pose proof ModFacts.add_assoc as ASSOC.
          apply COMM. apply COMM in PR. apply ASSOC. apply ModFacts.add_empty_rev_r. apply PR.
        * apply refines_add; et. apply adequacy_local.
          econs; et. ii. rr. apply ModSemR.self_sim.
    - apply refines_add; et. apply adequacy_local. apply H.
  Qed.
          

  Theorem adequacy_local_singleton md_src md_tgt
          (SIM: ModR.sim md_src md_tgt)
    :
      <<CR: (ctx_refines_list [md_tgt] [md_src])>>
  .
  Proof.
    eapply adequacy_local_list. econs; ss.
  Qed.

End ADEQUACY.

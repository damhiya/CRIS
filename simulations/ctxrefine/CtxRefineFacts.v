Require Export Coqlib sflib.
Require Import Behavior.
Require Import Mod Skeleton.
Require Import CtxRefine.
Require Import PCM IPM HMod ISimCore MainAdequacy.
Require Import ModSimAlgebra ModSimFacts.

(*
Section PROPERTIES.
  Context `{Σ: GRA.t}.

  Theorem adequacy_ctx
          md0 md1 Ist
          (SIM: HModR.sim md0 md1 Ist)
      :
          ctx_refines md0 md1.
  Proof. 
    econs. inv SIM.

  Admitted.




  (*** horizontal composition ***)
  (* Theorem refines_add
        (md0_src md0_tgt md1_src md1_tgt: HMod.t)
        (SIM0: ctx_refines md0_tgt md0_src)
        (SIM1: ctx_refines md1_tgt md1_src)
    :
        <<SIM: ctx_refines (HMod.add md0_tgt md1_tgt) (HMod.add md0_src md1_src)>>
  .
  Proof. 
    ii. r in SIM0. r in SIM1. 
    pose proof ModSemAlgebra.add_comm as COMM. 
    pose proof ModSemAlgebra.add_assoc as ASSOC. 
    (* pose proof ModSemAlgebra.add_assoc_rev as ASSOC'.  *)
    (* r in COMM. r in ASSOC. r in ASSOC'. *)
    (* apply ASSOC'.  *)
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
    apply ModSemAlgebra.add_assoc_rev. apply ModSemAlgebra.add_assoc in PR.
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
    pose proof ModSemAlgebra.add_comm as COMM.
    apply COMM. apply COMM in PR.
    apply ModSemAlgebra.add_assoc. apply ModSemAlgebra.add_assoc_rev in PR.
    apply COMM. apply COMM in PR.
    apply SIM0. apply PR.  
  Qed.

  Lemma refines_close: ctx_refines <2= refines_closed.
  Proof. 
    ii. specialize (PR Mod.empty). ss.
    pose proof ModSemAlgebra.add_empty_r as EMP.
    r in EMP.
    apply EMP with (x0 := x2) in PR.
    2: { apply ModSemAlgebra.add_empty_rev_r. et. } 
    apply PR.
  Qed.

  Lemma refines_empty 
    (md: Mod.t)
  :
    <<SIM: ctx_refines md (Mod.add md Mod.empty)>>
  .
  Proof. 
    ii. 
    pose proof ModSemAlgebra.add_comm as COMM. 
    pose proof ModSemAlgebra.add_assoc as ASSOC. 
    apply COMM. apply COMM in PR. apply ModSemAlgebra.add_empty_rev_r in PR.
    apply ASSOC. et.
  Qed.

  Lemma refines_empty_rev
  (md: Mod.t)
  :
  <<SIM: ctx_refines (Mod.add md Mod.empty) md>>
  .
  Proof. 
    ii. 
    pose proof ModSemAlgebra.add_comm as COMM. 
    pose proof ModSemAlgebra.add_assoc_rev as ASSOC'. 
    apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModSemAlgebra.add_empty_r in PR.
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
   Qed. *)

End PROPERTIES.
          

Section ADEQUACY.

  (* Theorem adequacy_local md_src md_tgt
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
        pose proof ModSemAlgebra.add_comm as COMM. 
        pose proof ModSemAlgebra.add_assoc_rev as ASSOC'.
        apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModSemAlgebra.add_empty_r in PR.
        apply PR.
    - etrans.
      + apply adequacy_local. apply H.
      + etrans.
        * instantiate (1:= Mod.add x (Mod.add_list [])). s. ii.
          pose proof ModSemAlgebra.add_comm as COMM. 
          pose proof ModSemAlgebra.add_assoc as ASSOC.
          apply COMM. apply COMM in PR. apply ASSOC. apply ModSemAlgebra.add_empty_rev_r. apply PR.
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
  Qed. *)

End ADEQUACY.


Module ModAlgebra.
Import Mod.
Section BEH.

  Context `{Sk.ld}.
(* 
  Theorem add_comm
          md0 md1
    :
    ModR.sim (add md1 md0) (add md0 md1).
  Proof.
    destruct (classic (ModSem.wf (enclose (add md1 md0)) /\ Sk.wf (sk (add md1 md0)))).
    2: { eapply ModSem.initial_itr_not_wf. ss. }
    ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
    { apply Sk.wf_comm. auto. }
    rewrite Sk.add_comm; et.

    eapply ModSemAlgebra.add_comm; [| |et].
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
    eapply ModSemAlgebra.add_assoc; [ |et|rewrite Sk.add_assoc;et].
    i. split; et. unfold enclose. ss.
    rewrite <- Sk.add_assoc.
    inv H2. inv H3. econs.
    repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in * ).
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
    eapply ModSemAlgebra.add_assoc_rev; [ |et|rewrite <- Sk.add_assoc;et].
    i. split; et. unfold enclose. ss.
    rewrite Sk.add_assoc.
    inv H2. inv H3. econs.
    repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in * ).
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
    eapply ModSemAlgebra.add_empty; [|et|].
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

    eapply ModSemAlgebra.add_empty_rev.
    
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
  Qed. *)



  (* Do we still add by list? (and refines2, refines_proper, etc.) *)
  (* Definition add_list (xs: list t): t :=
    fold_right add empty xs
  . *)

  (* Lemma add_list_single: forall (x: t), add_list [x] = x.
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
      end. *)

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
End ModAlgebra.
*)

Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import Behavior.
Require Import Relation_Definitions.
Require Import IPM.

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
  Hypothesis sim: ModSemR.sim ms_src ms_tgt.
  Hypothesis WFS: ModSem.wf ms_src.
  
  Lemma sim_itree_simg
    w my_tid ps pt nths itrs_src itrs_tgt st_src st_tgt
    (EQS: nths = List.length itrs_src)
    (EQT: nths = List.length itrs_tgt)
    (TID: my_tid < nths)
    (SIM: forall tid itr_src itr_tgt w0 nths0 st_src0 st_tgt0
                 (INS: base.lookup tid itrs_src = Some itr_src)
                 (INT: base.lookup tid itrs_tgt = Some itr_tgt)
                 (WLE: if Nat.eq_dec tid my_tid then w0 = w else le_mine sim.(ModSemR.wle) tid w w0)
                 (WF: if Nat.eq_dec tid my_tid then nths0 = nths /\ st_src0 = st_src /\ st_tgt0 = st_tgt else sim.(ModSemR.wf) w0 (nths0, st_src0, st_tgt0))
      ,
      exists ww, sim_itree ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems) sim.(ModSemR.winit) sim.(ModSemR.wf) sim.(ModSemR.wle) tid ww true true w0 nths0 (st_src0, itr_src) (st_tgt0, itr_tgt))
    :
    simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) => ret_src = ret_tgt) ps pt
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_src)) (my_tid, itrs_src)) st_src)
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_tgt)) (my_tid, itrs_tgt)) st_tgt).
  Proof.
    unfold interp_stateE.
    ginit. revert_until WFS. gcofix CIH. i.
    destruct (base.lookup my_tid itrs_src) eqn: LKS; cycle 1.
    { exfalso. exploit list.lookup_ge_None_1; eauto. i. nia. }
    destruct (base.lookup my_tid itrs_tgt) eqn: LKT; cycle 1.
    { exfalso. exploit list.lookup_ge_None_1; eauto. i. nia. }
    hexploit SIM; eauto; try by des_ifs.
    i. des. revert H. rewrite <-EQS.
    generalize true at 1 as ps0. generalize true at 1 as pt0.
    remember (st_src, i) as src. remember (st_tgt, i0) as tgt.
    i. move H before CIH. revert SIM. revert_until H.
    pattern ps0, pt0, w, nths, src, tgt.
    eapply sim_itree_ind, H. clear H. i. subst.

    inv PR.
    
    - rewrite !unfold_iter_eq. s. rewrite/__ LKS LKT.
      grind. des_ifs.
      + grind. steps. rr in RET. des; subst; eauto.
      + unfold triggerUB. grind. unfold Mod2STS.pure_state. grind. steps. ss.

    - rewrite !unfold_iter_eq. s. rewrite/__ LKS LKT.
      grind. gstep. do 3 (econs; eauto). gbase. eapply CIH; eauto.
      { rewrite !list.insert_length. eauto. }
      { rewrite !list.insert_length. eauto. }
      i. des_ifs; des; subst; cycle 1.
      { rewrite list.list_lookup_insert_ne in INS; try nia. inv INS.
        rewrite list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.
        eapply le_mine_trans; [apply sim| |eauto].
        rr in WLE. des. rr. i. rewrite <-WLE1; try nia. rewrite IN.
        esplits; eauto. apply sim.
      }

      rewrite !list.insert_length.      
      rewrite !list.list_lookup_insert in INS; try nia. inv INS.
      rewrite !list.list_lookup_insert in INT; try nia. inv INT.
      esplits. ginit. rewrite <-!bind_bind.
      guclo lbindC_spec. econs.
      { destruct (alist_find fn (ModSem.fnsems ms_src)) eqn: FIND; cycle 1.
        - eapply ModSemR.wf_sim_miss in FIND; eauto. rewrite FIND.
          grind. unfold triggerUB. grind.
          gstep. econs. econs. i. ss.
        - eapply sim in FIND. des. rewrite FIND. grind.
          eapply sim_itree_flag_down. gfinal. right.
          eapply FIND0; eauto.
      }

      i. rr in SIM0. des; subst.
      do 2 (guclo sim_itree_indC_spec; econs). grind.
      gfinal. right. eapply K; eauto.

    - rewrite !unfold_iter_eq. s. rewrite/__ LKS LKT.
      grind. unfold Mod2STS.pure_state. grind. steps. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. eapply K.
      + rewrite list.list_lookup_insert_ne in INS; try nia. inv INS.
        rewrite list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; des_ifs; eauto.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. rewrite FUN. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      { do 2 f_equal. extensionalities. grind. }
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. hdes. clear K0.
          erewrite equal_f; eauto. do 3 f_equal. extensionalities. grind. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. rewrite FUN. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      { do 2 f_equal. extensionalities. grind. }
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. hdes. clear K0.
          erewrite f_equal; eauto. do 2 f_equal. extensionalities. grind. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. unfold Mod2STS.pure_state at 1.
      grind. force. esplits. steps. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. unfold Mod2STS.pure_state at 2.
      grind. force. i. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. unfold Mod2STS.pure_state at 1.
      grind. force. i. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. unfold Mod2STS.pure_state at 2.
      grind. force. esplits. steps. grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite !unfold_iter_eq. s. rewrite/__ LKS LKT.
      grind. gstep. do 3 (econs; eauto). gbase. eapply CIH; eauto.
      { rewrite !app_length. s. rewrite !list.insert_length. nia. }
      { rewrite !app_length. s. rewrite !list.insert_length. nia. }
      i. des_ifs; des; subst.
      + rewrite lookup_app_l in INS; cycle 1.
        { rewrite list.insert_length. nia. }
        rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        rewrite lookup_app_l in INT; cycle 1.
        { rewrite list.insert_length. nia. }
        rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        rewrite app_length. s. rewrite list.insert_length.
        eexists. rewrite Nat.add_comm. s. rewrite !EQT in *. eapply K.
      + assert (DEC: tid < List.length itrs_tgt \/ tid = List.length itrs_tgt).
        { apply lookup_lt_Some in INS. rewrite app_length in INS. ss.
          rewrite list.insert_length in INS. nia. }
        des.
        { rewrite lookup_app_l in INS; cycle 1.
          { rewrite list.insert_length. nia. }
          rewrite list.list_lookup_insert_ne in INS; try nia.
          rewrite lookup_app_l in INT; cycle 1.
          { rewrite list.insert_length. nia. }
          rewrite list.list_lookup_insert_ne in INT; try nia.
          eapply SIM; eauto; des_ifs.
          ii. eapply WLE. rewrite lookup_app_l; eauto using lookup_lt_Some.
        }
        subst.
        rewrite (list_lookup_middle _ []) in INS; cycle 1.
        { rewrite list.insert_length. eauto. }
        inv INS.
        rewrite (list_lookup_middle _ []) in INT; cycle 1.
        { rewrite list.insert_length. eauto. }
        inv INT.
        
        esplits.
        destruct (alist_find fn (ModSem.fnsems ms_src)) eqn: FIND; cycle 1.
        * eapply ModSemR.wf_sim_miss in FIND; eauto. rewrite FIND.
          grind. unfold triggerUB. grind.
          pstep. econs. econs. i. ss.
        * eapply sim in FIND. des. rewrite FIND. grind.
          ginit. eapply sim_itree_flag_down. gfinal. right.
          eapply FIND0; eauto.

    - rewrite !unfold_iter_eq. s. rewrite/__ LKS LKT.
      grind. gstep. do 2 (econs; eauto).
      assert (DEC: tid < List.length itrs_src \/ tid >= List.length itrs_src) by nia.
      des; cycle 1.
      { rewrite unfold_iter_eq. s.
        rewrite list.lookup_ge_None_2; try (rewrite list.insert_length; nia).
        s. grind. unfold triggerUB. grind. unfold Mod2STS.pure_state. grind.
        econs; eauto. ss. }

      econs; eauto. gbase. eapply CIH; eauto.
      { rewrite !list.insert_length. nia. }
      { rewrite !list.insert_length. nia. }

      i. des_ifs; des; subst.
      { assert (DEC': tid = my_tid \/ tid ≠ my_tid) by nia; des; subst.
        - rewrite !list.list_lookup_insert in INS; try nia. inv INS.
          rewrite !list.list_lookup_insert in INT; try nia. inv INT.
          rewrite list.insert_length. eexists. eapply K; eauto.
          apply le_mine_refl. apply sim.
        - rewrite list.list_lookup_insert_ne in INS; try nia.
          rewrite list.list_lookup_insert_ne in INT; try nia.
          eapply SIM; eauto; des_ifs; eauto.
          + ii. red in WLE. des. rewrite <-WLE0. rewrite IN.
            esplits; eauto. apply sim. eauto.
          + rewrite list.insert_length. eauto.
      }
      { assert (DEC': tid0 = my_tid \/ tid0 ≠ my_tid) by nia; des; subst.
        - rewrite !list.list_lookup_insert in INS; try nia. inv INS.
          rewrite !list.list_lookup_insert in INT; try nia. inv INT.
          eexists. eapply K; eauto.
        - rewrite list.list_lookup_insert_ne in INS; try nia.
          rewrite list.list_lookup_insert_ne in INT; try nia.
          eapply SIM; eauto; des_ifs; eauto.
          eapply le_mine_trans; [apply sim| |eauto].
          ii. red in WLE. des. rewrite <-WLE1. rewrite IN.
          esplits; eauto. apply sim. eauto.
      }

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite/__ (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. steps.
      eapply K;
        try rewrite list.insert_length;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - admit.
  Admitted.

  (* Lemma sim_itree_simg *)
  (*   w0 itr_src itr_tgt ths st_src st_tgt cur_tid o_src o_tgt *)
  (*   (SIM: sim_itree wf le fl_src fl_tgt cur_tid o_src o_tgt w0 ths (st_src, itr_src) (st_tgt, itr_tgt)) *)
  (*   : *)
  (*   simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) => *)
  (*               g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt) *)
  (*   o_src o_tgt *)
  (*   (interp_modE (ModSem.prog ms_src) itr_src st_src) *)
  (*   (interp_modE (ModSem.prog ms_tgt) itr_tgt st_tgt). *)
  (* Proof. *)
  (*   ginit. revert_until sim_fnsems. *)
  (*   gcofix CIH. i. *)
  (*   unfold sim_itree in SIM. *)
  (*   remember (st_src, itr_src). *)
  (*   remember (st_tgt, itr_tgt). *)
  (*   remember w0 in SIM at 2. *)
  (*   revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw. *)
  (*   (* TODO: why induction using sim_itree_ind doesn't work? *) *)
  (*   pattern o_src, o_tgt, w, ths, p, p0. *)
  (*   match goal with *)
  (*   | |- ?P o_src o_tgt w ths p p0 => set P *)
  (*   end. *)
  (*   revert o_src o_tgt w ths p p0 SIM. *)
  (*   eapply (@sim_itree_ind world wf le fl_src fl_tgt cur_tid Any.t Any.t (final_rel wf le w0) P); subst P; ss; i; clarify. *)
  (*   - rr in RET. des. subst. *)
  (*     unfold interp_stateE. unfold interp_schE_callE. *)
  (*     rewrite !unfold_iter_eq. s. *)
      
      
      
  (*     Check interp_state_ret. *)
      
  (*     Search interp_state. *)
      

      
  (*     Search ITree.iter. *)
  (*     grind. *)
  (*     Search ITree.iter. *)

  (*     step. splits; auto. econs; et. *)
  (*   - destruct (alist_find fn fl_src) eqn: EQ; cycle 1. *)
  (*     { steps. fold fl_src fl_tgt. *)
  (*       rewrite EQ. unfold unwrapU, triggerUB. grind. step. ss. } *)
  (*     hexploit sim_fnsems; eauto. i; des. *)
  (*     hexploit (H0 (varg) (varg)); et. i. *)
  (*     steps. fold fl_src fl_tgt in *. rewrite EQ, H. unfold unwrapU. steps. *)
  (*     apply simg_progress_flag. *)
  (*     guclo bindC_spec. econs. *)
  (*     { gbase. eapply CIH; et. } *)
  (*     i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM. *)
  (*     hexploit K; et. i. steps. *)
  (*     gbase. eapply CIH; et.  *)
  (*     eapply sim_itree_bot_flag_up. et.            *)
  (*   - step. i. subst. apply simg_progress_flag. *)
  (*     hexploit (K x_tgt). i. des. pclearbot. *)
  (*     steps. gbase. eapply CIH; et. *)
  (*   - steps. unfold fl_src in FUN. rewrite FUN. grind. *)
  (*     rewrite <- interp_modE_bind. *)
  (*     eapply IH; et. *)
  (*   - steps. unfold fl_tgt in FUN. rewrite FUN. grind. *)
  (*     rewrite <- interp_modE_bind. *)
  (*     eapply IH; et. *)
  (*   - steps. *)
  (*   - steps.  *)
  (*   - des. force. exists x. steps. eapply IH; eauto.  *)
  (*   - steps. i. hexploit K. i. des. steps. eapply IH; eauto. *)
  (*   - steps. i. hexploit K. i. des. steps. eapply IH; eauto. *)
  (*   - des. force. exists x. steps. eapply IH; eauto. *)
  (*   - steps. destruct run. steps. eapply IH; eauto. *)
  (*   - steps. destruct run. steps. eapply IH; eauto. *)
  (*   - eapply simg_progress_flag. gbase. eapply CIH; eauto. *)
  (* Qed. *)

  Lemma adequacy_local_aux
    :
    (Beh.of_program (ModSem.compile ms_tgt))
    <1=
    (Beh.of_program (ModSem.compile ms_src)).
  Proof.
    (* destruct sim_initial. *)
    (* eapply adequacy_global_itree; ss. *)
    (* ginit. *)
    (* unfold ModSem.initial_itr, assume. generalize "CCR_init" as fn. i. *)

    (* ss. unfold ITree.map. *)
    (* fold fl_src fl_tgt. *)
    (* destruct (alist_find fn fl_src) eqn: EQ; cycle 1. *)
    (* { s. unfold triggerUB. grind. steps. ss. } *)

    (* hexploit sim_fnsems; eauto. i; des. *)
    (* fold fl_src fl_tgt in *. *)
    (* rewrite H0. grind. *)
    (* guclo bindC_spec. econs. *)
    (* { gfinal. right. eapply sim_itree_simg. eapply H1; eauto. } *)
    (* i. steps. *)
    (* destruct vret_src, vret_tgt. des; subst; eauto. *)
  Admitted.

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
    econs; eauto.
  Qed.
  
  (* Lemma adequacy_mod *)
  (*   md_src md_tgt sk *)
  (*   (WF: Mod.wf md_src) *)
  (*   (SIM: ModR.sim md_src md_tgt) *)
  (*   (SK: Sk.equiv md_tgt.(Mod.sk) sk) *)
  (*   : *)
  (*   <<REF: Beh.of_program (Mod.compile md_tgt sk) <1= Beh.of_program (Mod.compile md_src sk) >> *)
  (*   . *)
  (* Proof. *)
  (*   assert (SIM0 := SIM). *)
  (*   destruct WF, SIM0, md_src, md_tgt. ss. des. *)
  (*   ii. eapply adequacy_modsem; eauto. *)
  (*   - eapply sim_modsem. *)
  (*     + eapply Sk.equiv_incl. eauto. *)
  (*     + eapply Sk.equiv_wf, H. *)
  (*       etrans; eauto. *)
  (*   - s. eapply H0. symmetry. etrans; eauto. *)
  (* Qed. *)

End ADEQUACY.

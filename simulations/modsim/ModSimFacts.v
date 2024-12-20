Require Import Common.

Require Import Skeleton Mod.
Require Import SimGlobal SimGlobalFacts.
Require Import ModSimTactics ModSim.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Adequacy - Part 1. ( Divided to resolve the dependency issue. ) *)
Lemma itree_modE_inv R (itr : itree modE R) :
  (exists r, itr = Ret r) \/
  (exists itr', itr = tau;; itr') \/
  (exists V (e : coreE V) ktr, itr = v <- trigger e;; ktr v) \/
  (exists fn args ktr, itr = v <- trigger (Call fn args);; ktr v) \/
  (exists V run ktr, itr = v <- trigger (@SUpdate V run);; ktr v) \/
  (exists V (e : schE V) ktr, itr = v <- trigger e;; ktr v).
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

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_indC_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

End TAC.
Import TAC.

Section SEMR.
  Variable ms_src : ModSem.t.
  Variable ms_tgt : ModSem.t.
  Hypothesis sim : MSim.t ms_src ms_tgt.
  Hypothesis WFS : ModSem.wf ms_src.
  
  Lemma sim_itree_simg
    w my_tid ps pt nths itrs_src itrs_tgt st_src st_tgt
    (EQS : nths = List.length itrs_src)
    (EQT : nths = List.length itrs_tgt)
    (TID : my_tid < nths)
    (WLEN : nths = List.length w)
    (SIM : forall tid ps0 pt0 itr_src itr_tgt w0 nths0 st_src0 st_tgt0
            (INS : base.lookup tid itrs_src = Some itr_src)
            (INT : base.lookup tid itrs_tgt = Some itr_tgt)
            (TID : tid < nths0)
            (WLEN : nths0 = List.length w0)
            (FLG : if Nat.eq_dec tid my_tid then ps0 = ps /\ pt0 = pt else ps0 = true /\ pt0 = true)
            (WLE : if Nat.eq_dec tid my_tid then w0 = w else le_mine sim.(MSim.wle) tid w w0)
            (WF : if Nat.eq_dec tid my_tid then nths0 = nths /\ st_src0 = st_src /\ st_tgt0 = st_tgt else sim.(MSim.wf) w0 (nths0, st_src0, st_tgt0))
      ,
      exists ww, sim_itree ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems) sim.(MSim.winit) sim.(MSim.wf) sim.(MSim.wle) tid ww ps0 pt0 w0 nths0 (st_src0, itr_src) (st_tgt0, itr_tgt))
    :
    simg (fun '(st_src, ret_src) '(st_tgt, ret_tgt) => ret_src = ret_tgt) (Some ps) (Some pt)
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_src)) (my_tid, itrs_src)) st_src)
    (interp_stateE Any.t
       (ITree.iter (handle_schE_callE (ModSem.prog ms_tgt)) (my_tid, itrs_tgt)) st_tgt).
  Proof.
    unfold interp_stateE.
    ginit. revert_until WFS. gcofix CIH. i.
    destruct (base.lookup my_tid itrs_src) eqn : LKS; cycle 1.
    { exfalso. exploit list.lookup_ge_None_1; eauto. i. nia. }
    destruct (base.lookup my_tid itrs_tgt) eqn : LKT; cycle 1.
    { exfalso. exploit list.lookup_ge_None_1; eauto. i. nia. }
    hexploit (SIM my_tid ps pt); eauto; try by des_ifs.
    i. des.
    remember (st_src, i) as src. remember (st_tgt, i0) as tgt.
    move H before CIH. revert SIM. revert_until H.
    pattern ps, pt, w, nths, src, tgt.
    eapply sim_itree_ind, H. clear H. i. subst.

    inv PR.

    - rewrite !unfold_iter_eq. s. rewrite LKS LKT.
      grind. des_ifs.
      + grind. steps. rr in RET. des; subst; eauto.
      + unfold triggerUB. grind. unfold Mod2ITree.pure_state. grind. steps. ss.

    - rewrite !unfold_iter_eq. s. rewrite LKS LKT.
      grind. gstep. econs. do 5 (econs; eauto using smj_lt_mid_top).
      gbase. eapply (CIH w1); eauto.
      { rewrite !length_insert. eauto. }
      { rewrite !length_insert. eauto. }
      { rewrite !length_insert. inv WLE. nia. }

      i. guardH FLG. des_ifs; des; subst; cycle 1.
      { rewrite list.list_lookup_insert_ne in INS; try nia. inv INS.
        rewrite list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.
        eapply le_mine_trans; [apply sim| |eauto].
        rr in WLE. des. rr. i. rewrite <-WLE1; try nia. rewrite IN.
        esplits; eauto. apply sim.
      }

      rewrite !list.list_lookup_insert in INS; try nia. inv INS.
      rewrite !list.list_lookup_insert in INT; try nia. inv INT.
      esplits. ginit. rewrite <-!bind_bind.
      guclo lbindC_spec. econs.
      { destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn : FIND; cycle 1.
        - grind. unfold triggerNB. grind.
          gstep. econs. eapply sim_itree_choose_tgt. i. ss.
        - eapply sim in FIND. des. rewrite FIND. grind.
          eapply sim_itree_flag_down. gfinal. right.
          rewrite WF0. rewrite length_insert.
          eapply FIND0; eauto.
      }

      i. rr in SIM0. des; subst.
      do 2 (guclo sim_itree_indC_spec; econs). grind.
      gfinal. right. eapply K; eauto.

    - rewrite !unfold_iter_eq. s. rewrite LKS LKT.
      grind. unfold Mod2ITree.pure_state. grind. do 3 step. grind. do 2 step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. eapply K.
      + rewrite list.list_lookup_insert_ne in INS; try nia. inv INS.
        rewrite list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; des_ifs; eauto.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. rewrite FUN. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      { do 2 f_equal. extensionalities. grind. }
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. rewrite WF.
          erewrite equal_f; eauto. do 3 f_equal. extensionalities. grind. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. rewrite FUN. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      { do 2 f_equal. extensionalities. grind. }
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. rewrite WF.
          erewrite f_equal; eauto. do 2 f_equal. extensionalities. grind. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. do 2 step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. do 2 step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. unfold Mod2ITree.pure_state at 1.
      grind. step. esplits. step. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. unfold Mod2ITree.pure_state at 2.
      grind. do 2 step. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. unfold Mod2ITree.pure_state at 1.
      grind. do 2 step. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. unfold Mod2ITree.pure_state at 2.
      grind. step. esplits. step. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite unfold_iter_eq. s. rewrite LKS.
      grind. do 2 step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. do 2 step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite !unfold_iter_eq. s. rewrite LKS LKT.
      grind. do 2 step. gstep. econs. econs; eauto using smj_lt_mid_top.
      gbase. eapply CIH.
      { rewrite !length_app. s. rewrite !length_insert. eauto. }
      { rewrite !length_app. s. rewrite !length_insert. nia. }
      { nia. }
      { instantiate (1:=(x2 ++ [MSim.winit sim])). rewrite length_app. s. nia. }
      i. des_ifs; des; subst.
      + rewrite lookup_app_l in INS; cycle 1.
        { rewrite length_insert. nia. }
        rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        rewrite lookup_app_l in INT; cycle 1.
        { rewrite length_insert. nia. }
        rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF Nat.add_comm. s. move: K; rewrite !EQT; intros K; eapply K.
      + assert (DEC : tid < List.length itrs_tgt \/ tid = List.length itrs_tgt).
        { apply lookup_lt_Some in INS. rewrite length_app in INS. ss.
          rewrite length_insert in INS. nia. }
        des.
        { rewrite lookup_app_l in INS; cycle 1.
          { rewrite length_insert. nia. }
          rewrite list.list_lookup_insert_ne in INS; try nia.
          rewrite lookup_app_l in INT; cycle 1.
          { rewrite length_insert. nia. }
          rewrite list.list_lookup_insert_ne in INT; try nia.
          eapply SIM; eauto; des_ifs.
          ii. eapply WLE. rewrite lookup_app_l; eauto using lookup_lt_Some.
        }
        subst.
        rewrite (list_lookup_middle _ []) in INS; cycle 1.
        { rewrite length_insert. eauto. }
        inv INS.
        rewrite (list_lookup_middle _ []) in INT; cycle 1.
        { rewrite length_insert. eauto. }
        inv INT.
        
        esplits.
        destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn : FIND; cycle 1.
        * grind. unfold triggerNB. grind.
          pstep. econs. eapply sim_itree_choose_tgt. i. ss.
        * eapply sim in FIND. des. rewrite FIND. grind.
          ginit. eapply sim_itree_flag_down. gfinal. right.
          eapply FIND0; eauto.

    - rewrite !unfold_iter_eq. s. rewrite LKS LKT.
      grind. do 2 step. gstep. econs. econs; eauto using smj_lt_mid_top.
      assert (DEC : tid < List.length itrs_src \/ tid >= List.length itrs_src) by nia.
      des; cycle 1.
      { rewrite unfold_iter_eq. s.
        rewrite list.lookup_ge_None_2; try (rewrite length_insert; nia).
        s. grind. unfold triggerUB. grind. unfold Mod2ITree.pure_state. grind.
        step. ss. }

      gbase. eapply (CIH w1); eauto.
      { rewrite !length_insert. nia. }
      { rewrite !length_insert. nia. }
      { rewrite !length_insert. inv WLE. nia. }

      i. des_ifs; des; subst.
      { assert (DEC' : tid = my_tid \/ tid ≠ my_tid) by nia; des; subst.
        - rewrite !list.list_lookup_insert in INS; try nia. inv INS.
          rewrite !list.list_lookup_insert in INT; try nia. inv INT.
          rewrite WF0 length_insert. eexists. eapply K; eauto.
          apply le_mine_refl. apply sim.
        - rewrite list.list_lookup_insert_ne in INS; try nia.
          rewrite list.list_lookup_insert_ne in INT; try nia.
          eapply SIM; eauto; des_ifs; eauto.
          + ii. red in WLE. des. rewrite <-WLE0. rewrite IN.
            esplits; eauto. apply sim. eauto.
          + rewrite WF0 length_insert. eauto.
      }
      { assert (DEC' : tid0 = my_tid \/ tid0 ≠ my_tid) by nia; des; subst.
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
      grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INS; try nia. inv INS.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INS; try nia. inv INS.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. rewrite WF. ginit. guclo lflagC_spec. econs.
        { gfinal. right. eapply K. }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - rewrite (unfold_iter_eq _ (_, itrs_tgt)). s. rewrite LKT.
      grind. rewrite FUN. grind. step.
      eapply K;
        try rewrite length_insert;
        try rewrite list.list_lookup_insert; eauto; try nia.
      { do 2 f_equal. unfold triggerNB. grind. }
      i. des_ifs; des; subst.
      + rewrite !list.list_lookup_insert in INT; try nia. inv INT.
        eexists. ginit. guclo lflagC_spec. econs.
        { gfinal. right. rewrite WF.
          erewrite equal_f; eauto. do 2 f_equal. unfold triggerNB. grind.
          ginit. eapply sim_itree_indC_spec. econs. i. inv x. 
        }
        { apply le_others_refl. }
        { eauto. }
        { eauto. }
      + rewrite !list.list_lookup_insert_ne in INT; try nia. inv INT.
        eapply SIM; eauto; des_ifs.

    - gstep. econs. econs; cycle 1.
      { instantiate (1:= Some false). ss. }
      { instantiate (1:= Some false). ss. }

      gbase. eapply CIH; eauto.
      i. des_ifs; cycle 1; des; subst.
      { eapply SIM; eauto; des_ifs; eauto. }

      eexists. rewrite WF. ginit. guclo lflagC_spec.
      econs; try eassumption; eauto with paco.
      
  Unshelve. all : try exact smj_bot. eauto.
  Qed.

  Lemma adequacy_local_aux
    :
    (Beh.of_itree (ModSem.compile ms_tgt))
    <1=
    (Beh.of_itree (ModSem.compile ms_src)).
  Proof.
    eapply adequacy_global; ss.
    ginit.
    unfold ModSem.compile, assume. generalize ModSem.init_fun as fn. i.

    ss. unfold ITree.map.
    destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn: EQ; cycle 1.
    { s. unfold interp_modE, interp_stateE, interp_schE_callE.
      rewrite [ITree.iter (_ (ModSem.prog ms_tgt)) _]unfold_iter_eq. grind.
      ired_both; guclo simg_indC_spec. unfold Mod2ITree.pure_state. grind.
      eapply simg_chooseR. ss.
    }

    hexploit (MSim.sim_fnsems sim); eauto. i; des. rr in H0. grind.
    guclo bindC_spec. econs.
    - edestruct (MSim.sim_initial sim).
      gfinal. right. eapply sim_itree_simg; eauto.
      { instantiate (1:= [_]). s. eauto. }
      i. des_ifs.
      + des; subst. ss. inv INS.
        eexists. r. rewrite H. s. grind. eapply H0; eauto.
      + exfalso. exploit lookup_lt_is_Some_1; eauto.
        s. nia.
    - i. steps.
      destruct vret_src, vret_tgt. des; subst; eauto.
  Unshelve. all : exact smj_bot.
  Qed.
  
End SEMR.

Section ADEQUACY.

  Lemma adequacy_modsem
    ms_src ms_tgt
    (SIM : MSim.t ms_src ms_tgt)
    (WF : ModSem.wf ms_src)
    :
    Beh.of_itree (ModSem.compile ms_tgt)
    <1=
    Beh.of_itree (ModSem.compile ms_src).
  Proof.
    ii. eapply adequacy_local_aux; eauto.
  Qed.
  
End ADEQUACY.

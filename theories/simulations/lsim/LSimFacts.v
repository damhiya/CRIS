Require Import Common.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import LSim.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Adequacy - Part 1. ( Divided to resolve the dependency issue. ) *)
Definition b2smj (b : bool) : smj := if b then smj_mid else smj_bot.

Lemma lsim_gsim
    ms_src ms_tgt
    (MSIM : LSim.t ms_src ms_tgt)
    (WFS : LMod.wf ms_src)
    w ps pt my_tid itrs_src itrs_tgt st_src st_tgt
    (EQS : List.length w = List.length itrs_src)
    (EQT : List.length w = List.length itrs_tgt)
    (* (TID : my_tid < nths) *)
    (WLEN : my_tid < List.length w)
    (SIM : ∀ tid ps0 pt0 itr_src itr_tgt w0 st_src0 st_tgt0
      (INS : base.lookup tid itrs_src = Some itr_src)
      (INT : base.lookup tid itrs_tgt = Some itr_tgt)
      (TID : tid < List.length w0)
      (FLG : if Nat.eq_dec tid my_tid then ps0 = ps ∧ pt0 = pt else ps0 = true ∧ pt0 = true)
      (WLE : if Nat.eq_dec tid my_tid then w0 = w else le_mine MSIM.(LSim.wle) tid w w0)
      (WF : if Nat.eq_dec tid my_tid then st_src0 = st_src ∧ st_tgt0 = st_tgt else MSIM.(LSim.wf) w0 (st_src0, st_tgt0)),
        ∃ wany,
          lsim (LMod.fnsems ms_src) (LMod.fnsems ms_tgt) (LSim.winit MSIM) (LSim.wf MSIM) (LSim.wle MSIM)
            tid top2 wany ps0 pt0 w0 (st_src0, itr_src) (st_tgt0, itr_tgt)) :
  gsim (λ '(st_src, ret_src) '(st_tgt, ret_tgt), ret_src = ret_tgt) (b2smj ps) (b2smj pt)
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog ms_src)) (my_tid, itrs_src)) st_src)
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog ms_tgt)) (my_tid, itrs_tgt)) st_tgt).
Proof.
  unfold LModTr.interp_stateE. 
  ginit. revert_until WFS. gcofix CIH. i.
  destruct (base.lookup my_tid itrs_src) eqn : LKS; cycle 1.
  { exfalso. exploit lookup_ge_None_1; eauto. i. nia. }
  destruct (base.lookup my_tid itrs_tgt) eqn : LKT; cycle 1.
  { exfalso. exploit lookup_ge_None_1; eauto. i. nia. }
  hexploit (SIM my_tid ps pt); eauto; try by des_ifs.
  i. des.
  remember (st_src, i) as src. remember (st_tgt, i0) as tgt.
  move H before CIH. revert SIM. revert_until H.
  pattern ps, pt, w, src, tgt.
  eapply lsim_ind, H. clear H. i. subst.

  inv PR.

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind. des_ifs.
    + grind. zstep_l. zstep_r. zstep. rr in RET. des; subst; eauto.
    + unfold triggerUB, LModTr.pure_state. do 2 zstep_l.
  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unfold triggerUB, LModTr.pure_state. grind. do 2 zstep_l. }
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unshelve eapply LSim.sim_fnsems in Heq; et. des.
      erewrite Heq0 in Heq. ss.
    }
    grind. rename Heq into FIND.
    zstep_l. zstep_r.
    
    zprogress.
    gbase. eapply (CIH w1 true true); eauto; try by inv WLE; zsimpl_len.

    i. guardH FLG. des_ifs; des; subst; cycle 1.
    { rewrite list_lookup_insert_ne in INS; try nia.
      rewrite list_lookup_insert_ne in INT; try nia.
      eapply SIM; eauto; des_ifs.
      eapply le_mine_trans; [apply MSIM| |eauto].
      rr in WLE. des. rr. split; try nia. i. rewrite <-WLE1; try nia.
      rewrite IN. esplits; eauto. apply MSIM.
    }

    rewrite !list_lookup_insert in INS; try nia. inv INS.
    rewrite !list_lookup_insert in INT; try nia. inv INT.
    esplits. ginit. 
    guclo lbindC_spec. econs.
    { eapply MSIM in FIND. des.
      rewrite FIND in Heq0. inv Heq0.
      eapply lsim_flag_down. gfinal. right.
      eapply FIND0; eauto.
    }
    
    i. rr in SIM0. des; subst.
    do 2 (guclo lsim_indC_spec; econs). grind.
    gfinal. right. eapply K; eauto.
    (* rewrite length_insert in WF0. nia. *)

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LModTr.pure_state. grind. zstep. zostep_l. zostep_r. subst.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. eapply K.
    + rewrite list_lookup_insert_ne in INS; try nia. inv INS.
      rewrite list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; des_ifs; eauto.

  - rewrite unfold_iterV. s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. zostep_l.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    { do 2 f_equal. extensionalities. grind. }
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right.
        erewrite equal_f; eauto. do 3 f_equal. extensionalities. grind.
      }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. zostep_r.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    { do 2 f_equal. extensionalities. grind. }
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right.
        erewrite f_equal; eauto. do 2 f_equal. extensionalities. grind.
      }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind. zostep_l.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind. zostep_r.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind.
    unfold LModTr.pure_state at 1.
    grind. zstep_l. esplits. zostep_l.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT.
    grind. unfold LModTr.pure_state at 2.
    grind. zstep_r. zostep_r.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS.
    grind. unfold LModTr.pure_state at 1.
    grind. zstep_l. zostep_l. grind.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT.
    grind. unfold LModTr.pure_state at 2.
    grind. zstep_r. esplits. zostep_r.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind. zostep_l.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind. zostep_r.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo lflagC_spec. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite !unfold_iterV /= LKS LKT. grind.

    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unfold triggerUB, LModTr.pure_state. grind. do 2 zstep_l. }
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unshelve eapply LSim.sim_fnsems in Heq; et. des. erewrite Heq0 in Heq. ss. }
    grind. rename Heq into FIND.

    zstep_l. zstep_r. zprogress.
    gbase. eapply (CIH _ true true).
    { instantiate (1:=x2++[LSim.winit MSIM]). rewrite !length_app !length_insert. eauto. }
    { rewrite !length_app /= !length_insert. nia. }
    { rewrite length_app. nia. }
    i. des_ifs; des; subst.
    + rewrite lookup_app_l in INS; cycle 1.
      { rewrite length_insert. nia. }
      rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite lookup_app_l in INT; cycle 1.
      { rewrite length_insert. nia. }
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. s.
      move: K; rewrite -EQT -EQS; intros K. eapply K.
    + assert (DEC : tid < List.length itrs_tgt \/ tid = List.length itrs_tgt).
      { apply lookup_lt_Some in INS. rewrite length_app in INS. ss.
        rewrite length_insert in INS. nia.
      }
      des.
      { rewrite lookup_app_l in INS; cycle 1.
        { rewrite length_insert. nia. }
        rewrite list_lookup_insert_ne in INS; try nia.
        rewrite lookup_app_l in INT; cycle 1.
        { rewrite length_insert. nia. }
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs. destruct WLE. split.
        { rewrite length_app in H. ss. nia. }
        ii. eapply H0. rewrite lookup_app_l; eauto using lookup_lt_Some.
      }
      subst.
      rewrite (list_lookup_middle _ []) in INS; cycle 1.
      { rewrite length_insert. nia. }
      inv INS.
      rewrite (list_lookup_middle _ []) in INT; cycle 1.
      { rewrite length_insert. eauto. }
      inv INT.
      
      esplits.
      eapply MSIM in FIND. des. rewrite FIND in Heq0. inv Heq0.
      ginit. eapply lsim_flag_down. gfinal. right.
      eapply lsim_mon_rr, FIND0; et.

  - rewrite !unfold_iterV /= LKS LKT. grind.
    zstep_l. zstep_r. zprogress.
    assert (DEC : tid < List.length itrs_src \/ tid >= List.length itrs_src) by nia.
    des; cycle 1.
    { rewrite unfold_iterV. s.
      rewrite lookup_ge_None_2; try (rewrite length_insert; nia).
      s. grind. unfold triggerUB. grind. unfold LModTr.pure_state. grind.
      do 2 zstep_l. }

    gbase. eapply (CIH w1 true true); eauto.
    { rewrite !length_insert. inv WLE. nia. }
    { rewrite !length_insert. inv WLE. nia. }
    { inv WLE; nia. }

    i. des_ifs; des; subst.
    { assert (DEC' : tid = my_tid \/ tid ≠ my_tid) by nia; des; subst.
      - rewrite !list_lookup_insert in INS; try nia. inv INS.
        rewrite !list_lookup_insert in INT; try nia. inv INT.
        eexists. eapply K; eauto.
        apply le_mine_refl. apply MSIM.
      - rewrite list_lookup_insert_ne in INS; try nia.
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs; eauto.
        split.
        { inv WLE; try nia. }
        ii. esplits; eauto.
        { inv WLE; hexploit H0; eauto. intros <-; eauto. }
        { apply LSim.wle_refl. }
    }
    { assert (DEC' : tid0 = my_tid \/ tid0 ≠ my_tid) by nia; des; subst.
      - rewrite !list_lookup_insert in INS; try nia. inv INS.
        rewrite !list_lookup_insert in INT; try nia. inv INT.
        eexists. eapply K; eauto.
      - rewrite list_lookup_insert_ne in INS; try nia.
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs; eauto.
        eapply le_mine_trans; [apply MSIM| |eauto].
        destruct WLE. split; try nia.
        ii. rewrite <-H0. rewrite IN.
        esplits; eauto. apply MSIM. eauto.
    }

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LModTr.pure_state. zostep_l. zostep_r.
    (* grind. zstep. zostep_l. zostep_r. subst. *)
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. eapply K.
    + rewrite list_lookup_insert_ne in INS; try nia. inv INS.
      rewrite list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; des_ifs; eauto.

  - rewrite unfold_iterV; s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1. 
    rewrite FUN. grind. unfold triggerUB, LModTr.pure_state. grind.
    do 2 zstep_l.

  - rewrite unfold_iterV; s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1. 
    rewrite FUN. grind. unfold triggerUB, LModTr.pure_state. grind.
    do 2 zstep_l.

  - zprogress with smj_bot smj_bot _ _.
    gbase. eapply (CIH _ false false); eauto.
    i. des_ifs; cycle 1; des; subst.
    { eapply SIM; eauto; des_ifs; eauto. }

    eexists. ginit. guclo lflagC_spec.
    econs; try eassumption; eauto with paco.
    
Unshelve. all : try exact smj_top.
Qed.

Lemma lsim_adequacy_aux ms_src ms_tgt arg
    (MSIM : LSim.t ms_src ms_tgt)
    (WFS : LMod.wf ms_src) :
  (Beh.of_itree (LMod.compile ms_tgt arg)) <1= (Beh.of_itree (LMod.compile ms_src arg)).
Proof.
  eapply gsim_adequacy.
  rewrite /LMod.compile /LModTr.trans /LModTr.interp_callE.
  ginit.
  destruct (alist_find _ _) eqn: E; s; cycle 1.
  { zstep_l. }
  ired. hexploit (LSim.sim_initial MSIM); et. i; des.
  rewrite H. s. ired. specialize (H0 arg). des.
  erewrite <-(bind_ret_r (ITree.map snd _)), (bisim_is_eq (bind_map _ _ _)).
  erewrite <-(bind_ret_r (ITree.map snd _)), (bisim_is_eq (bind_map _ _ _)).
  
  guclo bindC_spec. econs; i; s.
  { gfinal. right. eapply (lsim_gsim MSIM WFS); cycle 3.
    - i. destruct tid; ss; inv INS. des; subst. eexists.
      instantiate (1:= [_]). eapply H0.
    - et.
    - et.
    - et.
  }
  { zstep. destruct vret_src, vret_tgt; ss. }
Unshelve. all: exact smj_top.  
Qed.

(* ADEQUACY *)
Lemma lsim_adequacy ms_src ms_tgt arg :
  LSim.t ms_src ms_tgt →
  LMod.wf ms_src →
  Beh.of_itree (LMod.compile ms_tgt arg) <1= Beh.of_itree (LMod.compile ms_src arg).
Proof. ii. eapply lsim_adequacy_aux; eauto. Qed.

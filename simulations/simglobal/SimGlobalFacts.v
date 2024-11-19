Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import Behavior.
Require Import Mod Mod2ITree.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
Require Import SimGlobal.
Require Import Events.

Set Implicit Arguments.

Section SPIN.

Lemma spin_nofinal
  t
  (SPIN: Beh.state_spin t)
  :
  forall retv, t <> Ret retv.
Proof.
  punfold SPIN. ii. subst. depdes SPIN; itree_clarify x.
Qed.

Lemma spin_novis
  t
  (SPIN: Beh.state_spin t)
  :
  forall I O fn args k, t <> (r <- trigger (@IO I O fn args);; k r).
Proof.
  punfold SPIN. ii. subst. depdes SPIN; itree_clarify x.
Qed.

Lemma behave_spin_spins
  t
  (SPIN: Beh.of_itree t Tr.spin)
  :
  Beh.state_spin t.
Proof.
  punfold SPIN. remember Tr.spin as tr. revert Heqtr.
  pattern t, tr. eapply Beh.of_itree_tarski, SPIN.
  i. subst. unfold Beh.state_spin in *.
  depdes PR; eauto; pstep; des; econs; eauto.
Qed.

Lemma spin_take
  X k x
  (SPIN: Beh.state_spin (x <- trigger (Take X);; k x))
  :
  Beh.state_spin (k x).
Proof.
  punfold SPIN. depdes SPIN; des; try itree_clarify x.
  pclearbot. eauto.
Qed.

Lemma spin_choose
  X k
  (SPIN: Beh.state_spin (x <- trigger (Choose X);; k x))
  :
  ∃ x, Beh.state_spin (k x).
Proof.
  punfold SPIN. depdes SPIN; des; try itree_clarify x.
  pclearbot. eauto.
Qed.

Lemma spin_tau
  t
  (SPIN: Beh.state_spin (tau;; t))
  :
  Beh.state_spin t.
Proof.
  punfold SPIN. depdes SPIN; pclearbot; eauto; itree_clarify x.
Qed.

End SPIN.

Section ADEQUACY.

  Lemma simg_adequacy_spin_aux
    (r : _ -> Prop)
    (CIH : ∀ ps pt itr_src itr_tgt,
        simg eq ps pt itr_src itr_tgt → Beh.state_spin itr_tgt → r itr_src)
    ps'
    (PRE: ∀ ps pt itr_src itr_tgt
             (LT: smj_ltb ps ps')
             (SIM : simg eq ps pt itr_src itr_tgt)
             (SPIN: Beh.state_spin itr_tgt),
        gpaco1 Beh._state_spin (cpn1 Beh._state_spin) bot1 r itr_src)
    ps pt itr_src itr_tgt
    (LE: smj_le ps ps')
    (SIM : simg eq ps pt itr_src itr_tgt)
    (SPIN: Beh.state_spin itr_tgt)
    :
    gpaco1 Beh._state_spin (cpn1 Beh._state_spin) bot1 r itr_src.
  Proof.
    revert LE SPIN. pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. clear - CIH PRE.
    intros ps pt itr_src itr_tgt SIM LT SPIN.
    depdes SIM; des; subst.
    - exfalso. eapply spin_nofinal; eauto.
    - exfalso. eapply spin_novis; eauto.
    - gstep. econs. gbase. eapply CIH; eauto.
    - eapply spin_tau in SPIN. eapply gpaco1_mon; eauto.
    - gstep. econs. esplits. gbase. eapply CIH; eauto.
    - eapply spin_choose in SPIN. des.
      eapply gpaco1_mon; try eapply SIM; eauto.
    - gstep. econs. i. gbase. eapply CIH; eauto. apply SIM.
    - eapply spin_take in SPIN. eauto.
    - eapply PRE; eauto.
      destruct LT; subst; eauto using smj_ltb_trans.
  Qed.
           
  Lemma simg_adequacy_spin
    ps pt itr_src itr_tgt
    (SIM: simg eq ps pt itr_src itr_tgt)
    (SPIN: Beh.state_spin itr_tgt)
    :
    Beh.of_itree itr_src Tr.spin.
  Proof.
    pstep. do 2 econs.
    ginit. revert_until ps. revert ps. gcofix CIH. i.
    do 3 (eapply simg_adequacy_spin_aux; try (by left; refl); eauto; i).
    exfalso. destruct ps2; ss. destruct b, ps1; ss.
    destruct b; ss. destruct ps0; ss.
  Qed.

  Local Ltac auto_simg SIM0 SIM1 x x0 x1 :=
    try itree_clarify x;
    try by des; hdes; eauto; pstep; do 2 econs; i; eauto 7;
           first [exploit SIM1|exploit SIM0]; eauto;
           i; esplits; first [punfold x1|punfold x0]; eauto.

  Lemma simg_adequacy_ret_aux
    pt' retv
    (PRE: ∀ ps pt itr_src
             (LE: smj_ltb pt pt')
             (SIM: simg eq ps pt itr_src (Ret retv)),
        Beh.of_itree itr_src (Tr.done retv))
    ps pt itr_src
    (LE: smj_le pt pt')
    (SIM: simg eq ps pt itr_src (Ret retv))
    :
    Beh.of_itree itr_src (Tr.done retv).
  Proof.
    remember (Ret retv) as itr_tgt eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. clear - PRE.
    intros ps pt itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM; auto_simg SIM0 SIM1 x x0 x1.
    eapply PRE; eauto.
    destruct LE; subst; eauto using smj_ltb_trans.
  Qed.
  
  Lemma simg_adequacy_ret
    retv ps pt itr_src
    (SIM: simg eq ps pt itr_src (Ret retv))
    :
    Beh.of_itree itr_src (Tr.done retv).
  Proof.
    do 3 (eapply simg_adequacy_ret_aux; try (by left; refl); eauto; i).
    exfalso. destruct pt2; ss. destruct b, pt1; ss.
    destruct b; ss. destruct pt0; ss.
  Qed.

  Lemma simg_adequacy_tau_aux
    pt' r itr_tgt tr
    (STEP: ∀ ps pt itr_src
              (SIM: simg eq ps pt itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    (PRE: ∀ ps pt itr_src              
             (LE: smj_ltb pt pt')
             (SIM: simg eq ps pt itr_src (tau;; itr_tgt)),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src
    (LE: smj_le pt pt')
    (SIM: simg eq ps pt itr_src (tau;; itr_tgt))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (tau;; itr_tgt) as itr_tgt' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, itr_src, itr_tgt'.
    eapply simg_ind, SIM. clear - STEP PRE.
    intros ps pt itr_src itr_tgt' SIM LE EQ. subst.
    depdes SIM; auto_simg SIM0 SIM1 x x0 x1.
    eapply PRE; eauto.
    destruct LE; subst; eauto using smj_ltb_trans.
  Qed.
  
  Lemma simg_adequacy_tau
    r itr_tgt tr
    (STEP: ∀ ps pt itr_src
              (SIM: simg eq ps pt itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src 
    (SIM: simg eq ps pt itr_src (tau;; itr_tgt))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    do 3 (eapply simg_adequacy_tau_aux; try (by left; refl); eauto; i).
    exfalso. destruct pt2; ss. destruct b, pt1; ss.
    destruct b; ss. destruct pt0; ss.
  Qed.

  Lemma simg_adequacy_io_aux
    pt' r I O fn args (retv: O) k tr
    (CIH: ∀ ps pt itr_src itr_tgt
             (SIM: simg eq ps pt itr_src itr_tgt),
        Beh.of_itree itr_tgt <1= r itr_src)
    (BEH: Beh.of_itree (k retv) tr)
    (PRE: ∀ ps pt itr_src
             (LE: smj_ltb pt pt')
             (SIM: simg eq ps pt itr_src (r <- trigger (@IO I O fn args);; k r)),
        paco2 Beh._of_itree r itr_src (Tr.cons (obs_io fn args retv) tr))
    ps pt itr_src 
    (LE: smj_le pt pt')
    (SIM: simg eq ps pt itr_src (r <- trigger (@IO I O fn args);; k r))
    :
    paco2 Beh._of_itree r itr_src (Tr.cons (obs_io fn args retv) tr).
  Proof.
    remember (r <- trigger (@IO I O fn args);; k r) as itr_tgt eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. clear - CIH BEH PRE.
    intros ps pt itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM; auto_simg SIM0 SIM1 x x0 x1.
    eapply PRE; eauto.
    destruct LE; subst; eauto using smj_ltb_trans.
  Qed.
  
  Lemma simg_adequacy_io
    r I O fn args (retv: O) k tr
    (CIH: ∀ ps pt itr_src itr_tgt
             (SIM: simg eq ps pt itr_src itr_tgt),
        Beh.of_itree itr_tgt <1= r itr_src)
    ps pt itr_src 
    (SIM: simg eq ps pt itr_src (r <- trigger (@IO I O fn args);; k r))
    (BEH: Beh.of_itree (k retv) tr)
    :
    paco2 Beh._of_itree r itr_src (Tr.cons (obs_io fn args retv) tr).
  Proof.
    do 3 (eapply simg_adequacy_io_aux; try (by left; refl); eauto; i).
    exfalso. destruct pt2; ss. destruct b, pt1; ss.
    destruct b; ss. destruct pt0; ss.
  Qed.

  Lemma simg_adequacy_choose_aux
    pt' r X retv k tr
    (STEP: ∀ ps pt itr_src
              (SIM: simg eq ps pt itr_src (k retv)),
        paco2 Beh._of_itree r itr_src tr)
    (BEH: Beh.of_itree (k retv) tr)
    (PRE: ∀ ps pt itr_src
             (LE: smj_ltb pt pt')
             (SIM: simg eq ps pt itr_src (r <- trigger (Choose X);; k r)),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src
    (LE: smj_le pt pt')
    (SIM: simg eq ps pt itr_src (r <- trigger (Choose X);; k r))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (r <- trigger (Choose X);; k r) as itr_tgt eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. clear - STEP BEH PRE.
    intros ps pt itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM; auto_simg SIM0 SIM1 x x0 x1.
    eapply PRE; eauto.
    destruct LE; subst; eauto using smj_ltb_trans.
  Qed.

  Lemma simg_adequacy_choose
    r X retv k tr
    (STEP: ∀ ps pt itr_src
              (SIM: simg eq ps pt itr_src (k retv)),
        paco2 Beh._of_itree r itr_src tr)
    (BEH: Beh.of_itree (k retv) tr)
    ps pt itr_src 
    (SIM: simg eq ps pt itr_src (r <- trigger (Choose X);; k r))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    do 3 (eapply simg_adequacy_choose_aux; try (by left; refl); eauto; i).
    exfalso. destruct pt2; ss. destruct b, pt1; ss.
    destruct b; ss. destruct pt0; ss.
  Qed.

  Lemma simg_adequacy_take_aux
    pt' r X k tr
    (STEP: ∀ ps pt itr_src retv
              (SIM: simg eq ps pt itr_src (k retv)),
        paco2 Beh._of_itree r itr_src tr)
    (BEH: ∀ retv, Beh.of_itree (k retv) tr)
    (PRE: ∀ ps pt itr_src
             (LE: smj_ltb pt pt')
             (SIM: simg eq ps pt itr_src (r <- trigger (Take X);; k r)),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src
    (LE: smj_le pt pt')
    (SIM: simg eq ps pt itr_src (r <- trigger (Take X);; k r))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (r <- trigger (Take X);; k r) as itr_tgt eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. clear - STEP BEH PRE.
    intros ps pt itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM; auto_simg SIM0 SIM1 x x0 x1.
    eapply PRE; eauto.
    destruct LE; subst; eauto using smj_ltb_trans.
  Qed.

  Lemma simg_adequacy_take
    r X k tr
    (STEP: ∀ ps pt itr_src retv
              (SIM: simg eq ps pt itr_src (k retv)),
        paco2 Beh._of_itree r itr_src tr)
    (BEH: ∀ retv, Beh.of_itree (k retv) tr)
    ps pt itr_src
    (SIM: simg eq ps pt itr_src (r <- trigger (Take X);; k r))
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    do 3 (eapply simg_adequacy_take_aux; try (by left; refl); eauto; i).
    exfalso. destruct pt2; ss. destruct b, pt1; ss.
    destruct b; ss. destruct pt0; ss.
  Qed.
  
  Theorem adequacy_global_itree ps pt itr_src itr_tgt
    (SIM: simg eq ps pt itr_src itr_tgt)
    :
    Beh.of_itree itr_tgt <1= Beh.of_itree itr_src.
  Proof.
    revert_until ps. revert ps. pcofix CIH.
    i. rename x0 into tr. revert ps pt itr_src SIM.
    pattern itr_tgt, tr. eapply Beh.of_itree_ind, PR. clear -CIH. i.
    depdes PR; des; hdes.
    - eapply paco2_mon; try eapply simg_adequacy_ret; eauto; ss.
    - eapply paco2_mon; try eapply simg_adequacy_spin; eauto; ss.
    - eapply paco2_mon; try eapply simg_adequacy_tau; eauto; ss.
    - eapply paco2_mon; try eapply simg_adequacy_io; eauto; ss.
    - eapply paco2_mon; try eapply simg_adequacy_choose; eauto; ss.
    - eapply paco2_mon; try eapply simg_adequacy_take; eauto; ss.
  Qed.

  Theorem adequacy_global (ms_src ms_tgt: ModSem.t) ps pt
    (SIM: simg eq ps pt (@ModSem.compile ms_src) (@ModSem.compile ms_tgt))
    :
    Beh.of_itree (@ModSem.compile ms_tgt) <1= Beh.of_itree (@ModSem.compile ms_src).
  Proof.
    eapply adequacy_global_itree. eauto.
  Qed.
  
End ADEQUACY.

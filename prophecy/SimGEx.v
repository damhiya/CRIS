From stdpp Require Import base strings.
Require Import CRIS LModTr.
Require Import ExtendedBehavior.

Ltac clexteq :=
  hrepeat do 1
    match goal with
    | H : existT ?x _ = existT ?x _ |- _ => apply inj_pair2 in H; clarify
    end.

Ltac fclarify :=
  match goal with
  | H : existT ?x (fun _ : fin 1 => _) = existT ?x (fun _ : fin 1 => _) |- _ =>
      apply inj_pair2 in H;
      apply (f_equal (fun y => y 0%fin)) in H; clarify
  end.

Section SIMG.

  Hint Constructors _extr_spin : core.
  Hint Unfold extr_spin : core.
  Hint Resolve extr_spin_mon: paco.
  Hint Resolve cpn1_wcompat: paco.

  Variant simg_ex_def
    (coself : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop)
    (self : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop)
    : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop :=

    | simg_ex_ret ps pt retv
      : simg_ex_def coself self ps pt (ExTr.done retv) (Ret retv) (Ret retv)

    | simg_ex_abort ps pt itr_src itr_tgt
      : simg_ex_def coself self ps pt (ExTr.abort) itr_src itr_tgt

    | simg_ex_hang ps pt
        I O (ktr_src0 : O -> itree coreE Any.t) (ktr_tgt0 : O -> itree coreE Any.t) fn (varg : I)
      : simg_ex_def coself self ps pt (ExTr.hang (obs_out (prefix_io +:+ fn) varg)) (trigger (IO fn varg) >>= ktr_src0) (trigger (IO (prefix_io +:+ fn) varg) >>= ktr_tgt0)
                 
    | simg_ex_interact_normal ps pt ps0 pt0
        I O ktr_src0 ktr_tgt0 fn (varg : I) (vret : O) extr
        (SIM : self ps0 pt0 extr (ktr_src0 vret) (ktr_tgt0 vret))
      : simg_ex_def coself self ps pt (ExTr.interact (obs_io (prefix_io +:+ fn) varg vret) extr) (trigger (IO fn varg) >>= ktr_src0) (trigger (IO (prefix_io +:+ fn) varg) >>= ktr_tgt0)
    | simg_ex_interact_proph ps pt pt0
        I O itr_src0 ktr_tgt0 fn (varg : I) (vret : O) extr
        (SIM : self ps pt0 extr itr_src0 (ktr_tgt0 vret))
      : simg_ex_def coself self ps pt (ExTr.interact (obs_io (prefix_proph +:+ fn) varg vret) extr) itr_src0 (trigger (IO (prefix_proph +:+ fn) varg) >>= ktr_tgt0)

    | simg_ex_tauR ps pt pt0
        itr_src0 itr_tgt0 extr
        (SIM : self ps pt0 extr itr_src0 itr_tgt0)
      : simg_ex_def coself self ps pt (ExTr.tau extr) (itr_src0) (tau;; itr_tgt0)
                 
    | simg_ex_tauL ps pt ps0 extr
        itr_src0 itr_tgt0
        (SIM : self ps0 pt extr itr_src0 itr_tgt0)
      : simg_ex_def coself self ps pt extr (tau;; itr_src0) (itr_tgt0)
                 
    | simg_ex_chooseR ps pt pt0
        X x itr_src0 ktr_tgt0 extr
        (SIM : self ps pt0 extr itr_src0 (ktr_tgt0 x))
      : simg_ex_def coself self ps pt (ExTr.choose X x extr) (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

    | simg_ex_chooseL ps pt ps0
        X ktr_src0 itr_tgt0 extr
        (SIM : exists x, self ps0 pt extr (ktr_src0 x) itr_tgt0)
      : simg_ex_def coself self ps pt extr (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
                 
                 
    | simg_ex_takeR ps pt pt0
        X itr_src0 ktr_tgt0 extr
        (SIM : exists x, self ps pt0 extr itr_src0 (ktr_tgt0 x))
      : simg_ex_def coself self ps pt (ExTr.take X extr) (itr_src0) (trigger (Take X) >>= ktr_tgt0)

    | simg_ex_takeL ps pt ps0
        X ktr_src0 itr_tgt0 extr
        (SIM : forall x, self ps0 pt extr (ktr_src0 x) itr_tgt0)
      : simg_ex_def coself self ps pt extr (trigger (Take X) >>= ktr_src0) (itr_tgt0)
                 
                 
    | simg_ex_progress
        itr_src itr_tgt extr
        (SIM : coself false false extr itr_src itr_tgt)
      : simg_ex_def coself self true true extr itr_src itr_tgt.
  
  Lemma simg_ex_def_mon simg_ex simg_ex' P P'
    (LESIM : simg_ex <5= simg_ex')
    (LE : P <5= P')
    :
    simg_ex_def simg_ex P <5= simg_ex_def simg_ex' P'.
  Proof.
    i. destruct PR; des; eauto using simg_ex_def.
  Qed.

  Inductive _simg_ex simg_ex ps pt extr isrc itgt : Prop :=
  | _simg_ex_intro (SIM : simg_ex_def simg_ex (_simg_ex simg_ex) ps pt extr isrc itgt)
  .

  Lemma simg_ex_tarski
    (simg_ex : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop)
    (P : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop)
    (SIM : simg_ex_def simg_ex P <5= P)
    :
    _simg_ex simg_ex <5= P.
  Proof.
    fix IH 6. i. inv PR; inv SIM0; eapply SIM; des; econs; try eapply IH; eauto.
  Qed.

  Definition simg_ex : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop :=
    paco5 _simg_ex bot5.

  Lemma simg_ex_mon : monotone5 _simg_ex.
  Proof.
    ii. eapply simg_ex_tarski, IN. i. inv PR; eauto using _simg_ex, simg_ex_def.
  Qed.

  Hint Resolve simg_ex_mon : paco.
  Hint Resolve cpn5_wcompat : paco.

  Lemma simg_ex_ind
    (P : bool -> bool -> ExTr.t -> (itree coreE Any.t) -> (itree coreE Any.t) -> Prop)
    (SIM : simg_ex_def simg_ex (simg_ex /5\ P) <5= P)
    :
    simg_ex <5= P.
  Proof.
    i. punfold PR.
    assert (SIM' : simg_ex_def simg_ex (simg_ex /5\ P) <5= (simg_ex /5\ P)).
    { i. split; eauto. pstep. econs.
      eapply simg_ex_def_mon, PR0; eauto.
      i. ss. des. punfold PR1. }
    
    eapply simg_ex_tarski in SIM'; des; eauto.
    eapply simg_ex_mon; eauto. i. pclearbot. eauto.
  Qed.

  Lemma simg_ex_adequacy_ret_aux
    pt' retv
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.done retv) itr_src itr_tgt),
        Beh.of_itree itr_src (Tr.done retv))
    ps pt itr_src itr_tgt
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.done retv) itr_src itr_tgt)
    :
    Beh.of_itree itr_src (Tr.done retv).
  Proof.
    remember (ExTr.done retv) as extr eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr, itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE.
    intros ps pt extr itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - pfold. econs. econs.
    - des. pfold. econs. econs. pfold_reverse. apply SIM0; eauto.
    - des. pfold. econs. econs. exists x. pfold_reverse. apply SIM0; eauto.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
      apply SIM0; eauto.
    - eapply PRE; eauto.
  Qed.

  Lemma simg_ex_adequacy_ret
    retv ps pt itr_src itr_tgt
    (SIM: simg_ex ps pt (ExTr.done retv) itr_src itr_tgt)
    :
    Beh.of_itree itr_src (Tr.done retv).
  Proof.
    eapply simg_ex_adequacy_ret_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_ret_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_hang_aux
    pt' fn I (i : I)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.hang (obs_out (prefix_io ++ fn) i)) itr_src itr_tgt),
        Beh.of_itree itr_src (Tr.hang (obs_out fn i)))
    ps pt itr_src itr_tgt
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.hang (obs_out (prefix_io ++ fn) i)) itr_src itr_tgt)
    :
    Beh.of_itree itr_src (Tr.hang (obs_out fn i)).
  Proof.
    remember (ExTr.hang _) as extr eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr, itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE.
    intros ps pt extr itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - pfold. econs. econs.
    - des. pfold. econs. econs. pfold_reverse. apply SIM0; eauto.
    - des. pfold. econs. econs. exists x. pfold_reverse. apply SIM0; eauto.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
      apply SIM0; eauto.
    - eapply PRE; eauto.
  Qed.

  Lemma simg_ex_adequacy_hang
    fn I (i : I) ps pt itr_src itr_tgt
    (SIM: simg_ex ps pt (ExTr.hang (obs_out (prefix_io ++ fn) i)) itr_src itr_tgt)
    :
    Beh.of_itree itr_src (Tr.hang (obs_out fn i)).
  Proof.
    eapply simg_ex_adequacy_hang_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_hang_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_interact_normal_aux r
    pt' fn I O (i : I) (o : O) tr extr
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_io ++ fn) i o) extr) itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src (Tr.interact (obs_io fn i o) tr))
    ps pt itr_src itr_tgt
    (TL : tr_extr_relation tr extr)
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_io ++ fn) i o) extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src (Tr.interact (obs_io fn i o) tr).
  Proof.
    remember (ExTr.interact _ _) as extr' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr', itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE CIH TL.
    intros ps pt extr' itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - des. pfold. econs. econs. apply (f_equal (fun y => y 0%fin)) in x; clarify. et.
    - des. pfold. econs. econs. pfold_reverse.
    - des. pfold. econs. econs. exists x. pfold_reverse.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
    - eapply paco2_mon. { eapply PRE; et. } i. clarify.
  Qed.

  Lemma simg_ex_adequacy_interact_normal r
    fn I O (i : I) (o : O) tr extr ps pt itr_src itr_tgt
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (TL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_io ++ fn) i o) extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src (Tr.interact (obs_io fn i o) tr).
  Proof.
    eapply simg_ex_adequacy_interact_normal_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_interact_normal_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_spin_aux r
    (CIH : forall (extr : ExTr.t) (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      extr_spin extr → simg_ex ps pt extr itr_src itr_tgt → r itr_src)
    ps' extr
    (PRE : forall ps pt extr itr_src itr_tgt
            (LE: ps' = true /\ ps = false)
            (SPIN: extr_spin extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        paco1 Beh._state_spin r itr_src)
    ps pt itr_src itr_tgt
    (LE: ps = true -> ps' = true)
    (SPIN: extr_spin extr)
    (SIM: simg_ex ps pt extr itr_src itr_tgt)
    :
    paco1 Beh._state_spin r itr_src.
  Proof.
    revert LE SPIN. pattern ps, pt, extr, itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - CIH PRE.
    intros ps pt extr itr_src itr_tgt SIM LT SPIN.
    depdes SIM; des; subst.
    - exfalso. punfold SPIN. inv SPIN.
    - exfalso. punfold SPIN. inv SPIN.
    - exfalso. punfold SPIN. inv SPIN.
    - exfalso. punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN. fclarify. clexteq. pclearbot. apply SIM0; et.
    - punfold SPIN. inv SPIN. fclarify. clexteq. pclearbot. apply SIM0; et.
    - pfold. econs. right. et.
    - punfold SPIN. inversion SPIN. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H2; clarify.
      pclearbot. apply SIM0; et.
    - pfold. econs. exists x. et.
    - punfold SPIN. inversion SPIN. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H1; clarify.
      pclearbot. apply SIM0; et.
    - pfold. econs. i. specialize (SIM x). des. et.
    - eapply PRE; eauto.
  Qed.

  Lemma simg_ex_adequacy_spin
    extr ps pt itr_src itr_tgt
    (SPIN : extr_spin extr)
    (SIM: simg_ex ps pt extr itr_src itr_tgt)
    :
    Beh.of_itree itr_src Tr.spin.
  Proof.
    pfold. econs. econs. revert_until extr. revert extr. pcofix CIH.
    i.
    eapply simg_ex_adequacy_spin_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_spin_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_interact_proph_aux r
    pt' fn (i : Any.t) tr extr
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_proph ++ fn) i ()) extr) itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src itr_tgt
    (TL : tr_extr_relation tr extr)
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_proph ++ fn) i ()) extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (ExTr.interact _ _) as extr' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr', itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE CIH STEP TL.
    intros ps pt extr' itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - des. apply (f_equal (fun y => y 0%fin)) in x; clarify. et.
    - des. pfold. econs. econs. pfold_reverse.
    - des. pfold. econs. econs. exists x. pfold_reverse.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
    - eapply paco2_mon. { eapply PRE; et. } i. clarify.
  Qed.

  Lemma simg_ex_adequacy_interact_proph r
    fn (i : Any.t) tr extr ps pt itr_src itr_tgt
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (TL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt (ExTr.interact (obs_io (prefix_proph ++ fn) i ()) extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    eapply simg_ex_adequacy_interact_proph_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_interact_proph_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_tau_aux r
    pt' tr extr
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.tau extr) itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src itr_tgt
    (TL : tr_extr_relation tr extr)
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.tau extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (ExTr.tau _) as extr' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr', itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE CIH STEP TL.
    intros ps pt extr' itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - des. apply (f_equal (fun y => y 0%fin)) in x; clarify. et.
    - des. pfold. econs. econs. pfold_reverse.
    - des. pfold. econs. econs. exists x. pfold_reverse.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
    - eapply paco2_mon. { eapply PRE; et. } i. clarify.
  Qed.

  Lemma simg_ex_adequacy_tau r
    tr extr ps pt itr_src itr_tgt
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (TL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt (ExTr.tau extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    eapply simg_ex_adequacy_tau_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_tau_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_choose_aux r
    X x pt' tr extr
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.choose X x extr) itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src itr_tgt
    (TL : tr_extr_relation tr extr)
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.choose X x extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (ExTr.choose _ _ _) as extr' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr', itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE CIH STEP TL.
    intros ps pt extr' itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - des. pfold. econs. econs. pfold_reverse.
    - des. apply (f_equal (fun y => y 0%fin)) in x; clarify. et.
    - des. pfold. econs. econs. exists x0. pfold_reverse.
    - des. pfold. econs. econs. i. specialize (SIM x0). des. pfold_reverse.
    - eapply paco2_mon. { eapply PRE; et. } i. clarify.
  Qed.

  Lemma simg_ex_adequacy_choose r
    X x tr extr ps pt itr_src itr_tgt
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (TL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt (ExTr.choose X x extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    eapply simg_ex_adequacy_choose_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_choose_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Lemma simg_ex_adequacy_take_aux r
    P pt' tr extr
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (PRE: ∀ ps pt itr_src itr_tgt
            (LE: pt' = true /\ pt = false)
            (SIM: simg_ex ps pt (ExTr.take P extr) itr_src itr_tgt),
        paco2 Beh._of_itree r itr_src tr)
    ps pt itr_src itr_tgt
    (TL : tr_extr_relation tr extr)
    (LE: pt = true -> pt' = true)
    (SIM: simg_ex ps pt (ExTr.take P extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    remember (ExTr.take _ _) as extr' eqn: EQ in SIM.
    revert LE EQ. pattern ps, pt, extr', itr_src, itr_tgt.
    eapply simg_ex_ind, SIM. clear - PRE CIH STEP TL.
    intros ps pt extr' itr_src itr_tgt SIM LE EQ. subst.
    depdes SIM.
    - des. pfold. econs. econs. pfold_reverse.
    - des. pfold. econs. econs. exists x. pfold_reverse.
    - des. apply (f_equal (fun y => y 0%fin)) in x; clarify. et.
    - des. pfold. econs. econs. i. specialize (SIM x). des. pfold_reverse.
    - eapply paco2_mon. { eapply PRE; et. } i. clarify.
  Qed.

  Lemma simg_ex_adequacy_take r
    P tr extr ps pt itr_src itr_tgt
    (STEP: ∀ (ps pt : bool) (itr_src itr_tgt : itree coreE Any.t),
      simg_ex ps pt extr itr_src itr_tgt → paco2 Beh._of_itree r itr_src tr)
    (CIH: ∀ ps pt extr tr itr_src itr_tgt
            (TL : tr_extr_relation tr extr)
            (SIM: simg_ex ps pt extr itr_src itr_tgt),
        r itr_src tr)
    (TL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt (ExTr.take P extr) itr_src itr_tgt)
    :
    paco2 Beh._of_itree r itr_src tr.
  Proof.
    eapply simg_ex_adequacy_take_aux; try (by left; refl); eauto; i. des. clarify.
    eapply simg_ex_adequacy_take_aux; try (by left; refl); eauto; i. des. clarify.
  Qed.

  Theorem simg_ex_adequacy ps pt extr tr itr_src itr_tgt
    (TREL : tr_extr_relation tr extr)
    (SIM: simg_ex ps pt extr itr_src itr_tgt)
    :
    Beh.of_itree itr_src tr.
  Proof.
    revert_until ps. revert ps. pcofix CIH.
    i. revert ps pt itr_src itr_tgt SIM. 
    pattern tr, extr. eapply tr_extr_relation_ind, TREL. clear -CIH. i.
    depdes PR; des; hdes.
    - eapply paco2_mon; try eapply simg_ex_adequacy_ret; eauto; ss.
    - pstep. econs. econs.
    - eapply paco2_mon; try eapply simg_ex_adequacy_hang; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_interact_normal; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_spin; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_interact_proph; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_tau; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_choose; eauto; ss.
    - eapply paco2_mon; try eapply simg_ex_adequacy_take; eauto; ss.
  Qed.

  Definition wsimg r ps pt extr itr_src itr_tgt : Prop :=
    paco2 ExBeh._of_itreeF bot2 itr_tgt extr
    -> paco5 _simg_ex r ps pt extr itr_src itr_tgt.

  Lemma wsimg_tau_src
      r ps pt extr itr_src itr_tgt
      (NEXT : wsimg r true pt extr itr_src itr_tgt) :
    wsimg r ps pt extr (tau;; itr_src) itr_tgt.
  Proof. ii. pfold. econs. econs. pfold_reverse. Qed.

  Lemma wsimg_take_src
      r ps pt extr P ktr_src itr_tgt
      (NEXT : forall p : P, wsimg r true pt extr (ktr_src p) itr_tgt) :
    wsimg r ps pt extr (x <- trigger (Take P);; ktr_src x) itr_tgt.
  Proof. ii. pfold. econs. econs. i. pfold_reverse. apply NEXT. et. Qed.

  Lemma wsimg_choose_src
      r ps pt extr X ktr_src itr_tgt
      (NEXT : exists x : X, wsimg r true pt extr (ktr_src x) itr_tgt) :
    wsimg r ps pt extr (x <- trigger (Choose X);; ktr_src x) itr_tgt.
  Proof. ii. des. pfold. econs. econs. exists x. pfold_reverse. Qed.

  Lemma wsimg_tau_tgt
      r ps pt extr itr_src itr_tgt
      (NEXT :
        forall extr' (EQ : extr = ExTr.tau extr'),
          wsimg r ps true extr' itr_src itr_tgt) :
    wsimg r ps pt extr itr_src (tau;; itr_tgt).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - pclearbot. pfold. econs. econs. pfold_reverse.
      apply NEXT; et.
  Qed.

  Lemma wsimg_choose_tgt
      r ps pt extr X itr_src ktr_tgt
      (NEXT :
        forall x extr' (EQ : extr = ExTr.choose X x extr'),
          wsimg r ps true extr' itr_src (ktr_tgt x)) :
    wsimg r ps pt extr itr_src (x <- trigger (Choose X);; ktr_tgt x).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - pclearbot. pfold. econs. econs. pfold_reverse.
      apply NEXT; et.
  Qed.

  Lemma wsimg_take_tgt
      r ps pt extr P itr_src ktr_tgt
      (NEXT :
        forall extr' (EQ : extr = ExTr.take P extr'),
          exists p : P, wsimg r ps true extr' itr_src (ktr_tgt p)) :
    wsimg r ps pt extr itr_src (p <- trigger (Take P);; ktr_tgt p).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - hexploit NEXT; et. i. des. pfold. econs. econs.
      exists p. pfold_reverse. apply H. pclearbot. apply STEP.
  Qed.

  Lemma wsimg_io_normal
      r ps pt extr fn I O (arg : I) ktr_src ktr_tgt
      (NEXT :
        forall extr' (ret : O) (EQ : extr = ExTr.interact (obs_io (prefix_io +:+ fn) arg ret) extr'),
          wsimg r true true extr' (ktr_src ret) (ktr_tgt ret)) :
    wsimg r ps pt extr (o <- trigger (IO fn arg);; ktr_src o) (o <- trigger (IO (prefix_io +:+ fn) arg);; ktr_tgt o).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - pfold. econs. econs.
    - hexploit NEXT; et. i. pfold. econs. econs. pclearbot. pfold_reverse.
  Qed.

  Lemma wsimg_io_proph
      r ps pt extr fn I O (arg : I) itr_src ktr_tgt
      (NEXT :
        forall extr' (ret : O) (EQ : extr = ExTr.interact (obs_io (prefix_proph +:+ fn) arg ret) extr'),
          wsimg r ps true extr' itr_src (ktr_tgt ret)) :
    wsimg r ps pt extr itr_src (o <- trigger (IO (prefix_proph +:+ fn) arg);; ktr_tgt o).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - hexploit NEXT; et. i. pfold. econs. econs. pclearbot. pfold_reverse.
  Qed.

  Lemma wsimg_ret
      r ps pt retv extr :
    wsimg r ps pt extr (Ret retv) (Ret retv).
  Proof.
    ii. punfold H. inv H; try itree_clarify H1.
    - pfold. econs. econs.
    - pfold. econs. econs.
  Qed.

  Lemma wsimg_endsim
      r extr itr_src itr_tgt
      (NEXT : paco2 ExBeh._of_itreeF bot2 itr_tgt extr ->
              r false false extr itr_src itr_tgt) :
    wsimg r true true extr itr_src itr_tgt.
  Proof. ii. pfold. econs. econs. et. Qed.

End SIMG.

Ltac step_r :=
  match goal with
  | |- wsimg _ _ _ _ _ ?itr_tgt =>
      match itr_tgt with
      | tau;; _ =>
          apply wsimg_tau_tgt;
          let extr' := fresh "extr" in
          intros extr' ?; clarify; rename extr' into extr
      | _ <- trigger (resum IFun _ (Choose _));; _ =>
          apply wsimg_choose_tgt;
          let extr' := fresh "extr" in
          intros ? extr' ?; clarify; rename extr' into extr
      | _ <- trigger (resum IFun _ (Take _));; _ =>
          apply wsimg_take_tgt;
          let extr' := fresh "extr" in
          intros extr' ?; clarify; rename extr' into extr
      end
  end.

Ltac step_l :=
  match goal with
  | |- wsimg _ _ _ _ ?itr_src _ =>
      match itr_src with
      | tau;; _ => apply wsimg_tau_src
      | _ <- trigger (resum IFun _ (Take _));; _ => apply wsimg_take_src; intros
      | _ <- trigger (resum IFun _ (resum IFun _ (Take _)));; _ => apply wsimg_take_src; intros
      | _ <- trigger (resum IFun _ (Choose _));; _ => apply wsimg_choose_src
      | _ <- trigger (resum IFun _ (resum IFun _ (Choose _)));; _ => apply wsimg_choose_src; intros
      end
  end.

Ltac steps_r := hrepeat do 1 step_r.
Ltac steps_l := hrepeat do 1 step_l.

Ltac clearub := unfold triggerUB; grind; unfold LModTr.pure_state; grind; steps_l; clarify.

Ltac endsim := apply wsimg_endsim; i;
               match goal with
               | H : context [?r false false _ _ _] |- _ =>
                   eapply H; et
               end.

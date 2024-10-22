Require Import Coqlib.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.

Section BEHAVES.

  Variable L : semantics.

  Theorem of_state_ind2 :
    forall (P : _ -> _ -> Prop),
      (forall st0 retv, state_sort L st0 = final retv -> P st0 (Tr.done retv)) ->
      (forall st0, Beh.state_spin L st0 -> P st0 Tr.spin) ->
      (forall st0, P st0 Tr.nb) ->

      (forall st0 st1 ev evs
              (SRT : state_sort L st0 = vis)
              (STEP : _.(step) st0 (Some ev) st1)
              (TL : Beh.of_state L st1 evs)
        ,
          P st0 (Tr.cons ev evs)) ->
      (forall st0 evs
              (SRT : state_sort L st0 = demonic)
              (STEP : Beh.union L st0
                       (fun e st1 =>
                          <<HD : e = None >> /\ <<TL : Beh.of_state L st1 evs >> /\ <<IH : P st1 evs>>)), P st0 evs) ->
      (forall st0 evs
              (SRT : state_sort L st0 = angelic)
              (STEP : Beh.inter L st0
                       (fun e st1 => <<HD : e = None >> /\ <<TL : Beh.of_state L st1 evs >> /\ <<IH : P st1 evs>>)),
          P st0 evs) ->
      forall s t, Beh.of_state L s t -> P s t.
  Proof.
    i. eapply Beh.of_state_ind; eauto.
    { i. eapply H3; eauto.
      unfold Beh.union in *. des. esplits; eauto.
      pfold. eapply Beh.of_state_mon; eauto.
    }
    { i. eapply H4; eauto. ii. exploit STEP; eauto.
      i. des. esplits; eauto.
      pfold. eapply Beh.of_state_mon; eauto.
    }
    { punfold H5. eapply Beh.of_state_mon; eauto.
      i. pclearbot. auto.
    }
  Qed.

  Variant of_state_indC (of_state : L.(state) -> Tr.t -> Prop) : L.(state) -> Tr.t -> Prop :=
    | of_state_indC_final
        st0 retv
        (FINAL : L.(state_sort) st0 = final retv)
      :
      of_state_indC of_state st0 (Tr.done retv)
    | of_state_indC_spin
        st0
        (SPIN : Beh.state_spin L st0)
      :
      of_state_indC of_state st0 (Tr.spin)
    | of_state_indC_nb
        st0
      :
      of_state_indC of_state st0 (Tr.nb)
    | of_state_indC_vis
        st0 st1 ev evs
        (SRT : L.(state_sort) st0 = vis)
        (STEP : _.(step) st0 (Some ev) st1)
        (TL : of_state st1 evs)
      :
      of_state_indC of_state st0 (Tr.cons ev evs)
    | of_state_indC_demonic
        st0
        evs
        (SRT : L.(state_sort) st0 = demonic)
        (STEP : Beh.union L st0 (fun e st1 => (<<HD : e = None>>) /\ (<<TL : of_state st1 evs>>)))
      :
      of_state_indC of_state st0 evs
    | of_state_indC_angelic
        st0
        evs
        (SRT : L.(state_sort) st0 = angelic)
        (STEP : Beh.inter L st0 (fun e st1 => (<<HD : e = None>>) /\ (<<TL : of_state st1 evs>>)))
      :
      of_state_indC of_state st0 evs
  .

  Lemma of_state_indC_mon:
    monotone2 of_state_indC.
  Proof.
    ii. inv IN; eauto.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto. unfold Beh.union in *. des. esplits; eauto.
    - econs 6; eauto. ii. exploit STEP; eauto. i. des. splits; auto.
  Qed.
  Hint Resolve of_state_indC_mon : paco.

  Lemma of_state_indC_spec:
    of_state_indC <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
  Proof.
    eapply wrespect2_uclo; eauto with paco.
    econs; eauto with paco.
    ii. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. eapply rclo2_base. auto. }
    { econs 5; eauto. unfold Beh.union in *. des. esplits; eauto.
      eapply Beh.of_state_mon; eauto. i. eapply rclo2_base. auto.
    }
    { econs 6; eauto. ii. exploit STEP; eauto. i. des. splits; auto.
      eapply Beh.of_state_mon; eauto. i. eapply rclo2_base. auto.
    }
  Qed.

End BEHAVES.

Lemma spin_nofinal
      L st0
      (SPIN : Beh.state_spin L st0)
  :
    forall retv, <<NOFIN : L.(state_sort) st0 <> final retv>>
.
Proof.
  punfold SPIN. inv SPIN; ii; rewrite H in *; ss.
Qed.

Lemma spin_novis
      L st0
      (SPIN : Beh.state_spin L st0)
  :
    <<NOFIN : L.(state_sort) st0 <> vis>>
.
Proof.
  punfold SPIN. inv SPIN; ii; rewrite H in *; ss.
Qed.

Lemma spin_astep
      L st0 ev st1
      (SRT : L.(state_sort) st0 = angelic)
      (STEP : _.(step) st0 ev st1)
      (SPIN : Beh.state_spin _ st0)
  :
    <<SPIN : Beh.state_spin _ st1>>
.
Proof.
  exploit wf_angelic; et. i; clarify.
  punfold SPIN. inv SPIN; rewrite SRT in *; ss.
  exploit STEP0; et. i; des. pclearbot. et.
Qed.

Section SIM.

  Variable L0 L1 : semantics.

  Variant sim_def (sim : bool -> bool -> L0.(state) -> L1.(state) -> Prop)
    (self : bool -> bool -> L0.(state) -> L1.(state) -> Prop)
    (ps0 : bool) (pt0 : bool) (st_src0 : L0.(state)) (st_tgt0 : L1.(state)) : Prop :=
  | sim_fin
      retv
      (SRT : _.(state_sort) st_src0 = final retv)
      (SRT : _.(state_sort) st_tgt0 = final retv)

  | sim_vis
      (SRT : _.(state_sort) st_src0 = vis)
      (SRT : _.(state_sort) st_tgt0 = vis)
      (SIM : forall ev st_tgt1
          (STEP : _.(step) st_tgt0 (Some ev) st_tgt1)
          ,
          exists st_src1 (STEP : _.(step) st_src0 (Some ev) st_src1),
            <<SIM : sim true true st_src1 st_tgt1>>)

  | sim_vis_stuck_tgt
      (SRT : _.(state_sort) st_tgt0 = vis)
      (STUCK : forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))

  | sim_demonic_src
      (SRT : _.(state_sort) st_src0 = demonic)
      (SIM : exists st_src1
                   (STEP : _.(step) st_src0 None st_src1)
        ,
          <<SIM : self true pt0 st_src1 st_tgt0>>)

  | sim_demonic_tgt
      (SRT : _.(state_sort) st_tgt0 = demonic)
      (SIM : forall st_tgt1
                   (STEP : _.(step) st_tgt0 None st_tgt1)
        ,
          <<SIM : self ps0 true st_src0 st_tgt1>>)

  | sim_angelic_src
      (SRT : _.(state_sort) st_src0 = angelic)
      (SIM : forall st_src1
          (STEP : _.(step) st_src0 None st_src1)
        ,
          <<SIM : self true pt0 st_src1 st_tgt0>>)

  | sim_angelic_tgt
      (SRT : _.(state_sort) st_tgt0 = angelic)
      (SIM : exists st_tgt1
          (STEP : _.(step) st_tgt0 None st_tgt1)
        ,
          <<SIM : self ps0 true st_src0 st_tgt1>>)

  | sim_progress
      (SIM : sim false false st_src0 st_tgt0)
      (SRC : ps0 = true)
      (TGT : pt0 = true)
  .

  Inductive _sim sim ps pt st_src st_tgt : Prop :=
    _sim_intro (SIM : sim_def sim (_sim sim) ps pt st_src st_tgt)
  .

  Lemma sim_ind sim (P : bool -> bool -> L0.(state) -> L1.(state) -> Prop)
    (SIM : sim_def sim (_sim sim /4\ P) <4= P)
    :
    _sim sim <4= P.
  Proof.
    fix IH 5. i. inv PR. inv SIM0; des.
    - eapply SIM. econs 1; eauto 7.
    - eapply SIM. econs 2; eauto 7.
    - eapply SIM. econs 3; eauto 7.
    - eapply SIM. econs 4; eauto 7.
    - eapply SIM. econs 5; eauto. i. hexploit SIM1; eauto.
    - eapply SIM. econs 6; eauto. i. hexploit SIM1; eauto.
    - eapply SIM. econs 7; eauto 7.
    - eapply SIM. econs 8; eauto 7.
  Qed.

  Lemma sim_mon : monotone4 _sim.
  Proof.
    ii. revert x0 x1 x2 x3 IN. eapply sim_ind. i.
    inv PR; clarify; econs.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto. }
    { econs 5; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 6; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 7; eauto. des. esplits; eauto. }
    { econs 8; eauto. }
  Qed.

  Definition sim : _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon : paco.
  Hint Resolve cpn4_wcompat : paco.

  Definition sim_indC sim := sim_def sim sim.
  
  Lemma sim_indC_mon : monotone4 sim_indC.
  Proof.
    ii. inv IN; eauto.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto. }
    { econs 5; eauto. i. hexploit SIM; eauto. }
    { econs 6; eauto. i. hexploit SIM; eauto. }
    { econs 7; eauto. des. esplits; eauto. }
    { econs 8; eauto. }
  Qed.
  Hint Resolve sim_indC_mon : paco.

  Lemma sim_indC_spec:
    sim_indC <5= gupaco4 _sim (cpn4 _sim).
  Proof.
    eapply wrespect4_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit SIM; eauto. i. des.
      esplits; eauto. eapply rclo4_base. auto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto.
      eapply sim_mon; eauto. i. eapply rclo4_base. auto.
    }
    { econs 5; eauto. i. hexploit SIM; eauto. i.
      eapply sim_mon; eauto. i. eapply rclo4_base. auto.
    }
    { econs 6; eauto. i. hexploit SIM; eauto. i.
      eapply sim_mon; eauto. i. eapply rclo4_base. auto.
    }
    { econs 7; eauto. des. esplits; eauto.
      eapply sim_mon; eauto. i. eapply rclo4_base. auto.
    }
    { econs 8; eauto. eapply rclo4_base. auto. }
  Qed.

  Variant sim_flagC (sim : bool -> bool -> L0.(state) -> L1.(state) -> Prop)
          (ps1 : bool) (pt1 : bool) (st_src : L0.(state)) (st_tgt : L1.(state)) : Prop :=
  | sim_flagC_intro
      ps0 pt0
      (SIM : sim ps0 pt0 st_src st_tgt)
      (SRC : ps0 = true -> ps1 = true)
      (TGT : pt0 = true -> pt1 = true)
  .

  Lemma sim_flagC_mon : monotone4 sim_flagC.
  Proof.
    ii. inv IN; eauto. econs; eauto.
  Qed.
  Hint Resolve sim_flagC_mon : paco.

  Lemma sim_flagC_spec:
    sim_flagC <5= gupaco4 _sim (cpn4 _sim).
  Proof.
    eapply wrespect4_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x0 x1 SRC TGT. pattern ps0, pt0, x2, x3.
    eapply sim_ind, SIM. i; inv PR; clarify; econs.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit SIM0; eauto. i. des.
      esplits; eauto. eapply rclo4_base. auto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto. }
    { econs 5; eauto. i. exploit SIM0; eauto. i. des. eauto. }
    { econs 6; eauto. i. exploit SIM0; eauto. i. des. eauto. }
    { econs 7; eauto. des. esplits; eauto. }
    { econs 8; eauto. eapply rclo4_base. auto. }
  Qed.

  Lemma sim_flag_mon:
    forall f_src0 f_tgt0 f_src1 f_tgt1 st_src st_tgt
           (SIM : sim f_src0 f_tgt0 st_src st_tgt)
           (SRC : f_src0 = true -> f_src1 = true)
           (TGT : f_tgt0 = true -> f_tgt1 = true),
      sim f_src1 f_tgt1 st_src st_tgt.
  Proof.
    ginit. i. guclo sim_flagC_spec. econs; eauto.
    gfinal. right. eauto.
  Qed.

  Record simulation : Prop := mk_simulation {
    sim_init : <<SIM : sim false false L0.(initial_state) L1.(initial_state)>>;
  }
  .

  Ltac pc H := rr in H; desH H; ss.
  Lemma adequacy_spin
        ps0 pt0 st_src0 st_tgt0
        (SIM : sim ps0 pt0 st_src0 st_tgt0)
        (SPIN : Beh.state_spin L1 st_tgt0)
    :
      <<SPIN : Beh.state_spin L0 st_src0>>
  .
  Proof.
    ginit.
    { i. eapply cpn1_wcompat; eauto. eapply Beh.state_spin_mon. }
    revert ps0 pt0 st_src0 st_tgt0 SIM SPIN. gcofix CIH.
    intros ? ? ? ? SIM. punfold SIM. pattern ps0, pt0, st_src0, st_tgt0.
    eapply sim_ind, SIM. i. inv PR; clarify.
    - (** final **)
      exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss.
    - (** vis **)
      des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss.
    - (** vis stuck **)
      exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss.
    - (** dsrc **)
      des. gstep. econs 2; eauto. esplits; eauto.
      eapply gpaco1_mon; eauto. ss.
    - (** dtgt **)
      punfold SPIN. inv SPIN; rewrite SRT in *; ss. des. pclearbot.
      exploit wf_demonic; et; i; clarify.
      exploit SIM0; et. i; des. eauto.
    - (** asrc **)
      gstep. econs 1; eauto. i.
      exploit wf_angelic; et; i; clarify.
      exploit SIM0; eauto.  i. des.
      eapply gpaco1_mon; eauto. ss.
    - (** atgt **)
      punfold SPIN. inv SPIN; rewrite SRT in *; ss. des.
      exploit STEP; eauto. i. pclearbot. eauto.
    - (** progress **)
      clear SIM. rename SIM0 into SIM. pclearbot. punfold SIM.
      remember false in SIM at 1. remember false in SIM at 1.
      clear Heqb0. revert Heqb SPIN.
      pattern b, b0, x2, x3. eapply sim_ind, SIM. i. inv PR; clarify.
      + exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; clarify.
      + exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; clarify.
      + exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss.
      + des. gstep. econs 2; auto. esplits; eauto.
        gbase. eapply CIH; eauto.
      + punfold SPIN. inv SPIN; rewrite SRT in *; clarify. des.
        exploit wf_demonic; et; i; clarify. pclearbot.
        exploit SIM0; et. i; des. eauto.
      + gstep. econs 1; auto. i.
        exploit wf_angelic; et; i; clarify.
        exploit SIM0; eauto. i. des.
        gbase. eapply CIH; eauto.
      + punfold SPIN. inv SPIN; rewrite SRT in *; clarify. des.
        exploit STEP; eauto. i. pclearbot.
        eauto.
  Qed.

  Lemma adequacy_aux
        ps0 pt0 st_src0 st_tgt0
        (SIM : sim ps0 pt0 st_src0 st_tgt0)
    :
      <<IMPR : Beh.improves (Beh.of_state L0 st_src0) (Beh.of_state L1 st_tgt0)>>
  .
  Proof.
    ginit.
    { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. }
    revert pt0 ps0 st_src0 st_tgt0 SIM. gcofix CIH.
    i. rename x2 into tr.
    revert ps0 pt0 st_src0 SIM.
    induction PR using of_state_ind2; ii; ss; rename st0 into st_tgt0.
    - (** done **)
      rename H into SRT. punfold SIM.
      revert retv SRT. pattern ps0, pt0, st_src0, st_tgt0.
      eapply sim_ind, SIM. i. inv PR; clarify.
      + rewrite SRT in *; clarify. gstep. econs; eauto.
      + rewrite SRT in *. clarify.
      + rewrite SRT0 in *. clarify.
      + des. exploit SIM0; eauto. i; des; ss.
        guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
      + rewrite SRT in *. clarify.
      + guclo of_state_indC_spec. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i. des. splits; auto.
      + rewrite SRT in *. clarify.
      + clear SIM. rename SIM0 into SIM. pclearbot. punfold SIM.
        remember false as ps1 eqn:FLAGSRC in SIM at 1.
        remember false as pt1 eqn:FLAGTGT in SIM at 1.
        clear FLAGSRC. revert FLAGTGT. revert retv SRT.
        pattern ps1, pt1, x2, x3.
        eapply sim_ind, SIM. i. inv PR; try rewrite SRT in *; clarify.
        * gstep. econs; eauto.
        * des. guclo of_state_indC_spec. econs 5; eauto.
          red. esplits; eauto.
        * guclo of_state_indC_spec. econs 6; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i. des. esplits; eauto.
    - (** spin **)
      exploit adequacy_spin; eauto. i.
      gstep. econs. et.
    - (** nb **)
      gstep. econs; eauto.
    - (** cons **)
      move SIM before CIH. revert_until SIM.
      punfold SIM. pattern ps0, pt0, st_src0, st_tgt0.
      eapply sim_ind, SIM. i. inv PR; i; try rewrite SRT in *; clarify.
      + (** vv **)
        specialize (SIM0 ev st1). apply SIM0 in STEP; clear SIM; des.
        gstep. econs 4; eauto. pc SIM. gbase. eapply CIH; eauto.
      + (** vis stuck **)
        apply STUCK in STEP. clarify.
      + (** d_ **)
        des. guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
      + (** a_ **)
        guclo of_state_indC_spec. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i. des. esplits; eauto.
      + (** progress **)
        clear SIM. rename SIM0 into SIM. pclearbot. punfold SIM.
        remember false as ps1 eqn:FLAGSRC in SIM at 1.
        remember false as pt1 eqn:FLAGTGT in SIM at 1.
        clear FLAGSRC. revert FLAGTGT ev SRT STEP.
        pattern ps1, pt1, x2, x3. eapply sim_ind, SIM. i.
        inv PR; try rewrite SRT in *; clarify.
        * exploit SIM0; eauto. i. des. pclearbot.
          gstep. econs 4; eauto. gbase. eauto.
        * exfalso. eapply STUCK; eauto.
        * des. exploit SIM0; eauto. i.
          guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
        * guclo of_state_indC_spec. econs 6; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i. des. esplits; eauto.
    - (** demonic **)
      red in STEP. des. clarify. punfold SIM.
      move SIM before CIH. revert_until SIM.
      pattern ps0, pt0, st_src0, st_tgt0.
      eapply sim_ind, SIM. i. inv PR; try rewrite SRT in *; clarify.
      + des. guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
      + hexploit SIM0; eauto. i. des. eapply IH; eauto.
      + guclo of_state_indC_spec. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i. des. esplits; eauto.
      + clear SIM. rename SIM0 into SIM.
        remember false as ps1 eqn:FLAGSRC in SIM at 1.
        remember false as pt1 eqn:FLAGTGT in SIM at 1.
        clear FLAGSRC. revert FLAGTGT st1 SRT STEP0 TL IH.
        pclearbot. punfold SIM. pattern ps1, pt1, x2, x3.
        eapply sim_ind, SIM. i. inv PR; try rewrite SRT in *; clarify.
        * des. exploit SIM0; eauto. i.
          guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
        * exploit SIM0; eauto. i. des. eapply IH; eauto.
        * guclo of_state_indC_spec. econs 6; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i. des. esplits; eauto.
    - (** angelic **)
      red in STEP. des. clarify.
      move SIM before CIH. revert_until SIM.
      punfold SIM. pattern ps0, pt0, st_src0, st_tgt0.
      eapply sim_ind, SIM. i. inv PR; try rewrite SRT in *; clarify.
      + des. guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
      + guclo of_state_indC_spec. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i. des. esplits; eauto.
      + des. exploit STEP; eauto. i. des. esplits; eauto.
      + clear SIM. rename SIM0 into SIM.
        remember false as ps1 eqn:FLAGSRC in SIM at 1.
        remember false as pt1 eqn:FLAGTGT in SIM at 1.
        clear FLAGSRC. revert FLAGTGT SRT STEP.
        pclearbot. punfold SIM. pattern ps1, pt1, x2, x3.
        eapply sim_ind, SIM. i. inv PR; try rewrite SRT in *; clarify.
        * des. guclo of_state_indC_spec. econs 5; eauto. red. esplits; eauto.
        * guclo of_state_indC_spec. econs 6; eauto. ii.
          exploit wf_angelic; try apply SRT0; et. i; clarify.
          exploit SIM0; eauto. i. des. esplits; eauto.
        * des. exploit STEP; eauto. i. des. esplits; eauto.
  Qed.

  Theorem adequacy
          (SIM : simulation)
    :
      <<IMPR : Beh.improves (Beh.of_program L0) (Beh.of_program L1)>>
  .
  Proof.
    inv SIM. des.
    eapply adequacy_aux; et.
  Qed.

End SIM.
Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon : paco.
Hint Resolve cpn4_wcompat : paco.

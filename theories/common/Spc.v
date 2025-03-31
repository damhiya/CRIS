Require Import Common.
Require Import SMod.

Set Implicit Arguments.

Create HintDb spc.
Hint Rewrite (Seal.sealing_eq "spc") : spc.

Definition to_spc `{Σ : GRA} (l : alist string fspec) : string -> option fspec :=
  fun fn => alist_find fn l.

Definition to_spc_context `{Σ : GRA} (spcu : list string) (spck : alist string fspec) :=
  to_spc (List.map (fun fn => (fn, fspec_trivial)) spcu ++ spck).

Definition to_closed_spc `{Σ : GRA} (l : alist string fspec) : string -> option fspec :=
  fun fn => match alist_find fn l with
            | Some fsp => Some fsp
            | _ => Some fspec_trivial
            end.

Ltac spc_tac :=
  match goal with
  | [ |- to_spc_context _ _ _ = _ ] =>
    unfold to_spc_context, to_spc;
    autounfold with spc; autorewrite with spc; simpl
  | [ |- to_spc ?xs _ = _ ] =>
    unfold to_spc;
    autounfold with spc; autorewrite with spc; simpl
  | [ |- to_closed_spc ?xs _ = _ ] =>
    unfold to_closed_spc;
    autounfold with spc; autorewrite with spc; simpl
  | [ |- alist_find _ ?xs = _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with spc; autorewrite with spc; simpl
    end
  | [H : alist_find _ ?xs = _ |- _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with spc in H; autorewrite with spc in H; simpl in H
    end
  | [H : to_spc_context _ _ _ = _ |- _ ] =>
    unfold to_spc_context, to_spc in H;
    autounfold with spc in H; autorewrite with spc in H; simpl in H
  | [H : to_spc ?xs _ = _ |- _ ] =>
    unfold to_spc in H;
    autounfold with spc in H; autorewrite with spc in H; simpl in H
  | [H : to_closed_spc ?xs _ = _ |- _ ] =>
    unfold to_closed_spc in H;
    autounfold with spc in H; autorewrite with spc in H; simpl in H
  end.

Section HEADER.

  Context `{Σ: GRA}.
  
  Definition fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
    forall x_src,
    exists x_tgt,
      (<<PRE: forall arg_src arg_tgt,
          (fsp_src.(precond) x_src arg_src arg_tgt) ==∗ (fsp_tgt.(precond) x_tgt arg_src arg_tgt)>>) ∧
      (<<POST: forall ret_src ret_tgt,
          (fsp_tgt.(postcond) x_tgt ret_src ret_tgt) ==∗ (fsp_src.(postcond) x_src ret_src ret_tgt)>>)
  .

  Global Program Instance fspec_weaker_PreOrder : PreOrder fspec_weaker.
  Next Obligation.
  Proof using.
    ii. exists x_src. esplits; ii.
    { iStartProof. iIntros "H". iApply "H". }
    { iStartProof. iIntros "H". iApply "H". }
  Qed.
  Next Obligation.
  Proof using.
    ii. hexploit (H x_src). i. des.
    hexploit (H0 x_tgt). i. des. esplits; ii.
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply PRE0.
      iApply bupd_idemp. iApply PRE. iApply "H". }
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply POST.
      iApply bupd_idemp. iApply POST0. iApply "H". }
  Qed.

  Variant fn_has_spec (spc : string -> option fspec) (fn : string) (fsp : fspec) : Prop :=
  | fn_has_spec_intro fsp1
      (FIND : spc fn = Some fsp1)
      (WEAK : fspec_weaker fsp fsp1).
  Hint Constructors fn_has_spec : core.

  Lemma fn_has_spec_weaker (spc : string -> option fspec) (fn : string) (fsp0 fsp1 : fspec)
      (SPEC : fn_has_spec spc fn fsp1)
      (WEAK : fspec_weaker fsp0 fsp1) :
    fn_has_spec spc fn fsp0.
  Proof using. inv SPEC. econs; eauto. etrans; eauto. Qed.

  Definition spc_sub (spc0 spc1 : string -> option fspec) : Prop :=
    ∀ fn fsp (FIND : spc0 fn = Some fsp), spc1 fn = Some fsp.

  Definition spc_incl (spcl : alist string fspec) (gspc : string -> option fspec) : Prop :=
    List.NoDup (List.map fst spcl) ∧ spc_sub (to_spc spcl) gspc.

  Global Program Instance spc_sub_PreOrder : PreOrder spc_sub.
  Next Obligation.
  Proof using. ii. ss. Qed.
  Next Obligation.
  Proof using. ii. eapply H0, H, FIND. Qed.

  Lemma incl_to_spc spc0 spc1 (INCL : List.incl spc0 spc1)
        (NODUP : List.NoDup (List.map fst spc1)) :
      spc_sub (to_spc spc0) (to_spc spc1).
  Proof using.
    unfold to_spc. ii.
    eapply alist_find_some in FIND. eapply INCL in FIND.
    eapply alist_find_some_iff in FIND; et.
  Qed.

  Lemma to_spc_context_sub spcu spck spcall
      (INCL : List.incl spck spcall)
      (NODUP : List.NoDup (spcu ++ (List.map fst spcall))) :
    spc_sub (to_spc_context spcu spck) (to_closed_spc spcall).
  Proof using.
    unfold to_spc_context, to_spc, to_closed_spc. ii.
    rewrite alist_find_app_o in FIND. 
    destruct (alist_find fn (List.map (fun fn => (fn, fspec_trivial)) spcu)) eqn:EQ; clarify.
    { eapply alist_find_some in EQ. eapply in_map_iff in EQ. des. clarify.
      des_ifs. exfalso. eapply alist_find_some in Heq.
      eapply NoDup_app_disjoint in NODUP; et.
      eapply in_map with (f:=fst) in Heq. ss. }
    { eapply alist_find_some in FIND. eapply INCL in FIND.
      eapply alist_find_some_iff in FIND; et.
      rewrite FIND; et. eapply nodup_app_r; et. }
    Unshelve. exact string_Dec.
  Qed.

  Definition spc_weaker (spc0 spc1 : string -> option fspec) : Prop :=
    ∀ fn fsp0 (FINDTGT : spc0 fn = Some fsp0),
      ∃ fsp1, (<<FINDSRC : spc1 fn = Some fsp1>>) ∧ (<<WEAKER : fspec_weaker fsp0 fsp1>>).

  Global Program Instance spc_weaker_PreOrder : PreOrder spc_weaker.
  Next Obligation. ii. esplits; eauto. refl. Qed.
  Next Obligation.
    ii. r in H. r in H0. exploit H; et. intro T; des.
    exploit H0; et. intro U; des. esplits; eauto. etrans; et.
  Qed.

  Lemma spc_sub_weaker : spc_sub <2= spc_weaker.
  Proof using.
    ii. eapply PR in FINDTGT. esplits; et. refl.
  Qed.

  Lemma incl_spc_sub :
    ∀ spc0 spc1 (NODUP : List.NoDup (List.map fst spc1)) (INCL : List.incl spc0 spc1),
      spc_sub (to_spc spc0) (to_spc spc1).
  Proof using.
    unfold to_spc.
    ii. eapply alist_find_some in FIND.
    destruct (alist_find fn spc1) eqn:T.
    { eapply alist_find_some in T.
      eapply INCL in FIND.
      destruct (classic (fsp = f)).
      { subst. esplits; et. }
      exfalso.
      eapply NoDup_inj_aux in NODUP; revgoals.
      { eapply T. }
      { eapply FIND. }
      { ii; clarify. }
      ss.
    }
    eapply alist_find_none in T; et. exfalso. et.
  Qed.

  Lemma incl_weaker :
    ∀ spc0 spc1 (NODUP : List.NoDup (List.map fst spc1)) (INCL : List.incl spc0 spc1),
      spc_weaker (to_spc spc0) (to_spc spc1).
  Proof using. i. eapply spc_sub_weaker. eapply incl_spc_sub; et. Qed.

  Lemma app_sub : ∀ spc0 spc1, spc_sub (to_spc spc0) (to_spc (spc0 ++ spc1)).
  Proof using. unfold to_spc. ii. eapply alist_find_app in FIND. esplits; eauto. Qed.

  Lemma app_weaker : ∀ spc0 spc1, spc_weaker (to_spc spc0) (to_spc (spc0 ++ spc1)).
  Proof using. i. eapply spc_sub_weaker. eapply app_sub. Qed.

  Lemma to_closed_spc_weaker spc : spc_sub (to_spc spc) (to_closed_spc spc).
  Proof using. unfold to_closed_spc, to_spc. ii. rewrite FIND. auto. Qed.

  Lemma incl_to_closed_spc spc0 spc1 (INCL : List.incl spc0 spc1) (NODUP : List.NoDup (List.map fst spc1)) :
    spc_sub (to_spc spc0) (to_closed_spc spc1).
  Proof using.
    unfold to_spc, to_closed_spc. ii.
    eapply alist_find_some in FIND. eapply INCL in FIND.
    eapply alist_find_some_iff in FIND; et.
    rewrite FIND. et.
  Unshelve. exact string_Dec.
  Qed.

End HEADER.


Ltac spc_sub_tac :=
  i; eapply incl_to_spc;
  [ autounfold with spc; autorewrite with spc; ii; ss; des; clarify; auto|
    autounfold with spc; autorewrite with spc; (hrepeat do 1 econs); ii; ss; des; ss].

Ltac spc_context_sub_tac :=
  i; eapply to_spc_context_sub;
  [ autounfold with spc; autorewrite with spc; ii; ss; des; clarify; auto|
    autounfold with spc; autorewrite with spc; (hrepeat do 1 econs); ii; ss; des; ss].

Ltac ors_tac := hrepeat do 1 ((try by (ss; left; ss)); right).

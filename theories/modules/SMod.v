Require Import Common.
Require Import HMod.
Require Export SMod2HMod.

Set Implicit Arguments.

Module SMod.
Section SMOD.

  Context `{Σ : GRA}.
  Variable ginv : iProp Σ.
  Variable spc : string -> option fspec.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist string (list string * fspecbody);
    initial_st : alist key Any.t;

    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (state_scopes initial_st) scopes;
    nodup_fns:
      List.NoDup scopes -> List.NoDup (List.map fst initial_st);
  }.

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := [];
    initial_st := [];
  |}.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. econs. Qed.

  Program Definition add ms1 ms2 : t := {|
    scopes := ms1.(scopes) ++ ms2.(scopes);
    fnsems := ms1.(fnsems) ++ ms2.(fnsems);
    initial_st := ms1.(initial_st) ++ ms2.(initial_st);
  |}.
  Next Obligation.
    ii. unfold fnsems_scopes in H. des_ifs.
    rewrite alist_find_app_o in Heq. des_ifs.
    {
      hexploit (ms1.(well_scoped_fns) fn a).
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
    {
      hexploit (ms2.(well_scoped_fns) fn a).
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
  Qed.
  Next Obligation.
    unfold state_scopes. ii. destruct ms1, ms2. ss.
    rewrite map_app in H. apply in_or_app. apply in_app_or in H.
    destruct H; eauto.
  Qed.
  Next Obligation.
    ii. exploit nodup_app_l; eauto. i.
    exploit nodup_app_r; eauto; i.
    apply ms1 in x0. apply ms2 in x1.
    assert (INCL1:= ms1.(well_scoped_init)).
    assert (INCL2:= ms2.(well_scoped_init)).
    revert_until ms2. unfold state_scopes.
    generalize (initial_st ms1) as l1.
    generalize (initial_st ms2) as l2.
    i. revert_until l1. induction l1; ss.
    i. econs; cycle 1.
    {
      eapply IHl1; eauto.
      { eapply NoDup_cons_iff in x0. des. eauto. }
      { ss. ii. eapply INCL1. ss. eauto. }
    }
    ii. rewrite map_app in H0. eapply in_app_or in H0. des.
    { eapply NoDup_cons_iff in x0. des. eauto. }
    eapply NoDup_app_disjoint; eauto.
    { eapply INCL1. s. left. eauto. }
    { eapply INCL2. rewrite - List.map_map. eapply in_map. eauto. }
  Qed.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

  Program Definition to_hmod (ms : t) : HMod.t := {|
    HMod.scopes := ms.(scopes);
    HMod.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp ginv spc ksb.2))) ms.(fnsems);
    HMod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End SMOD.
End SMod.

Infix "☆" := SMod.add (at level 60, right associativity).

Section ADD.
  Context `{Σ : GRA}.
    
  Lemma smod_add_interp_comm
      ginv spc
      (ms0 ms1: SMod.t)
    :
    SMod.to_hmod ginv spc (SMod.add ms0 ms1) = HMod.add (SMod.to_hmod ginv spc ms0) (SMod.to_hmod ginv spc ms1).
  Proof.
    eapply hmod_extensionality; ss; eauto.
    rewrite map_app. ss.
  Qed.

  Lemma add_interp_comm
      ginv spc
      (md0 md1: SMod.t)
    :
    SMod.to_hmod ginv spc (SMod.add md0 md1) = HMod.add (SMod.to_hmod ginv spc md0) (SMod.to_hmod ginv spc md1).
  Proof.
    unfold SMod.to_hmod. unfold "★". s. 
    f_equal. extensionalities.
    eapply smod_add_interp_comm.
  Qed.

  Lemma interp_empty
      ginv spc
    :
    SMod.to_hmod ginv spc SMod.empty = HMod.empty.
  Proof.
    unfold SMod.to_hmod, HMod.empty.
    eapply hmod_extensionality; eauto.
  Qed.

  Lemma addL_interp_comm
      ginv spc
      (mds: list SMod.t)
    :
    SMod.to_hmod ginv spc (SMod.addL mds) = HMod.addL (List.map (SMod.to_hmod ginv spc) mds).
  Proof.
    induction mds; [eapply interp_empty|].
    s. rewrite add_interp_comm.
    f_equal. eauto.
  Qed. 

End ADD.

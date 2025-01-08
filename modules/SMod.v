Require Import Common.

Require Import Skeleton HMod.
Require Export SMod2HMod.

Set Implicit Arguments.

Module SModSem.
Section SMODSEM.

  Context `{Σ : GRA}.
  Variable ginv : invspec.
  Variable stb : gname -> option fspec.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist gname (list string * fspecbody);
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

  Program Definition to_hmod (ms : t) : HModSem.t := {|
    HModSem.scopes := ms.(scopes);
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp ginv stb ksb.2))) ms.(fnsems);
    HModSem.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End SMODSEM.
End SModSem.

Module SMod.
Section SMOD.

  Context `{Σ : GRA}.
  Variable ginv : Sk.t -> invspec.
  Variable stb : Sk.t -> gname -> option fspec.

  Record t : Type := mk {
    modsem : Sk.t -> SModSem.t;
    sk : Sk.t;
  }.

  Definition empty := {|
    modsem := const (SModSem.empty);
    sk := []
  |}.

  Definition add (md0 md1 : t) : t := {|
    modsem := λ sk, SModSem.add (md0.(modsem) sk) (md1.(modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

  Definition to_hmod (md:t) : HMod.t := {|
    HMod.modsem := fun sk => SModSem.to_hmod (ginv sk) (stb sk) (md.(modsem) sk);
    HMod.sk := md.(sk);
 |}.
    
  (* Definition get_stb (mds : list t) : Sk.t -> alist gname (list string * fspec) := *)
  (*   fun sk => List.map (map_snd (map_snd fsb_fspec)) (flat_map (SModSem.fnsems ∘ (flip modsem sk)) mds). *)

  (* Definition get_sk (mds : list t) : Sk.t := *)
  (*   fold_right Sk.add Sk.unit (List.map sk mds). *)

End SMOD.
End SMod.

Infix "☆" := SMod.add (at level 9, right associativity).

Section ADD.
  Context `{Σ : GRA.t}.

  Lemma hmod_ext (ms0 ms1: HModSem.t)
      (SCOPES: ms0.(HModSem.scopes) = ms1.(HModSem.scopes))
      (FNSEMS: ms0.(HModSem.fnsems) = ms1.(HModSem.fnsems))
      (STATES: ms0.(HModSem.initial_st) = ms1.(HModSem.initial_st))
    :
    ms0 = ms1.
  Proof.
    destruct ms0, ms1. ss. subst.
    assert (well_scoped_fns = well_scoped_fns0) by apply proof_irr.
    assert (well_scoped_init = well_scoped_init0) by apply proof_irr.
    assert (nodup_fns = nodup_fns0) by apply proof_irr.
    subst. eauto.
  Qed.
    
  Lemma smodsem_add_interp_comm
      ginv stb
      (ms0 ms1: SModSem.t)
    :
    SModSem.to_hmod ginv stb (SModSem.add ms0 ms1) = HModSem.add (SModSem.to_hmod ginv stb ms0) (SModSem.to_hmod ginv stb ms1).
  Proof.
    eapply hmod_ext; ss; eauto.
    rewrite map_app. ss.
  Qed.

  Lemma add_interp_comm
      ginv stb
      (md0 md1: SMod.t)
    :
    SMod.to_hmod ginv stb (SMod.add md0 md1) = HMod.add (SMod.to_hmod ginv stb md0) (SMod.to_hmod ginv stb md1).
  Proof.
    unfold SMod.to_hmod. unfold "★". s. 
    f_equal. extensionalities.
    eapply smodsem_add_interp_comm.
  Qed. 

  Lemma interp_empty
      ginv stb
    :
    SMod.to_hmod ginv stb SMod.empty = HMod.empty.
  Proof.
    unfold SMod.to_hmod, HMod.empty. ss. 
    f_equal. extensionalities.
    eapply hmod_ext; eauto.
  Qed.

  Lemma addL_interp_comm
      ginv stb
      (mds: list SMod.t)
    :
    SMod.to_hmod ginv stb (SMod.addL mds) = HMod.addL (List.map (SMod.to_hmod ginv stb) mds).
  Proof.
    induction mds; [eapply interp_empty|].
    s. rewrite add_interp_comm.
    f_equal. eauto.
  Qed. 

End ADD.

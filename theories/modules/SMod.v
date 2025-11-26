Require Import Common ConcRA.
Require Import Mod.
Require Export FSpec SModTr Sp.

Definition fnsems_type `{Σ : GRA} :=
  alist (option string) (fnsem_type (option fspec * fbody)).

Module SMod. Section SMOD.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist (option string) fnsem;
    initial_st : alist key Any.t;

    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (state_scopes initial_st) scopes;
    nodup_init:
      List.NoDup scopes -> List.NoDup (List.map fst initial_st);
  }.

  Definition cancellable (ms : t) : Prop :=
    ∀ fno img msk scp fspo bd
      (FIND: alist_find fno (fnsems ms) = Some (img, msk, scp, (fspo, bd))),
      img = true ∧ is_some fspo ∧ (fno = None → fspo = Some (fspec_trivial)).

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
    ii. unfold fnsems_scopes in H0. des_ifs.
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
    rewrite map_app in H0. apply in_or_app. apply in_app_or in H0.
    destruct H0; eauto.
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
    ii. rewrite map_app in H1. eapply in_app_or in H1. des.
    { eapply NoDup_cons_iff in x0. des. eauto. }
    eapply NoDup_app_disjoint; eauto.
    { eapply INCL1. s. left. eauto. }
    { eapply INCL2. rewrite - List.map_map. eapply in_map. eauto. }
  Qed.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

  Program Definition to_mod (sp : sp_type) (ms : t) : Mod.t := {|
    Mod.scopes := ms.(scopes);
    Mod.fnsems := List.map (map_snd (SModTr.trans_ktree sp)) ms.(fnsems);
    Mod.initial_st := ms.(initial_st);
    |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in *.
    rewrite alist_find_map in H0. specialize (well_scoped_fns0 fn a).
    destruct (alist_find fn fnsems0) eqn: E; ss.
    destruct f. destruct p. destruct p0. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

  Program Definition cancel (ms : t) : t := {|
    scopes := ms.(scopes);
    fnsems := List.map (map_snd (map_snd (map_fst (const None)))) ms.(fnsems);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in *.
    rewrite !alist_find_map in H0. specialize (well_scoped_fns0 fn a).
    destruct (alist_find fn fnsems0) eqn: E; try rewrite E in H0; ss.
    destruct f. destruct p. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End SMOD.
End SMod.

Infix "☆" := SMod.add (at level 60, right associativity).

Section ADD.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Lemma smod_add_interp_comm
      sp
      (ms0 ms1: SMod.t)
    :
    SMod.to_mod sp (SMod.add ms0 ms1) = Mod.add (SMod.to_mod sp ms0) (SMod.to_mod sp ms1).
  Proof using.
    eapply mod_extensionality; ss; eauto.
    rewrite map_app. ss.
  Qed.

  Lemma add_interp_comm
      sp
      (md0 md1: SMod.t)
    :
    SMod.to_mod sp (SMod.add md0 md1) = Mod.add (SMod.to_mod sp md0) (SMod.to_mod sp md1).
  Proof using.
    unfold SMod.to_mod. unfold "★". s.
    f_equal. extensionalities.
    eapply smod_add_interp_comm.
  Qed.

  Lemma interp_empty
      sp
    :
    SMod.to_mod sp SMod.empty = Mod.empty.
  Proof using.
    unfold SMod.to_mod, Mod.empty.
    eapply mod_extensionality; eauto.
  Qed.

  Lemma addL_interp_comm
      sp
      (mds: list SMod.t)
    :
    SMod.to_mod sp (SMod.addL mds) = Mod.addL (List.map (SMod.to_mod sp) mds).
  Proof using.
    induction mds; [eapply interp_empty|].
    s. rewrite add_interp_comm.
    f_equal. eauto.
  Qed.

End ADD.

Section Aux.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition sp_from (md : SMod.t) : sp_type :=
    to_sp (List.map (map_snd (fst ∘ snd)) md.(SMod.fnsems)).
  
  (* Definition has_param (md : SMod.t) fno img msk scp := *)
  (*   ∃ sbd, alist_find fno (SMod.fnsems md) = Some (img, msk, scp, sbd). *)

  (* Definition has_trivial_spec (md : SMod.t) (fn : string) : Prop := *)
  (*   ∃ fno msk scp, has_param md fno false msk scp ∧ msk fn. *)

  (* Definition valid_sp (md: SMod.t) (sp: sp_type) : Prop := *)
  (*   sp_imply' (sp_from md) sp ∧ *)
  (*   (∀ fn (NS: has_trivial_spec md fn), fspec_imply (fspec_flat (sp fn)) fspec_trivial) *)

  (* Definition real_smod (md : SMod.t) : Prop := *)
  (*   ∀ fno img msk scp, has_param md fno img msk scp → img = false. *)

  (* Lemma real_smod_ignores_sp md sp *)
  (*   (REAL: real_smod md) *)
  (*   (WF: Mod.wf (SMod.to_mod sp_none md)) *)
  (*   : *)
  (*   SMod.to_mod sp md = SMod.to_mod sp_none md. *)
  (* Proof. *)
  (*   eapply mod_extensionality; s; et. unfold SModTr.trans_ktree. *)
  (*   eapply map_ext_Forall. eapply List.Forall_forall. i. *)
  (*   destruct x as [fno [[[img msk] scp] [fsp bd]]]. s. repeat f_equal. *)
  (*   destruct WF; ss. rewrite map_map fst_map_snd in wf_fns. *)
  (*   eapply alist_find_some_iff in H0; et. *)
  (*   exploit REAL; [r; et|]. *)
  (*   i; subst; et. *)
  (* Qed. *)
End Aux.

(* Global Hint Unfold has_param : core. *)
(* Global Hint Unfold has_trivial_spec : core. *)

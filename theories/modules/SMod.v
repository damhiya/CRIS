Require Import Common ConcRA.
Require Import Mod.
Require Export FSpec SModTr Sp.

Module SMod. Section Smod.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* SMods are basic units of composition in CRIS. *)
  (* The image of the maps are lifted by option to make the module append operation total. *)
  Record t : Type := mk {
    scopes : list string;
    fnsems : gmap (option string) (option (emask * (option fspec * fbody)));
    initial_st : gmap key (option Any.t);

    well_scoped_fns :
      map_Forall
        (λ _ '((msk, _) : emask * _),
          (∀ (k : key) (v : Any.t), msk _ (subevent _ (SPut k v)) = true → k.1 ∈ scopes) ∧
          (∀ (k : key), msk _ (subevent _ (SGet k)) = true → k.1 ∈ scopes))
        (omap id fnsems);
      (* forall fn, incl (fnsems_scopes fn fnsems) scopes; *)
    well_scoped_init :
      (elements (dom initial_st)).*1 ⊆ scopes;
    nodup_init :
      NoDup scopes → map_Forall (const is_Some) initial_st;
  }.

  Definition cancellable (ms : t) (sp: specmap) : Prop :=
    ∀ fno msk fspo bd
      (FIND: (fnsems ms) !! fno = Some (Some (msk, (fspo, bd)))),
      (img_msk msk) ∧ (speckey_concE ∈ dom sp).

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.

  Program Definition add ms1 ms2 : t := {|
    scopes := (scopes ms1) ++ (scopes ms2);
    fnsems := union_with (λ _ _, Some None) (fnsems ms1) (fnsems ms2);
    initial_st := union_with (λ _ _, Some None) (initial_st ms1) (initial_st ms2);
  |}.
  Next Obligation.
    intros ms1 ms2 fn [msk p].
    rewrite lookup_omap lookup_union_with.
    destruct ((fnsems ms1) !! fn) eqn: Heq1; destruct ((fnsems ms2) !! fn) eqn: Heq2; ss; intros ->.
    { hexploit (ms1.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq1 //. }
      intros [? ?]; split; ii; rewrite elem_of_app; left; eauto.
    }
    { hexploit (ms2.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq2 //. }  
      intros [? ?]; split; ii; rewrite elem_of_app; right; eauto.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 fn; rewrite elem_of_list_fmap; intros [[scp ?] [-> Hin]]; ss.
    rewrite elem_of_elements elem_of_dom lookup_union_with in Hin.
    destruct (initial_st ms1 !! _) eqn: Heq1; eapply elem_of_app; [left|right].
    { apply (ms1.(well_scoped_init)); rewrite elem_of_list_fmap; eexists (scp, _); split; ss.
      rewrite elem_of_elements elem_of_dom //.
    }
    destruct (initial_st ms2 !! _) eqn: Heq2; [|inv Hin].
    { apply (ms2.(well_scoped_init)); rewrite elem_of_list_fmap; eexists (scp, _); split; ss.
      rewrite elem_of_elements elem_of_dom //.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 [Hnodup1%ms1 [Hdisj Hnodup2%ms2]]%NoDup_app.
    rewrite map_Forall_lookup; intros [scp nm] x; rewrite lookup_union_with.
    destruct (_ ms1 !! _) eqn : Hms1.
    { destruct (_ ms2 !! _) eqn : Hms2; ss; cycle 1.
      { i; clarify. rewrite map_Forall_lookup in Hnodup1; eapply Hnodup1 in Hms1; destruct x; ss. }
      exfalso; hexploit (Hdisj scp).
      { apply (well_scoped_init ms1).
        apply elem_of_list_fmap; exists (scp, nm); split; ss.
        rewrite elem_of_elements elem_of_dom Hms1 //.
      }
      { intros Hf; apply Hf.
        apply (well_scoped_init ms2).
        apply elem_of_list_fmap; exists (scp, nm); split; ss.
        rewrite elem_of_elements elem_of_dom Hms2 //.
      }
    }
    destruct (_ ms2 !! _) eqn : Hms2; ss; cycle 1.
    { i; clarify. rewrite map_Forall_lookup in Hnodup2; eapply Hnodup2 in Hms2; destruct x; ss. }
  Qed.

  (* TODO *)
  Definition addL (ms : list t) : t := foldr add empty ms.

  Program Definition to_mod (sp : specmap) (ms : t) : Mod.t := {|
    Mod.scopes := ms.(scopes);
    Mod.fnsems := fmap (option_map (map_snd (SModTr.trans_fnsem sp))) ms.(fnsems);
    Mod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    intros sp ms fno [msk p].
    rewrite lookup_omap lookup_fmap. destruct (fnsems ms !! fno) eqn: Heq; intros FIND; ss.
    destruct o as [[msk0 [fspo p0]]|]; ss. inv FIND.
    hexploit (well_scoped_fns ms). i. unfold map_Forall in H0. specialize (H0 fno (msk, (fspo, p0))).
    eapply H0. rewrite lookup_omap Heq; refl.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H2 i). eapply H2; eauto.
  Qed.
  
  Program Definition cancel (ms : t) : t := {|
    scopes := ms.(scopes);
    fnsems := (.≫= (λ '(msk, bd), Some (msk, (None, bd.2)))) <$> ms.(fnsems);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    intros ms fn [? ?] Hin; hexploit (ms.(well_scoped_fns)); eauto.
    rewrite lookup_omap_id_Some lookup_fmap in Hin;
      destruct (_ !! _) as [[[p1 [p2 p3]]|]|] eqn : Hin';
      ss; clarify.
    intros Hwf; specialize (Hwf fn (e, (p2, p3))); ss; apply Hwf.
    rewrite lookup_omap_id_Some; ss.
  Qed.
  Next Obligation. intros ms; ii; destruct ms; ss; eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H2 i). eapply H2; eauto.
  Qed.
End Smod. End SMod.

Infix "☆" := SMod.add (at level 60, right associativity).

Section ADD.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* Lemma smod_add_interp_comm sp (ms0 ms1 : SMod.t) :
    SMod.to_mod sp (SMod.add ms0 ms1) = Mod.add (SMod.to_mod sp ms0) (SMod.to_mod sp ms1).
  Proof using.
    eapply mod_extensionality; ss; eauto. rewrite map_app. ss.
  Qed. *)

  (* Lemma add_interp_comm
      sp
      (md0 md1: SMod.t)
    :
    SMod.to_mod sp (SMod.add md0 md1) = Mod.add (SMod.to_mod sp md0) (SMod.to_mod sp md1).
  Proof using.
    unfold SMod.to_mod. unfold "★". s.
    f_equal. extensionalities.
    eapply smod_add_interp_comm.
  Qed. *)

  (* Lemma interp_empty
      sp
    :
    SMod.to_mod sp SMod.empty = Mod.empty.
  Proof using.
    unfold SMod.to_mod, Mod.empty.
    eapply mod_extensionality; eauto.
  Qed. *)

  (* Lemma addL_interp_comm
      sp
      (mds: list SMod.t)
    :
    SMod.to_mod sp (SMod.addL mds) = Mod.addL (List.map (SMod.to_mod sp) mds).
  Proof using.
    induction mds; [eapply interp_empty|].
    s. rewrite add_interp_comm.
    f_equal. eauto.
  Qed. *)
End ADD.

Section Aux.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* Definition sp_from (md : SMod.t) : sp_type :=
    to_sp (List.map (map_snd (fst ∘ snd)) md.(SMod.fnsems)). *)
  
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

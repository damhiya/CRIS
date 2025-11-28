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
    (* nodup_init:
      List.NoDup scopes -> List.NoDup (List.map fst initial_st); *)
  }.

  (* Definition cancellable (ms : t) : Prop :=
    ∀ fno img msk scp fspo bd
      (FIND: alist_find fno (fnsems ms) = Some (img, msk, scp, (fspo, bd))),
      img = true ∧ is_some fspo ∧ (fno = None → fspo = Some (fspec_trivial)). *)

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.
  (* Next Obligation. econs. Qed. *)

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

  (* TODO *)
  (* Definition addL (ms : list t) : t := foldr add empty ms. *)

  (* Program Definition to_mod (sp : sp_type) (ms : t) : Mod.t := {|
    scopes := ms.(scopes);
    (* fnsems := List.map (map_snd (SModTr.trans_fnsem sp)) ms.(fnsems); *)
    fnsems := List.map (map_snd (SModTr.trans_fnsem sp)) ms.(fnsems);
    initial_st := ms.(initial_st);
  |}. *)
  (* Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in *.
    rewrite alist_find_map in H0. specialize (well_scoped_fns0 fn a).
    destruct (alist_find fn fnsems0) eqn: E; ss.
    destruct f. destruct p. destruct p0. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed. *)
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

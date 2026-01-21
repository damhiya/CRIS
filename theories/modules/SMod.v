Require Import Common ConcRA.
Require Import Mod.
Require Export FSpec SModTr Sp.

Module SMod. Section Smod.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* SMods are basic units of composition in CRIS. *)
  (* The image of the maps are lifted by option to make the module append operation total. *)
  Record t : Type := mk {
    scopes : gmultiset string;
    fnsems : gmap (option string) (option (emask * (option fspec * fbody)));
    initial_st : gmap key (option Any.t);

    well_scoped_fns :
      map_Forall
        (λ _ '((msk, _) : emask * _),
          (∀ (k : key) (v : Any.t), msk _ (subevent _ (SPut k v)) = true → k.1 ∈ scopes) ∧
          (∀ (k : key), msk _ (subevent _ (SGet k)) = true → k.1 ∈ scopes))
        (omap id fnsems);
    well_scoped_init :
      (set_map fst (dom initial_st)) ⊆ dom scopes;
    nodup_init :
      (∀ x, multiplicity x scopes ≤ 1) → map_Forall (const is_Some) initial_st;
  }.

  Definition lift_fn (fno: option string) : speckey :=
    match fno with
    | Some fn => speckey_fn fn
    | None => speckey_entry
    end.

  Definition sp_from (md : t) : specmap :=
    kmap lift_fn (omap id (fst ∘ snd <$> omap id md.(fnsems))).
  
  Definition conc_sp_from (md : t) : specmap :=
    <[speckey_concE := fspec_trivial]> (sp_from md).

  Definition cancellable (ms : t) : Prop :=
    ∀ fno msk fspo bd
      (FIND: (fnsems ms) !! fno = Some (Some (msk, (fspo, bd)))),
      (img_msk msk) ∧ (call_msk msk) ∧ (is_Some fspo).

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := ∅;
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Solve All Obligations with done.

  Program Definition add ms1 ms2 : t := {|
    scopes := (scopes ms1) ⊎ (scopes ms2);
    fnsems := union_with (λ _ _, Some None) (fnsems ms1) (fnsems ms2);
    initial_st := union_with (λ _ _, Some None) (initial_st ms1) (initial_st ms2);
  |}.
  Next Obligation.
    intros ms1 ms2 fn [msk p].
    rewrite lookup_omap lookup_union_with.
    destruct ((fnsems ms1) !! fn) eqn: Heq1; destruct ((fnsems ms2) !! fn) eqn: Heq2; ss; intros ->.
    { hexploit (ms1.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq1 //. }
      intros [? ?]; split; ii; apply gmultiset_elem_of_disj_union; left; eauto.
    }
    { hexploit (ms2.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq2 //. }  
      intros [? ?]; split; ii; apply gmultiset_elem_of_disj_union; right; eauto.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 fn [[scp ?] [-> [? Hin]%elem_of_dom]]%elem_of_map; ss.
    apply lookup_union_with_Some in Hin; des; ss;
      apply gmultiset_elem_of_dom, gmultiset_elem_of_disj_union; [left|right|left].
    { hexploit (ms1.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
    { hexploit (ms2.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
    { hexploit (ms1.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 H1; rewrite map_Forall_lookup; intros [scp key] v.
    rewrite lookup_union_with_Some; intros [Hl | [Hl | [? [? [Hl1 Hl2]]]]]; des.
    { apply (nodup_init ms1); eauto.
      intros x; hexploit (H1 x); rewrite multiplicity_disj_union; lia.
    }
    { apply (nodup_init ms2); eauto.
      intros x; hexploit (H1 x); rewrite multiplicity_disj_union; lia.
    }
    hexploit (well_scoped_init ms1) => /(_ scp); rewrite elem_of_map.
    intros Hin1; hexploit Hin1; [exists (scp, key); split; ss; apply elem_of_dom; eauto|].
    rewrite gmultiset_elem_of_dom elem_of_multiplicity.
    hexploit (well_scoped_init ms2) => /(_ scp); rewrite elem_of_map.
    intros Hin2; hexploit Hin2; [exists (scp, key); split; ss; apply elem_of_dom; eauto|].
    rewrite gmultiset_elem_of_dom elem_of_multiplicity.
    hexploit (H1 scp); rewrite multiplicity_disj_union; lia.
  Qed.

  (* TODO *)
  (* Definition addL (ms : list t) : t := foldr add empty ms. *)
  Program Definition to_mod (sp : specmap) (ms : t) : Mod.t := {|
    Mod.scopes := ms.(scopes);
    Mod.fnsems := (λ (x : option _), (map_snd (SModTr.trans_fnsem sp)) <$> x) <$> ms.(fnsems);
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

  #[global]
  Instance smod_lift_fn_inj : Inj (=) (=) SMod.lift_fn.
  Proof. ii. rewrite /SMod.lift_fn in H0. des_ifs. Qed.

  Lemma lookup_sp_from md fn kboo
    (FIND: md.(SMod.fnsems) !! Some fn = kboo) :
    (SMod.sp_from md) !! (speckey_fn fn) =
      match kboo with
      | Some (Some (_, (Some fsp, _))) => Some fsp
      | _ => None
      end.
  Proof using.
    rewrite /SMod.sp_from.
    destruct (match kboo with
              | Some (Some (_, (Some fsp, _))) => Some fsp
              | _ => None
              end) eqn: E; cycle 1.
    { set (l:=omap _ _).
      eapply (lookup_kmap_None SMod.lift_fn l (speckey_fn fn)).
      i. rewrite /SMod.lift_fn in H0. destruct i; ss. inv H0. subst l.
      rewrite lookup_omap lookup_fmap lookup_omap. des_ifs. }
    { set (l:=omap _ _).
      eapply (lookup_kmap_Some SMod.lift_fn l (speckey_fn fn)).
      exists (Some fn). split; ss. subst l.
      rewrite lookup_omap lookup_fmap lookup_omap. des_ifs. }
  Qed.

  (* Definition lift_fn (fno: option string) : speckey := *)
  (*   match fno with *)
  (*   | Some fn => speckey_fn fn *)
  (*   | None => speckey_entry *)
  (*   end. *)
  
  (* Definition sp_from (md : SMod.t) : specmap := *)
  (*   list_to_map (map (map_fst lift_fn) (map_to_list (omap id (fst ∘ snd <$> omap id md.(SMod.fnsems))))). *)

  (* Definition sp_from_conc (md : SMod.t) : specmap := *)
  (*   <[speckey_concE := fspec_trivial]> (sp_from md). *)
  
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

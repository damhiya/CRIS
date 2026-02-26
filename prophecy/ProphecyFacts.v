Require Export CRIS CallFilter ProphecyIAproof HelpingFacts.
Require Export SchI MemI MemA MemIAproof.
From stdpp Require Import base list.

Lemma CFilter_real_mod `{Σ : GRA} (md : Mod.t) (msk : gset string) :
  real_mod md → real_mod (CFilter.filter msk md).
Proof.
  rewrite /real_mod !map_Forall_lookup /CFilter.filter {2}/Mod.fnsems.
  intros Hix i x; rewrite lookup_fmap; specialize (Hix i); destruct lookup as [[[? ?]|]|];
    i; clarify; destruct x; ss; clarify.
  { rewrite /CFilter.msk_filter /=; eapply (Hix (Some (e, f))); ss. }
Qed.

Section prophecy.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !prophGS}.

  (* Lemmas about names *)
  Local Definition maxlen (s : list string) : nat :=
    list_max (String.length <$> s).

  Local Fixpoint mname_long (n : nat) : string :=
    match n with
    | 0 => ""
    | S n' => "h" +:+ mname_long n'
    end.

  Local Lemma mname_long_length n : String.length (mname_long n) = n.
  Proof. induction n; ss. rewrite IHn. et. Qed.

  Local Lemma elem_of_maxlen (fn : string) (s : list string) :
    fn ∈ s → String.length fn ≤ maxlen s.
  Proof. i; eapply max_list_elem_of_le, elem_of_list_fmap; esplits; eauto. Qed.

  Local Lemma maxlen_union s1 s2 : maxlen (s1 ++ s2) = maxlen s1 `max` maxlen s2.
  Proof. rewrite /maxlen fmap_app list_max_app //. Qed.

  Lemma prophecy_refines (mds mdt ctx : Mod.t) (mdm : string → Mod.t) (Pm Ps : iProp Σ) :
    (∀ mn,
      ctx_refines
        (mdm mn ★ ProphecyI.t mn, Pm)
        (CFilter.filter (ProphecyName.exports mn) mdt ★ ProphecyI.t mn, emp%I)) →
    (∀ mn,
      ctx_refines
        (mds, Ps)
        (mdm mn ★ ProphecyA.t mn ∅, emp%I)) →
    (∀ mn, real_mod (mdm mn)) →
    real_mod ctx →
    refines (mds ★ ctx, Pm ∗ ProphecyA.initial_cond ∗ Ps)%I (mdt ★ ctx, emp%I).
  Proof.
    intros Hproph Hreal ? ?.
    set (mn := maxlen
      (elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems (mdt ★ ctx))) : gset string) ++
       elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems (ctx ★ mds))) : gset string) ++
      Mod.scopes mdt ++ Mod.scopes ctx ++ Mod.scopes mds)).
    etrans; cycle 1.
    { eapply ctxr_refines,
        CFilter.intro_filter with (fns := ProphecyName.exports (mname_long (S mn))). }
    etrans; cycle 1.
    { eapply CFilter.intro_module with (mc := ProphecyI.t (mname_long (S mn))).
      { econs; [mod_tac|prove_nodup]. }
      { set_solver. }
      { intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1;
        set_unfold; des; subst mn; subst; ss;
          rewrite ?mname_long_length ?maxlen_union in Hi1; lia.
      }
      { set_solver+. }
      { set_solver+. }
    }
    rewrite CFilter.filter_app.
    etrans; cycle 1.
    { eapply ctxr_refines.
      ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply (Hproph (mname_long (S mn))).
    }
    etrans; cycle 1.
    { rewrite comm -assoc (Mod.add_comm (ProphecyI.t _)) assoc.
      eapply ProphIA.adequacy_refines; eauto.
      eapply real_mod_add; eauto using CFilter_real_mod.
    }
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop. ctxr_rotate. eapply Hreal. }
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_drop. eapply CFilter.intro_filter. }
    erewrite <-!CFilter.filter_app. ctxr_norm.
    etrans; cycle 1.
    { eapply CFilter.elim_filter.
      intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1;
        set_unfold; des; subst mn; subst; ss;
          rewrite ?mname_long_length ?maxlen_union in Hi1; lia.
    }

    rewrite Mod.add_comm.
    eapply ctxr_refines, ctxr_cond_strengthen; iIntros "[$ [$ $]]".
  Qed.

  Lemma helping_prophecy_refines
      `{!memGS}
      (mds mdt ctx : Mod.t) (mdp mdm : string → Mod.t) csl genv sp_mem sp_help
      {jobID retID} (jobs : jobID → itree crisE retID) :
    let fns mn := ProphecyName.exports mn ∪ Helping.exports mn in
    (∀ mn,
      ctx_refines
        (mdp mn ★ ProphecyI.t mn, emp%I) (CFilter.filter (fns mn) mdt ★ ProphecyI.t mn, emp%I)) →
    (∀ mn,
      ctx_refines
        (mdm mn ★ HelpingOn.t mn jobs sp_help ★ MemA.t sp_mem ★ ProphecyA.t mn ∅, emp%I)
        (mdp mn ★ HelpingDummy.t mn ★ MemA.t sp_mem ★ ProphecyA.t mn ∅, emp%I)) →
    (∀ mn, ctx_refines (mds, emp%I) (mdm mn ★ HelpingOff.t mn jobs sp_help, emp%I)) →
    real_mod ctx →
    (∀ mn, real_mod (mdp mn)) →
    refines
      (mds ★ MemA.t sp_mem ★ SchI.t ★ ctx, MemA.init_cond csl genv ∗ ProphecyA.initial_cond)%I
      (mdt ★ MemI.t csl genv ★ SchI.t ★ ctx, emp%I).
  Proof.
    intros fns Hproph_insert Hmain Herase Hctx_real Hmdp_real.
    assert (Hadd_wf : ∀ mn, Mod.wf (ProphecyI.t mn ★ HelpingDummy.t mn)).
    { i; econs; [mod_tac|prove_nodup]. }
    set (l := maxlen
      (elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems (SchI.t ★ ctx ★ MemA.t sp_mem ★ mds))) : gset string) ++
       elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems (mdt ★ MemI.t csl genv ★ SchI.t ★ ctx))) : gset string) ++
       Mod.scopes (mdt ★ MemI.t csl genv ★ SchI.t ★ ctx) ++
      Mod.scopes mdt ++ Mod.scopes ctx ++ Mod.scopes mds)).
    set (mn := mname_long (S l)).
    assert (mn ∉ Mod.scopes (mdt ★ MemI.t csl genv ★ SchI.t ★ ctx)) as Hmn.
    { intros Hcontra%elem_of_maxlen; subst mn l.
      rewrite !mname_long_length ?maxlen_union in Hcontra; lia.
    }
    etrans; cycle 1.
    { eapply ctxr_refines, CFilter.intro_filter with (fns := fns mn). }
    etrans; cycle 1.
    { eapply CFilter.intro_module with (mc := ProphecyI.t mn ★ HelpingDummy.t mn).
      { apply Hadd_wf. }
      { revert Hmn; generalize mn; clear dependent mn. intros ? ?. set_solver+Hmn. }
      { intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
        subst fns; set_unfold in Hi2; des; subst mn l; subst;
          rewrite string_length_app ?mname_long_length ?maxlen_union in Hi1; lia.
      }
      { clear. generalize mn; clear dependent mn l; subst fns; intros ?.
        rewrite Mod.dom_fnsems_add set_omap_union; set_solver. }
      { clear. generalize mn; clear dependent mn l; intros ?.
        rewrite Mod.dom_fnsems_add. set_solver+. }
    }
    do 2 rewrite CFilter.filter_app.
    etrans; cycle 1.
    { eapply ctxr_refines.
      ctxr_rotate. do 2 ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply (Hproph_insert).
    }
    etrans; cycle 1.
    { rewrite ?assoc.
      eapply ProphIA.adequacy_refines; eauto.
      rewrite -!assoc CFilter.filter_app.
      repeat eapply real_mod_add; eauto using CFilter_real_mod.
      { apply CFilter_real_mod. rewrite /real_mod.
        clear dependent mn l.
        let real_tac :=
          (split; ss; intros ??; destruct excluded_middle_informative; ss) in
        mod_tac real_tac.
       }
      { apply CFilter_real_mod. rewrite /real_mod.
        clear.
        let real_tac :=
          (split; ss; intros ??; destruct excluded_middle_informative; ss) in
        mod_tac real_tac.
      }
      { rewrite /real_mod.
        clear. generalize mn; clear dependent mn l; intros ?.
        let real_tac :=
          (split; ss; intros ??; destruct excluded_middle_informative; ss) in
        mod_tac real_tac.
      }
    }
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_rotate. do 4 ctxr_drop.
      clear. generalize mn; clear dependent mn l; intros ?.
      eapply main_adequacy, MemIA.sim; set_solver.
    }
    etrans; cycle 1.
    { eapply ctxr_refines.
      ctxr_drop. ctxr_swap. do 2 ctxr_rotate. ctxr_swap. do 2 ctxr_rotate.
      eapply Hmain.
    }
    rewrite CFilter.filter_app.
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop. ctxr_drop. ctxr_swap. ctxr_drop.
      ctxr_swap. ctxr_drop.
      eapply helping_onoff_correct; eauto.
      clear. generalize mn; clear dependent mn l; intros ?.
      set_solver.
    }
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_drop. do 2 (ctxr_swap; ctxr_drop). rewrite /mod_src.
      do 2 ctxr_rotate. ctxr_drop. eapply Herase.
    }
    etrans; cycle 1.
    { eapply ctxr_refines. do 2 ctxr_drop. ctxr_rotate. do 2 ctxr_drop. eapply elim_module. }
    etrans; cycle 1.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop. ctxr_swap; ctxr_drop. rewrite left_id.
      erewrite <-!CFilter.filter_app. refl.
    }
    etrans; cycle 1.
    { eapply ctxr_refines. do 2 ctxr_rotate. ctxr_drop. eapply CFilter.intro_filter. }
    erewrite <-!CFilter.filter_app.
    etrans; cycle 1.
    { eapply CFilter.elim_filter.
      rewrite -assoc.
      intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
      subst fns; set_unfold in Hi2; des; subst mn l; subst;
        rewrite string_length_app ?mname_long_length ?maxlen_union in Hi1; lia.
    }
    eapply ctxr_refines.
    ctxr_norm. do 3 ctxr_rotate. ctxr_drop. do 2 ctxr_rotate. ctxr_drop. refl.
  Qed.
End prophecy.

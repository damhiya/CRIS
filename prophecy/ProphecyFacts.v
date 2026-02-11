Require Export CRIS CallFilter ProphecyIAproof.

Lemma CFilter_real_mod `{Σ : GRA} (md : Mod.t) (msk : gset string) :
  real_mod md → real_mod (CFilter.filter msk md).
Proof.
  rewrite /real_mod !map_Forall_lookup /CFilter.filter {2}/Mod.fnsems.
  intros Hix i x; rewrite lookup_fmap; specialize (Hix i); destruct lookup as [[[? ?]|]|];
    i; clarify; destruct x; ss; clarify.
  { rewrite /CFilter.msk_filter /=; eapply (Hix (Some (e, f))); ss. }
Qed.

Section prophecy.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !prophGS}.

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
      (elements (set_omap id (dom (Mod.fnsems (mdt ★ ctx))) : gset string) ++
       (* elements (set_omap id (dom (Mod.fnsems ctx)) : gset string) ++ *)
       elements (set_omap id (dom (Mod.fnsems (ctx ★ mds))) : gset string) ++
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
    { rewrite Mod.add_comm mod_add_assoc (Mod.add_comm (ProphecyI.t _)) -mod_add_assoc.
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
End prophecy.

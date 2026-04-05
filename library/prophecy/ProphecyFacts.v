From CRIS Require Export CRIS CallFilter ProphecyIAproof.
From stdpp Require Import base list.

Section prophecy.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !prophGS}.

  Lemma prophecy_exports_long mn fn
    (INfn: fn ∈ Prophecy.exports mn)
    :
    String.length fn > String.length mn.
  Proof.
    revert INfn. rewrite !elem_of_union !elem_of_singleton.
    rewrite /Prophecy.new /Prophecy.resolve /Prophecy.close.
    i; des; subst; s; rewrite string_length_app; nia.
  Qed.

  Lemma prophecy_refines sz (mds mdt ctx : Mod.t) (mdm : string → Mod.t) (Pm Ps : iProp Σ)
    (REF1: ∀ Q,
      refines
        (CFilter.filter (Prophecy.exports (mname_long sz)) mdt ★ ProphecyI.t (mname_long sz) ★ CFilter.filter (Prophecy.exports (mname_long sz)) ctx, Q)
        (mdm (mname_long sz) ★ ProphecyI.t (mname_long sz) ★ CFilter.filter (Prophecy.exports (mname_long sz)) ctx, (Pm ∗ Q)%I))
    (REF2: ∀ Q,
      refines
        (mdm (mname_long sz) ★ ProphecyA.t (mname_long sz) ∅ ★ CFilter.filter (Prophecy.exports (mname_long sz)) ctx, Q)
        (mds ★ CFilter.filter (Prophecy.exports (mname_long sz)) ctx, (Ps ∗ Q)%I))
    (SZ: sz > max (maxlen (elements (get_fids (dom (Mod.fnsems (mds ★ mdt ★ ctx))))))
                  (maxlen (Mod.scopes (mds ★ mdt ★ ctx))))
    (Realmdm: real_mod (mdm (mname_long sz)))
    (Realctx: real_mod ctx)
    :
    refines
      (mdt ★ ctx, emp%I)
      (mds ★ ctx, Pm ∗ ProphecyA.initial_cond ∗ Ps)%I.
  Proof.
    etrans.
    { eapply ctxr_refines, (CFilter.intro_filter (Prophecy.exports (mname_long sz))). }

    etrans.
    { eapply CFilter.intro_module with (mc := ProphecyI.t (mname_long sz)).
      { econs; [mod_tac|prove_nodup]. }
      { set_solver. }
      { intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
        eapply prophecy_exports_long in Hi2. rewrite mname_long_length in Hi2.
        rewrite Mod.dom_fnsems_add maxlen_get_fids_union in SZ. nia.
      }
      { set_solver+. }
      { set_solver+. }
    }
    rewrite CFilter.filter_app.
    etrans.
    { rewrite -assoc (comm _ _ (ProphecyI.t _)). apply REF1. }
    etrans.
    { rewrite (comm _ (ProphecyI.t _)) assoc.
      eapply ProphIA.adequacy_refines; eauto.
      eapply real_mod_add; eauto using CFilter.real_mod.
    }
    etrans.
    { rewrite -assoc (comm _ _ (ProphecyA.t _ _)). apply REF2. }
    etrans.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop.
      eapply CFilter.intro_filter. }
    erewrite <-!CFilter.filter_app. ctxr_norm.
    etrans.
    { eapply CFilter.elim_filter.
      intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
      rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi1.
      eapply prophecy_exports_long in Hi2. rewrite mname_long_length in Hi2.
      do 2 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in SZ. nia.
    }

    rewrite comm.
    eapply ctxr_refines, ctxr_consequence; iIntros "[$ [$ $]]".
  Qed.

  Lemma prophecy_main (mds mdt ctx : Mod.t) (mdm : string → Mod.t) (Pm Ps : iProp Σ) :
    (∀ mn,
      ctx_refines
        (CFilter.filter (Prophecy.exports mn) mdt ★ ProphecyI.t mn, emp%I)
        (mdm mn ★ ProphecyI.t mn, Pm)) →
    (∀ mn,
      ctx_refines
        (mdm mn ★ ProphecyA.t mn ∅, emp%I)
        (mds, Ps)) →
    (∀ mn, real_mod (mdm mn)) →
    real_mod ctx →
    refines (mdt ★ ctx, emp%I) (mds ★ ctx, Pm ∗ ProphecyA.initial_cond ∗ Ps)%I.
  Proof.
    intros REF1 REF2 Rmdm Rctx; s.
    set (sz := S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems (mds ★ mdt ★ ctx))))))
                 (maxlen (Mod.scopes (mds ★ mdt ★ ctx))))).
    eapply prophecy_refines with (sz:=sz); i; eauto using prophecy_exports_long; try nia.
    - eapply ctxr_refines. rewrite !assoc -{1}(left_id _ bi_sep Q).
      eapply ctxr_frameR, ctxr_cond_frameR. eapply REF1.
    - eapply ctxr_refines. rewrite !assoc -{1}(left_id _ bi_sep Q).
      eapply ctxr_frameR, ctxr_cond_frameR. eapply REF2.
  Qed.

End prophecy.

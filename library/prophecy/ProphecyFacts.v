From CRIS.common Require Export CRIS.
From CRIS.filter Require Export CallFilter.
From CRIS.prophecy Require Export ProphecyIAproof.
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

  Lemma prophecy_refines sz (mds mdt ctx : Mod.t)
      (mdm : string → Mod.t)
    (SZ: sz > max (maxlen (elements (get_fids (dom
                  (Mod.fnsems (mds ★ mdt ★ ctx))))))
                  (maxlen (Mod.scopes (mds ★ mdt ★ ctx))))
    (Realmdm: real_mod (mdm (mname_long sz)))
    (Realctx: real_mod ctx)
    :
    refines
        (CFilter.filter (Prophecy.exports (mname_long sz)) mdt ★
          ProphecyI.t (mname_long sz) ★
          CFilter.filter (Prophecy.exports (mname_long sz)) ctx)
        (mdm (mname_long sz) ★ ProphecyI.t (mname_long sz) ★
          CFilter.filter (Prophecy.exports (mname_long sz)) ctx) ∗
      ProphecyA.initial_cond ∗
      refines
        (mdm (mname_long sz) ★ ProphecyA.t (mname_long sz) ∅ ★
          CFilter.filter (Prophecy.exports (mname_long sz)) ctx)
        (mds ★
          CFilter.filter (Prophecy.exports (mname_long sz)) ctx) ⊢
      refines (mdt ★ ctx) (mds ★ ctx).
  Proof.
    iIntros "[REF1 [INIT REF2]]".
    iApply refines_trans. iSplitR "REF1 INIT REF2".
    { iApply ctxr_refines.
      iApply (CFilter.intro_filter
        (Prophecy.exports (mname_long sz))).
    }

    iApply refines_trans. iSplitR "REF1 INIT REF2".
    { iApply (CFilter.intro_module
        (Prophecy.exports (mname_long sz)) (mdt ★ ctx)
        (ProphecyI.t (mname_long sz))).
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
    iApply refines_trans. iSplitL "REF1".
    { rewrite -assoc (comm _ _ (ProphecyI.t _)).
      iExact "REF1".
    }
    iApply refines_trans. iSplitL "INIT".
    { rewrite (comm _ (ProphecyI.t _)) assoc.
      iApply ProphIA.adequacy_refines.
      eapply real_mod_add; eauto using CFilter.real_mod.
      done.
    }
    iApply refines_trans. iSplitL "REF2".
    { rewrite -assoc (comm _ _ (ProphecyA.t _ _)).
      iExact "REF2".
    }
    iApply refines_trans. iSplitR.
    { iApply ctxr_refines. iApply ctxr_frameR.
      iApply CFilter.intro_filter.
    }
    erewrite <-!CFilter.filter_app.
    { iApply CFilter.elim_filter.
      intros i Hi1 Hi2; rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
      rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi1.
      eapply prophecy_exports_long in Hi2. rewrite mname_long_length in Hi2.
      do 2 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in SZ. nia.
    }
  Qed.

  Lemma prophecy_main (mds mdt ctx : Mod.t) (mdm : string → Mod.t) :
    (∀ mn, real_mod (mdm mn)) →
    real_mod ctx →
    (∀ mn,
      ctx_refines
        (CFilter.filter (Prophecy.exports mn) mdt ★ ProphecyI.t mn)
        (mdm mn ★ ProphecyI.t mn)) ∗
      ProphecyA.initial_cond ∗
      (∀ mn,
      ctx_refines
        (mdm mn ★ ProphecyA.t mn ∅)
        mds) ⊢
      refines (mdt ★ ctx) (mds ★ ctx).
  Proof.
    intros Rmdm Rctx; s.
    set (sz := S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems (mds ★ mdt ★ ctx))))))
                 (maxlen (Mod.scopes (mds ★ mdt ★ ctx))))).
    iIntros "[REF1 [INIT REF2]]".
    iApply (prophecy_refines sz mds mdt ctx mdm); try nia; eauto.
    iSplitL "REF1".
    - iApply ctxr_refines. rewrite !assoc.
      iApply (ctxr_frameR
        (CFilter.filter (Prophecy.exports (mname_long sz)) mdt ★
          ProphecyI.t (mname_long sz))
        (mdm (mname_long sz) ★ ProphecyI.t (mname_long sz))
        (CFilter.filter (Prophecy.exports (mname_long sz)) ctx)).
      iSpecialize ("REF1" $! (mname_long sz)). done.
    - iFrame "INIT". iApply ctxr_refines. rewrite !assoc.
      iApply (ctxr_frameR
        (mdm (mname_long sz) ★ ProphecyA.t (mname_long sz) ∅)
        mds
        (CFilter.filter (Prophecy.exports (mname_long sz)) ctx)).
      iSpecialize ("REF2" $! (mname_long sz)). done.
  Qed.

End prophecy.

From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From CRIS.helping Require Export HelpingOnOffproof.
From CRIS.filter Require Export CallFilter.
From stdpp Require Import base list.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

  Lemma helping_on_wf mn jobs : Mod.wf (HelpingOn.t mn jobs).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  Lemma helping_dummy_wf mn : Mod.wf (HelpingDummy.t mn).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  Lemma helping_exports_long mn fn :
    fn ∈ Helping.exports mn →
    String.length fn > String.length mn.
  Proof.
    rewrite elem_of_union !elem_of_singleton /Helping.run /Helping.help.
    i; des; subst; s; rewrite string_length_app; nia.
  Qed.

  Lemma helping_refines fns (mM : string → Mod.t) (mA mI ctx : Mod.t) jobs
    (DISJ: get_fids (dom (Mod.fnsems (mA ★ SchI.t ★ ctx))) ## fns) :
    (∀ mn,
      refines
        (CFilter.filter (Helping.exports mn) mI ★
          CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★
          HelpingDummy.t mn)
        (mM mn ★
          CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★
          HelpingOn.t mn jobs)) ∗
    (∀ mn,
      refines
        (mM mn ★
          CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★
          HelpingOff.t mn jobs)
        (mA ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx))) ⊢
    refines
      (mI ★ CFilter.filter fns (SchI.t ★ ctx))
      (mA ★ SchI.t ★ ctx).
  Proof using H.
    iIntros "[REF1 REF2]".
    set (mn := mname_long (S (max
      (maxlen (elements (get_fids (dom (Mod.fnsems (mA ★ mI ★ SchI.t ★ ctx))))))
      (maxlen (Mod.scopes (mA ★ mI ★ SchI.t ★ ctx)))))).

    iApply refines_trans. iSplitR "REF1 REF2".
    { iApply ctxr_refines. iApply (CFilter.intro_filter (Helping.exports mn)). }

    iApply refines_trans. iSplitR "REF1 REF2".
    { iApply (CFilter.intro_module (Helping.exports mn)
        (mI ★ CFilter.filter fns (SchI.t ★ ctx)) (HelpingDummy.t mn)); et.
      { eapply helping_dummy_wf. }
      { intros ? a ->%elem_of_list_singleton. subst mn. eapply elem_of_maxlen in a.
        rewrite mname_long_length !Mod.maxlen_scopes_add in a. nia.
      }
      { intros i Hi1 Hi2. rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
        eapply helping_exports_long in Hi2. rewrite mname_long_length in Hi2.
        rewrite !CFilter.filter_app in Hi1.
        do 3 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi2.
        do 2 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi1.
        rewrite /maxlen /get_fids in Hi1, Hi2.
        do 2 rewrite (dom_fmap (λ x, map_fst (CFilter.msk_filter_out fns) <$> x)) in Hi1.
        nia.
      }
      { set_solver+. }
      { set_solver+. }
    }

    iApply refines_trans. iSplitL "REF1".
    { rewrite CFilter.filter_app -CFilter.filter_union -!assoc.
      iApply ("REF1" $! mn).
    }

    iApply (refines_trans _
      (mM mn ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★
        HelpingOff.t mn jobs) _).
    iSplitR "REF2".
    { iApply ctxr_refines.
      rewrite !CFilter.filter_app.
      replace
        (mM mn ★
          (CFilter.filter (Helping.exports mn ∪ fns) SchI.t ★
            CFilter.filter (Helping.exports mn ∪ fns) ctx) ★
          HelpingOn.t mn jobs)
        with
        ((mM mn ★ CFilter.filter (Helping.exports mn ∪ fns) ctx) ★
          (HelpingOn.t mn jobs ★
            CFilter.filter (Helping.exports mn ∪ fns) SchI.t))
        by mod_eq_solver.
      replace
        (mM mn ★
          (CFilter.filter (Helping.exports mn ∪ fns) SchI.t ★
            CFilter.filter (Helping.exports mn ∪ fns) ctx) ★
          HelpingOff.t mn jobs)
        with
        ((mM mn ★ CFilter.filter (Helping.exports mn ∪ fns) ctx) ★
          (HelpingOff.t mn jobs ★
            CFilter.filter (Helping.exports mn ∪ fns) SchI.t))
        by mod_eq_solver.
      iApply ctxr_frameL.
      iApply helping_onoff_correct. set_solver.
    }

    iApply refines_trans. iSplitL "REF2".
    { iApply ("REF2" $! mn).
    }

    iApply (refines_trans _
      (CFilter.filter (Helping.exports mn ∪ fns) (mA ★ SchI.t ★ ctx)) _).
    iSplitR.
    { iApply ctxr_refines.
      replace
        (mA ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx))
        with
        (CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★ mA)
        by mod_eq_solver.
      replace
        (CFilter.filter (Helping.exports mn ∪ fns) (mA ★ SchI.t ★ ctx))
        with
        (CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★
          CFilter.filter (Helping.exports mn ∪ fns) mA)
        by (rewrite !CFilter.filter_app; mod_eq_solver).
      iApply ctxr_frameL. iApply CFilter.intro_filter.
    }
    iApply CFilter.elim_filter.
      rewrite disjoint_union_r. split; et.
      intros i Hi1 Hi2. rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
      eapply helping_exports_long in Hi2. rewrite mname_long_length in Hi2.
      rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi1.
      do 2 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi2. nia.
  Qed.

  Lemma helping_main (mM : string → Mod.t) (mA mI mE : Mod.t) jobs :
    (∀ mn,
      ctx_refines
        (CFilter.filter (Helping.exports mn) (mI ★ mE ★ SchI.t) ★
          HelpingDummy.t mn)
        (mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★
          HelpingOn.t mn jobs)) ∗
    (∀ mn,
      ctx_refines
        (mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★
          HelpingOff.t mn jobs)
        (mA ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t))) ⊢
    ctx_refines
      (mI ★ mE ★ SchI.t)
      (mA ★ mE ★ SchI.t).
  Proof.
    iIntros "[REF1 REF2]" (ctx).
    replace
      ((mI ★ mE ★ SchI.t) ★ ctx)
      with
      (mI ★ (SchI.t ★ (mE ★ ctx)))
      by (rewrite !assoc;
          rewrite -(assoc _ mI mE SchI.t) (comm _ mE SchI.t);
          rewrite (assoc _ mI SchI.t mE); et).
    rewrite -(CFilter.filter_empty (SchI.t ★ (mE ★ ctx))).
    replace
      ((mA ★ mE ★ SchI.t) ★ ctx)
      with
      (mA ★ SchI.t ★ (mE ★ ctx))
      by (rewrite !assoc;
          rewrite -(assoc _ mA mE SchI.t) (comm _ mE SchI.t);
          rewrite (assoc _ mA SchI.t mE); et).
    iApply (helping_refines ∅ mM mA mI (mE ★ ctx) jobs).
    - apply disjoint_empty_r.
    - iSplitL "REF1".
      + iIntros (mn). iApply ctxr_refines.
        replace (Helping.exports mn ∪ ∅) with (Helping.exports mn)
          by set_solver.
        replace
          (CFilter.filter (Helping.exports mn) mI ★
            CFilter.filter (Helping.exports mn) (SchI.t ★ (mE ★ ctx)) ★
            HelpingDummy.t mn)
          with
          ((CFilter.filter (Helping.exports mn) (mI ★ mE ★ SchI.t) ★
              HelpingDummy.t mn) ★
            CFilter.filter (Helping.exports mn) ctx)
          by (rewrite !CFilter.filter_app; mod_eq_solver).
        replace
          (mM mn ★
            CFilter.filter (Helping.exports mn) (SchI.t ★ (mE ★ ctx)) ★
            HelpingOn.t mn jobs)
          with
          ((mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★
              HelpingOn.t mn jobs) ★
            CFilter.filter (Helping.exports mn) ctx)
          by (rewrite !CFilter.filter_app; mod_eq_solver).
        iApply ctxr_frameR. iApply ("REF1" $! mn).
      + iIntros (mn). iApply ctxr_refines.
        replace (Helping.exports mn ∪ ∅) with (Helping.exports mn)
          by set_solver.
        replace
          (mM mn ★
            CFilter.filter (Helping.exports mn) (SchI.t ★ (mE ★ ctx)) ★
            HelpingOff.t mn jobs)
          with
          ((mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★
              HelpingOff.t mn jobs) ★
            CFilter.filter (Helping.exports mn) ctx)
          by (rewrite !CFilter.filter_app; mod_eq_solver).
        replace
          (mA ★ CFilter.filter (Helping.exports mn) (SchI.t ★ (mE ★ ctx)))
          with
          ((mA ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t)) ★
            CFilter.filter (Helping.exports mn) ctx)
          by (rewrite !CFilter.filter_app; mod_eq_solver).
        iApply ctxr_frameR. iApply ("REF2" $! mn).
  Qed.
End Helping.

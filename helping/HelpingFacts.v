Require Import CRIS.
Require Import SchHeader SchI SchA.
Require Export HelpingOnOffproof.
Require Export CallFilter.
From stdpp Require Import base list.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

  Lemma helping_on_wf {jobID retID} mn (jobs : jobID → _) : Mod.wf (HelpingOn.t (retID:=retID) mn jobs ∅).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  Lemma helping_dummy_wf mn : Mod.wf (HelpingDummy.t mn).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  Lemma helping_exports_long mn fn
    (INfn: fn ∈ Helping.exports mn)
    :
    String.length fn > String.length mn.
  Proof.
    revert INfn. rewrite elem_of_union !elem_of_singleton /Helping.run /Helping.help.
    i; des; subst; s; rewrite string_length_app; nia.
  Qed.

  Lemma helping_refines fns (mM : string → Mod.t) (mA mI ctx: Mod.t) (P1 P2 P: iProp Σ)
    {jobID retID : Type} (jobs : jobID -> _) (sp : specmap)
    (REF1: ∀ Q mn,
      refines
        (CFilter.filter (Helping.exports mn) mI ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★ (HelpingDummy.t mn), Q)
        (mM mn ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★ (HelpingOn.t (retID:=retID) mn jobs sp), (P1 ∗ Q)%I))
    (REF2: ∀ Q mn,
      refines
        (mM mn ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx) ★ HelpingOff.t mn jobs sp, Q)
        (mA ★ CFilter.filter (Helping.exports mn ∪ fns) (SchI.t ★ ctx), (P2 ∗ Q)%I))
    (DISJ: get_fids (dom (Mod.fnsems (mA ★ SchI.t ★ ctx))) ## fns)
    :
    refines
      (mI ★ CFilter.filter fns (SchI.t ★ ctx), P)
      (mA ★ SchI.t ★ ctx, (P1 ∗ P2 ∗ P)%I).
  Proof using.
    set (mn := mname_long (S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems (mA ★ mI ★ SchI.t ★ ctx))))))
                 (maxlen (Mod.scopes (mA ★ mI ★ SchI.t ★ ctx)))))).

    etrans.
    { eapply ctxr_refines, (CFilter.intro_filter (Helping.exports mn)). }

    etrans.
    { eapply CFilter.intro_module with (mask := Helping.exports mn) (mc := (HelpingDummy.t mn)); et.
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

    etrans.
    { rewrite CFilter.filter_app -CFilter.filter_union -!assoc. apply REF1. }

    etrans.
    { eapply ctxr_refines.
      rewrite CFilter.filter_app.
      ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply helping_onoff_correct; et. set_solver.
    }

    etrans.
    { evar_at_last_2; [apply REF2|]. 
      do 2 f_equal. rewrite !CFilter.filter_app -!assoc.
      rewrite (comm _ (_ _ SchI.t)) assoc. refl.
    }

    etrans.
    { eapply ctxr_refines.
      ctxr_rotate. ctxr_drop. eapply CFilter.intro_filter.
    }
    repeat erewrite <-CFilter.filter_app. rewrite (comm _ _ mA).
    etrans.
    { eapply CFilter.elim_filter.
      rewrite disjoint_union_r. split; et.
      intros i Hi1 Hi2. rewrite -elem_of_elements in Hi1; eapply elem_of_maxlen in Hi1.
      eapply helping_exports_long in Hi2. rewrite mname_long_length in Hi2.
      rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi1.
      do 2 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in Hi2. nia.
    }

    eapply ctxr_refines.
    eapply ctxr_consequence. iIntros "[$ [$ $]]".
  Qed.

  Lemma helping_main (mM : string → Mod.t) (mA mI mE : Mod.t) (P1 P2 : iProp Σ)
      {jobID retID : Type} (jobs : jobID -> _) (sp : specmap) :
    (∀ mn,
      ctx_refines
        (CFilter.filter (Helping.exports mn) (mI ★ mE ★ SchI.t) ★ (HelpingDummy.t mn), emp%I)
        (mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★ (HelpingOn.t (retID:=retID) mn jobs sp), P1)) →
    (∀ mn,
      (ctx_refines
        (mM mn ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t) ★ HelpingOff.t mn jobs sp, emp%I))
        (mA    ★ CFilter.filter (Helping.exports mn) (mE ★ SchI.t), P2)) →
    ctx_refines
      (mI ★ mE ★ SchI.t, emp%I)
      (mA ★ mE ★ SchI.t, (P1 ∗ P2)%I).
  Proof.
    intros REF1 REF2 [ctx P]; s.
    rewrite (comm _ mE) -!assoc.
    etrans; [|eapply helping_refines with (mI := mI) (mM := mM) (fns:=∅)]; cycle 1; i.
    - rewrite CFilter.filter_union CFilter.filter_empty -{1}(left_id _ bi_sep Q).
      evar_at_last_1; [evar_at_last_2|]; [eapply (REF1 _ (_,_))|..]; s.
      + f_equal. rewrite !CFilter.filter_app. instantiate (1:= _ _ ctx). mod_eq_solver.
      + f_equal. rewrite !CFilter.filter_app. mod_eq_solver.
    - rewrite CFilter.filter_union CFilter.filter_empty -{1}(left_id _ bi_sep Q).
      evar_at_last_1; [evar_at_last_2|]; [eapply (REF2 _ (_,_))|..]; s.
      + f_equal. rewrite !CFilter.filter_app. instantiate (1:= _ _ ctx). mod_eq_solver.
      + f_equal. rewrite !CFilter.filter_app. mod_eq_solver.
    - apply disjoint_empty_r.
    - rewrite CFilter.filter_empty left_id. refl.
  Qed.
  
End Helping.

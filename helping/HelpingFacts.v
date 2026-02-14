Require Import CRIS.
Require Import SchHeader SchI SchA.
Require Export HelpingOnOffproof.
Require Export CallFilter.
From stdpp Require Import base list.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

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
  Proof.
    i; eapply max_list_elem_of_le, elem_of_list_fmap; esplits; eauto.
  Qed.

  Local Lemma maxlen_union s1 s2 : maxlen (s1 ++ s2) = maxlen s1 `max` maxlen s2.
  Proof. rewrite /maxlen fmap_app list_max_app //. Qed.

  Lemma helping_on_wf {jobID retID} mn (jobs : jobID → _) : Mod.wf (HelpingOn.t (retID:=retID) mn jobs ∅).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  Lemma helping_dummy_wf mn : Mod.wf (HelpingDummy.t mn).
  Proof. econs; [mod_tac|prove_nodup]. Qed.

  (* imp : list of function names mI calls *)
  (* TODO : modify sp according to the proof of helpingonoff *)
  Lemma helping_main (mM : string → Mod.t) (mA mI m_aux : Mod.t) (P1 P2 : iProp Σ)
      {jobID retID : Type} (jobs : jobID -> _) (sp : specmap) :
    (∀ mn,
      ctx_refines
        (mM mn ★ CFilter.filter (Helping.exports mn) (m_aux ★ SchI.t) ★ (HelpingOn.t (retID:=retID) mn jobs sp), P1)
        (CFilter.filter (Helping.exports mn) (mI ★ m_aux ★ SchI.t) ★ (HelpingDummy.t mn), emp%I)) →
    (∀ mn,
      (ctx_refines
        (mA    ★ CFilter.filter (Helping.exports mn) (m_aux ★ SchI.t), P2)
        (mM mn ★ CFilter.filter (Helping.exports mn) (m_aux ★ SchI.t) ★ HelpingOff.t mn jobs sp, emp%I))) →
    ctx_refines
      (mA ★ m_aux ★ SchI.t, (P1 ∗ P2)%I)
      (mI ★ m_aux ★ SchI.t, emp%I).
  Proof using.
    intros Hc1 Hc2 [ctx P]; s.
    ctxr_norm.
    match goal with [|-refines (?src,?P1) (?tgt,?P2)] =>
      pose (md_src := src);
      pose (md_tgt := tgt);
      pose (all_names :=
        (elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems md_src)) : gset string)) ++
        (elements (set_omap (λ a, match a with | fid fn => Some fn | _ => None end) (dom (Mod.fnsems md_tgt)) : gset string)) ++
        (Mod.scopes md_src) ++ (Mod.scopes md_tgt) : list string)
    end.

    etrans; cycle 1.
    { eapply ctxr_refines.
      eapply CFilter.intro_filter.
    }

    pose (mn := mname_long (S (maxlen all_names))).

    etrans; cycle 1.
    { eapply CFilter.intro_module with
        (mask := Helping.exports mn) (mc := (HelpingDummy.t mn)); et.
      { eapply helping_dummy_wf. }
      { s; intros ? a ->%elem_of_list_singleton.
        eapply elem_of_maxlen in a.
        subst mn all_names md_tgt md_src.
        rewrite mname_long_length ?maxlen_union in a; ss. lia.
      }
      { intros ? Hx%elem_of_elements%elem_of_maxlen; intros
          [?%elem_of_singleton|?%elem_of_singleton]%elem_of_union; subst;
        subst mn all_names md_tgt md_src;
        rewrite !Mod.dom_fnsems_add !set_omap_union_L ?maxlen_union in Hx;
        rewrite string_length_app mname_long_length in Hx; lia.
      }
      { set_solver+. }
      { set_solver+. }
    }

    erewrite ?CFilter.filter_app.

    etrans; cycle 1.
    { eapply ctxr_refines.
      do 3 ctxr_rotate. ctxr_drop. ctxr_rotate.
      hexploit (Hc1 mn); rewrite ?CFilter.filter_app; ctxr_norm.
    }

    etrans; cycle 1.
    { eapply ctxr_refines.
      do 3 ctxr_drop. ctxr_swap.
      eapply helping_onoff_correct; et.
    }

    etrans; cycle 1.
    { eapply ctxr_refines.
      ctxr_drop.
      rewrite /mod_src.
      do 3 ctxr_rotate. ctxr_swap. ctxr_rotate; ctxr_swap.
      do 3 ctxr_rotate. rewrite -?mod_add_assoc. rewrite (mod_add_assoc (mM _)).
      erewrite <-CFilter.filter_app. rewrite mod_add_assoc.
      eapply Hc2; et.
    }

    etrans; cycle 1.
    { eapply ctxr_refines.
      do 2 ctxr_rotate. do 2 ctxr_drop. eapply CFilter.intro_filter.
    }

    etrans; cycle 1.
    { eapply ctxr_refines. do 2 ctxr_rotate. ctxr_refl. }

    erewrite <-!CFilter.filter_app. ctxr_norm.
    etrans; [|eapply CFilter.elim_filter]; cycle 1.
    { intros ? Hx%elem_of_elements%elem_of_maxlen; intros
          [?%elem_of_singleton|?%elem_of_singleton]%elem_of_union; subst;
      subst mn all_names md_tgt md_src;
      rewrite !Mod.dom_fnsems_add !set_omap_union_L ?maxlen_union in Hx;
      rewrite string_length_app mname_long_length in Hx; lia.
    }

    eapply ctxr_refines.
    eapply ctxr_cond_strengthen.
    iIntros "[[P1 P2] P]". iFrame.
  Qed.
End Helping.

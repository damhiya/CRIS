Require Import CRIS.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff HelpingOnOffproof.
From stdpp Require Import list.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  (* Lemmas about names *)
  Local Definition maxlen (s : gset string) : nat :=
    list_max (String.length <$> elements s).

  Local Fixpoint mname_long (n : nat) : string :=
    match n with
    | 0 => ""
    | S n' => "h" +:+ mname_long n'
    end.

  Local Lemma mname_long_length n : String.length (mname_long n) = n.
  Proof. induction n; ss. rewrite IHn. et. Qed.

  Local Lemma elem_of_maxlen (fn : string) (s : gset string) :
    fn ∈ s → String.length fn ≤ maxlen s.
  Proof.
    i; eapply max_list_elem_of_le, elem_of_list_fmap; esplits; eauto.
    by apply elem_of_elements.
  Qed.

  Local Lemma maxlen_union s1 s2 : maxlen (s1 ∪ s2) = maxlen s1 `max` maxlen s2.
  Proof.
    revert s2; eapply (set_ind_L (λ s, ∀ s2, maxlen (s ∪ s2) = maxlen s `max` maxlen s2)).
    { i; rewrite /maxlen left_id_L elements_empty //=. }
    intros x X Hx IH s2.
    rewrite (union_comm_L _ X) -union_assoc_L ?IH -Nat.max_assoc; f_equal.
    rewrite {2}/maxlen elements_singleton /= Nat.max_0_r.
    generalize s2 x; clear.
    intros s x; destruct (decide (x ∈ s)); cycle 1.
    { rewrite /maxlen elements_disj_union; [|set_solver].
      rewrite fmap_app ?elements_singleton //=.
    }
    replace (_ ∪ s) with s by set_solver; hexploit (elem_of_maxlen x s); eauto; lia.
  Qed.

  Lemma helping_on_wf {jobID retID} mn (jobs : jobID → _) : Mod.wf (HelpingOn.t (retID:=retID) mn jobs ∅).
  Proof.
    econs; ss.
    { unfold_fnsem. rewrite /HelpingOn.fnsems /= ?fmap_insert fmap_empty. mod_tac scope_solver. }
    { rewrite /HelpingOn.scopes; multiset_solver. }
  Qed.

  Lemma helping_dummy_wf mn : Mod.wf (HelpingDummy.t mn).
  Proof.
    econs; ss.
    { unfold_fnsem. rewrite /HelpingOn.fnsems /= ?fmap_insert fmap_empty. mod_tac scope_solver. }
    { rewrite /HelpingDummy.scopes; multiset_solver. }
  Qed.

  (* imp : list of function names mI calls *)
  (* TODO : modify sp according to the proof of helpingonoff *)
  Lemma helping_main (mM : string → Mod.t) (mA mI m_aux : Mod.t) (P1 P2 : iProp Σ)
      {jobID retID} (jobs : jobID -> _) (sp : specmap) :
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
        (set_omap id (dom (Mod.fnsems md_src) ∪ dom (Mod.fnsems md_tgt))) ∪
        dom (Mod.scopes md_src) ∪ dom (Mod.scopes md_tgt) : gset string)
    end.
      (* cut(refines (src,P1) (tgt,P2))
    end.
    { intros Hg WFM; ss. eapply Hg; et. destruct WFM. et. }
    intros NODUP. *)

    etrans; cycle 1.
    { eapply ctxr_refines.
      eapply CFilter.intro_filter.
    }

    pose (mn := mname_long (S (maxlen all_names))).
    (* pose (mask := wmask_list all_names). *)

    (* assert (DISJ : Helping.exports mn ## imp).
    { intros x H1 H2. eapply (long_name_notin _ x); cycle 1.
      { unfold wmask_list. eapply existsb_exists.
        esplits; [|apply String.eqb_eq]; et.
        apply elem_of_list_In, H2.
      }
      { rewrite /Helping.exports elem_of_cons in H1. des; ss; subst.
        { rewrite /Helping.exports /Helping.run /mn /=.
          rewrite !strings_maxlen_app !string_length_app.
          rewrite /Helping.exports mname_long_length /=. nia.
        }
        { apply elem_of_cons in H1; des; last inv H1. subst mn x. ss. fold append.
          rewrite !strings_maxlen_app !string_length_app.
          rewrite mname_long_length. nia.
        }
      }
    } *)

    (* assert (SUB : wmask_sub (wmask_list imp) mask).
    { unfold mask, wmask_sub, wmask_list.
      intros ? Hin. eapply existsb_exists in Hin. des.
      eapply existsb_exists. esplits; et.
      eapply in_or_app; et.
    } *)

    etrans; cycle 1.
    { eapply CFilter.intro_module with
        (mask := Helping.exports mn) (mc := (HelpingDummy.t mn)); et.
      { eapply helping_dummy_wf. }
      { intros ? a%gmultiset_elem_of_dom ->%gmultiset_elem_of_singleton.
        eapply elem_of_maxlen in a.
        subst mn all_names md_tgt md_src.
        rewrite mname_long_length ?maxlen_union in a; lia.
      }
      { intros x Hx%elem_of_maxlen [?%elem_of_singleton|?%elem_of_singleton]%elem_of_union; subst;
          subst mn all_names; rewrite string_length_app mname_long_length ?set_omap_union_L
          ?maxlen_union /md_src /md_tgt /= in Hx; lia.
      }
      { set_solver+. }
      { set_solver+. }
    }

    erewrite ?CFilter.filter_app.
    (* etrans; cycle 1.
    { eapply ctxr_refines. ctxr_norm.
      erewrite ?CFilter.filter_app.
      ctxr_refl.
    } *)

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
    { intros x Hx%elem_of_maxlen [?%elem_of_singleton|?%elem_of_singleton]%elem_of_union; subst;
        subst mn all_names; rewrite string_length_app mname_long_length ?set_omap_union_L
        ?maxlen_union /md_src /md_tgt /= in Hx; lia.
    }

    eapply ctxr_refines.
    eapply ctxr_cond_strengthen.
    iIntros "[[P1 P2] P]". iFrame.
  Qed.
End Helping.

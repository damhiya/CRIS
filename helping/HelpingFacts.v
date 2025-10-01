Require Import CRIS.
Require Import SchHeader SchI.
From CRIS.helping Require Import Header HelpingOn HelpingOff HelpingOnOffproof.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !schG}.

  (* Lemmas about names *)
  Definition strings_maxlen (l : list string) : nat :=
    list_max (List.map String.length l).

  Fixpoint mname_long (n : nat) : string :=
    match n with
    | 0 => ""
    | S n' => "h" +:+ mname_long n'
    end.

  Lemma mname_long_length n :
    String.length (mname_long n) = n.
  Proof.
    induction n; ss.
    rewrite IHn. et.
  Qed.

  Lemma strings_maxlen_app l1 l2 :
    strings_maxlen (l1 ++ l2) = max (strings_maxlen l1) (strings_maxlen l2).
  Proof.
    revert l2. induction l1; et.
    i. s. unfold strings_maxlen in *. ss.
    rewrite IHl1. nia.
  Qed.

  Lemma long_name_notin l (fn : string) :
    String.length fn > strings_maxlen l →
    ~ wmask_list l fn.
  Proof.
    intros Hlen Hmsk. eapply existsb_exists in Hmsk. des. eapply String.eqb_eq in Hmsk0; subst.
    revert_until l. induction l; i; ss.
    des; subst.
    - rewrite /strings_maxlen in Hlen. ss. nia.
    - eapply IHl; et. unfold strings_maxlen in *. ss. nia.
  Qed.

  Lemma helping_dummy_wf mn : Mod.wf (HelpingDummy.t mn).
  Proof. unfold_mod. econs; ss; prove_nodup. Qed.

  (* imp : list of function names mI calls *)
  Lemma helping_main (mM : string → Mod.t) (mA mI m_aux : Mod.t) (P1 P2 : iProp Σ) imp
      {jobID retID} (jobs : jobID -> _) (sp : string → sp_type) :
    (∀ mn msk,
      ((Helping.exports mn) ## imp →
      wmask_sub (wmask_list imp) msk →
      ctx_refines
        (mM mn ★ CFilter.filter msk (m_aux ★ SchI.t) ★ (HelpingOn.t (retID:=retID) mn jobs (sp mn)), P1)
        (CFilter.filter msk (mI ★ m_aux ★ SchI.t) ★ HelpingDummy.t mn, emp%I))) →
    (∀ mn msk,
      ((Helping.exports mn) ## imp →
      wmask_sub (wmask_list imp) msk →
      ctx_refines
        (mA    ★ CFilter.filter msk (m_aux ★ SchI.t), P2)
        (mM mn ★ CFilter.filter msk (m_aux ★ SchI.t) ★ HelpingOff.t mn jobs (sp mn), emp%I))) →
    ctx_refines
      (mA ★ m_aux ★ SchI.t, (P1 ∗ P2)%I)
      (mI ★ m_aux ★ SchI.t, emp%I).
  Proof.
    intros Hc1 Hc2 [ctx P]; s.
    ctxr_norm.

    match goal with [|-refines (?src,?P1) (?tgt,?P2)] =>
      pose (md_src := src);
      pose (md_tgt := tgt);
      pose (all_names :=
        imp ++ omap id (Mod.exports md_src) ++ omap id (Mod.exports md_tgt)
                           ++ Mod.scopes md_src ++ Mod.scopes md_tgt);
      cut(List.NoDup (Mod.scopes tgt) -> refines (src,P1) (tgt,P2))
    end.
    { intros Hg WFM; ss. eapply Hg; et. destruct WFM. et. }
    intros NODUP.

    etrans; cycle 1.
    { eapply ctxr_refines.
      eapply CFilter.intro_filter.
    }

    pose (mn := mname_long (10 + strings_maxlen all_names)).
    pose (mask := wmask_list all_names).

    assert (DISJ : Helping.exports mn ## imp).
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
    }

    assert (SUB : wmask_sub (wmask_list imp) mask).
    { unfold mask, wmask_sub, wmask_list.
      intros ? Hin. eapply existsb_exists in Hin. des.
      eapply existsb_exists. esplits; et.
      eapply in_or_app; et.
    }

    etrans; cycle 1.
    { eapply CFilter.intro_module with (mask := mask) (mc := HelpingDummy.t mn); et.
      - eapply helping_dummy_wf.
      - i. r. rewrite existsb_exists.
        esplits; try apply String.eqb_eq; eauto.
        do 2 (eapply in_or_app; right).
        eapply in_or_app; left; rewrite /Mod.exports; subst md_tgt.
        rewrite -elem_of_list_In elem_of_list_omap; eexists; rewrite elem_of_list_In //.
      - intros fn IN.
        eapply long_name_notin.
        revert IN. unfold_mod. s. i. des; subst; try by ss.
        { inv IN. simpl String.length. fold append.
          rewrite !strings_maxlen_app !string_length_app mname_long_length.
          nia.
        }
        { inv IN. simpl String.length. fold append.
          rewrite !strings_maxlen_app !string_length_app mname_long_length.
          nia.
        }
      - unfold_mod; ss; ii; des; ss.
      - eapply List.NoDup_app.
        + unfold_mod; ss.
        + unfold_mod; ss. econs; ss. econs; ss.
        + intros a Ha Ha2; eapply (long_name_notin _ a); cycle 1.
          * rewrite /wmask_list; eapply existsb_exists.
            esplits; [apply Ha|apply String.eqb_eq]; eauto.
          * revert Ha2; unfold_mod; intros Ha2.
            rr in Ha2; des; ss; subst.
            unfold mn; rewrite !strings_maxlen_app; s.
            rewrite mname_long_length; nia.
    }
    rewrite !CFilter.filter_app.

    etrans; cycle 1.
    {
      eapply ctxr_refines. ctxr_norm.
      do 3 ctxr_rotate. do 2 ctxr_drop. erewrite <- ?CFilter.filter_app.
      ctxr_refl.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines; ctxr_norm.
      ctxr_drop. ctxr_rotate. eapply Hc1; eauto.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      do 2 ctxr_drop. rewrite CFilter.filter_app. ctxr_drop. ctxr_swap.
      eapply helping_onoff_correct; et.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      ctxr_drop. rewrite /mod_off. do 3 ctxr_rotate. ctxr_swap. ctxr_rotate; ctxr_swap.
      do 3 ctxr_rotate. rewrite -?mod_add_assoc. rewrite (mod_add_assoc (mM _)).
      erewrite <-CFilter.filter_app. rewrite mod_add_assoc.
      eapply Hc2; et.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      do 2 ctxr_rotate. do 2 ctxr_drop. eapply CFilter.intro_filter.
    }

    etrans; cycle 1.
    { eapply ctxr_refines. do 2 ctxr_rotate. ctxr_refl. }

    erewrite <-!CFilter.filter_app. ctxr_norm.
    etrans; [|eapply CFilter.elim_filter]; cycle 1.
    {
      intros fn Hin; eapply existsb_exists.
      exists fn; split; last apply String.eqb_refl.
      apply in_or_app; right.
      apply in_or_app; left.
      rewrite /md_src /Mod.exports.
      apply elem_of_list_In, elem_of_list_omap; exists (Some fn); split; ss.
      apply elem_of_list_In; eauto.
    }

    eapply ctxr_refines.
    eapply ctxr_cond_strengthen.
    iIntros "[[P1 P2] P]". iFrame.
  Qed.

End Helping.  

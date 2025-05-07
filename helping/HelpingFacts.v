Require Import CRIS.
Require Import SchHeader SchA.
Require Import HelpingHeader HelpingOn HelpingOff HelpingOnOffproof.
Require Import CallFilter.

Section Helping.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_schG: !schG}.

  (* Lemmas about names *)
  
  Definition strings_maxlen (l: list string) : nat :=
    list_max (List.map String.length l).

  Fixpoint mname_long (n: nat) : string :=
    match n with
    | 0 => ""
    | S n' => "h" +:+ mname_long n'
    end.

  Lemma mname_long_length n:
    String.length (mname_long n) = n.
  Proof.
    induction n; ss.
    rewrite IHn. et.
  Qed.

  Lemma strings_maxlen_app l1 l2:
    strings_maxlen (l1++l2) = max (strings_maxlen l1) (strings_maxlen l2).
  Proof.
    revert l2. induction l1; et.
    i. s. unfold strings_maxlen in *. ss.
    rewrite IHl1. nia.
  Qed.

  Lemma long_name_notin l (fn: string)
    (LONG: String.length fn > strings_maxlen l)
    :
    ~ wmask_list l fn.
  Proof.
    ii. eapply existsb_exists in H. des. eapply String.eqb_eq in H0; subst.
    revert_until l. induction l; i; ss.
    des; subst.
    - rewrite /strings_maxlen in LONG. ss. nia.
    - eapply IHl; et. unfold strings_maxlen in *. ss. nia.
  Qed.

  Lemma sch_pure_elim_filter msk u sp_s:
    ctx_refines
      (SchAPure.t u sp_s, emp%I)
      (CFilter.filter msk (SchAPure.t u sp_s), emp%I).
  Proof.
    eapply main_adequacy with (Ist := fun _ _ _ => emp%I).
    init_sim; et.
    init_simF u u.

    steps_l. forces_r. iSplitL "ASM"; et.
    steps_r. forces_l. iSplitL "GRT"; et.
    step; et.
  Qed.

  Lemma helping_on_wf jobID (jobs: jobID -> _) mn sp:
    HMod.wf (HelpingOn.t mn jobs sp).
  Proof.
    unfold_hmod. econs; prove_nodup.
  Qed.

  Theorem helping_main {mA mM mI P1 P2} imp jobID (jobs: jobID -> _) u sp sp_s sp_u
    (UserInSp: sp_sub sp_u sp_s)
    (SchInSp : sp_incl (SchAS.sp u sp_u) sp_s)
    (MAIN  : ∀ mn msk
                (DISJ: ∀ fn, In fn (Helping.exports mn) → In fn imp → False)
                (SUB: wmask_sub (wmask_list imp) msk),
        ctx_refines
          (mM mn ★                 (HelpingOn.t mn jobs sp) ★ (SchAPure.t u sp_s) ★ CFilter.filter msk (SchA.t u sp_s sp_u), P1)
          (CFilter.filter msk mI ★ (HelpingOn.t mn jobs sp) ★ (SchAPure.t u sp_s) ★ CFilter.filter msk (SchA.t u sp_s sp_u), emp%I))
    (CANCEL: ∀ mn msk
                (DISJ: ∀ fn, In fn (Helping.exports mn) → In fn imp → False)
                (SUB: wmask_sub (wmask_list imp) msk),
        ctx_refines
          (mA                                ★ (SchAPure.t u sp_s) ★ CFilter.filter msk (SchA.t u sp_s sp_u), P2)
          (mM mn ★ (HelpingOff.t mn jobs sp) ★ (SchAPure.t u sp_s) ★ CFilter.filter msk (SchA.t u sp_s sp_u), emp%I))
    :
    ctx_refines
      (mA ★ (SchAPure.t u sp_s) ★ (SchA.t u sp_s sp_u), (P1 ∗ P2)%I)
      (mI ★ (SchAPure.t u sp_s) ★ (SchA.t u sp_s sp_u), emp%I).
  Proof.
    r. i. s. destruct ctx as [ctx P]. s.
    etrans; [ctxr_refl|].
    etrans; [|ctxr_refl].

    match goal with [|-refines (?src,?P1) (?tgt,?P2)] =>
      pose (md_src := src);
      pose (md_tgt := tgt);
      pose (all_names := imp ++ HMod.exports md_src ++ HMod.exports md_tgt
                           ++ HMod.scopes md_src ++ HMod.scopes md_tgt);
      cut(List.NoDup (HMod.scopes tgt) -> refines (src,P1) (tgt,P2))
    end.
    { ii. eapply H; et. destruct WFM. et. }
    intros NODUP.

    etrans; cycle 1.
    { eapply ctxr_refines.
      eapply CFilter.intro_filter.
    }

    pose (mn := mname_long (10 + strings_maxlen all_names)).
    pose (mask := wmask_list all_names).

    assert (DISJ: ∀ fn, In fn (Helping.exports mn) → In fn imp → False).
    {
      ii. eapply (long_name_notin _ fn); cycle 1.
      * unfold wmask_list. eapply existsb_exists.
        esplits; [apply H0|apply String.eqb_eq]; et.
      * s in H. des; ss; subst.
        { subst mn. s. fold append.
          rewrite !strings_maxlen_app !string_length_app.
          rewrite mname_long_length. nia.
        }
        { subst mn. s. fold append.
          rewrite !strings_maxlen_app !string_length_app.
          rewrite mname_long_length. nia.
        }
    }

    assert(SUB: wmask_sub (wmask_list imp) mask).
    {
      unfold mask, wmask_sub, wmask_list.
      i. eapply existsb_exists in H. des.
      eapply existsb_exists. esplits; et.
      eapply in_or_app; et.
    }

    etrans; cycle 1.
    { eapply CFilter.intro_module
        with (mask:= mask) (mc := HelpingOn.t mn jobs sp); et.
      - eapply helping_on_wf.
      - i. r. rewrite existsb_exists.
        esplits; try apply String.eqb_eq; eauto.
        do 2 (eapply in_or_app; right).
        eapply in_or_app; et.
      - intros fn IN.
        split; cycle 1.
        { revert IN. unfold_hmod. s. i. des; subst; ss. }
        eapply long_name_notin.
        revert IN. s. unfold_hmod. s. i. des; subst; try by ss.
        + simpl String.length. fold append.
          rewrite !strings_maxlen_app !string_length_app mname_long_length.
          nia.
        + simpl String.length. fold append.
          rewrite !strings_maxlen_app !string_length_app mname_long_length.
          nia.
      - eapply List.NoDup_app; et.
        + unfold_hmod. econs; ss. econs.
        + ii. eapply (long_name_notin _ a); cycle 1.
          * unfold wmask_list. eapply existsb_exists.
            esplits; [apply H|apply String.eqb_eq]; et.
          * revert H0; unfold_hmod. i. rr in H0. des; ss; subst.
            unfold mn. rewrite !strings_maxlen_app. s.
            rewrite mname_long_length. nia.
    }
    rewrite !CFilter.filter_app.
    
    etrans; cycle 1.
    {
      eapply ctxr_refines.
      do 2 ctxr_rotate. do 4 ctxr_drop.
      eapply sch_pure_elim_filter.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      ctxr_rotate. ctxr_drop. ctxr_swap.
      eapply MAIN; et.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      do 2 ctxr_drop.
      eapply helping_onoff_correct; et.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      ctxr_drop.
      eapply CANCEL; et.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      do 2 ctxr_rotate. do 3 ctxr_drop. eapply CFilter.intro_filter.
    }

    etrans; cycle 1.
    {
      eapply ctxr_refines.
      ctxr_rotate. do 3 ctxr_drop. eapply CFilter.intro_filter.
    }

    etrans; cycle 1.
    { eapply ctxr_refines. do 2 ctxr_rotate. ctxr_refl. }
    
    erewrite <-!CFilter.filter_app.
    etrans; [|eapply CFilter.elim_filter]; cycle 1.
    { i. unfold mask, wmask_list. eapply existsb_exists.
      esplits; [|eapply String.eqb_eq]; et.
      eapply in_or_app; right.
      eapply in_or_app; et.
    }

    eapply ctxr_refines.
    eapply ctxr_cond_strengthen.
    iIntros "[[P1 P2] P]". iFrame.
  Qed.

End Helping.  

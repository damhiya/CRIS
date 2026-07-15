From CRIS.common Require Import CRIS.
From CRIS.modules Require Import LMod.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From CRIS.helping Require Export HelpingOn HelpingOff.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Section props.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

  Lemma option_Assume_sred sp N :
    ⇓smod(sp) (option_Assume N) = option_Assume N.
  Proof using.
    rewrite /option_Assume; case_match; rewrite ?SRed.ret; auto.
    etrans; first hnorm_itr. symmetry; etrans; first hnorm_itr. grind. rewrite SRed.ret //.
  Qed.

  Lemma option_Guarantee_sred sp N :
    ⇓smod(sp) (option_Guarantee N) = option_Guarantee N.
  Proof using.
    rewrite /option_Guarantee; case_match; rewrite ?SRed.ret; auto.
    etrans; first hnorm_itr. symmetry; etrans; first hnorm_itr. grind. rewrite SRed.ret //.
  Qed.

  Lemma gsim_option_Guarantee_both (N : option namespace)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp k_s k_t (res : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Guarantee N);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Guarantee N);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct N as [N | ]; cycle 1.
    { ss; rewrite SBRed.ret ?bind_ret_l in Hin_s, Hin_t.
      specialize (Hk res Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Guarantee_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    intros res2 Hres2. ghcNormT.
    eapply gsim_Guarantee_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    exists res2; splits; try by des. ghcNormS.
    eapply gsim_flag; last eapply (Hk res2).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_option_Assume_both (N : option namespace)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp k_s k_t (res : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Assume N);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Assume N);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct N as [N | ]; cycle 1.
    { ss; rewrite SBRed.ret ?bind_ret_l in Hin_s, Hin_t.
      specialize (Hk res Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Assume_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    intros res2 Hres2. ghcNormS.
    eapply gsim_Assume_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    exists res2; splits; try by des. ghcNormT.
    eapply gsim_flag; last eapply (Hk res2).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_jobs_both
      (job : itree crisE (SAny.t + SAny.t))
      r g RR st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      sp k_s k_t (res : Σ) mn :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ) (ret : SAny.t + SAny.t), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s ret)]> tp_s))
          (st_s, (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t ret)]> tp_t))
          (st_t, (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT * Any.t)%type (lstateT * Any.t)%type RR smj_bot smj_bot
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true) (⇓smod(sp) (⇓sb(msk_pure) job));; k_s x)]>
        tp_s)) (st_s, (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (⇓smod(sp) (⇓sb(msk_pure) job));; k_t x)]>
        tp_t)) (st_t, (res↑))).
  Proof using.
    intros Hlen_s Hlen_t Hres Hk.
    revert Hres Hk; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres Hk.
    ides job.
    { ghcNormS; ghcNormT.
      eapply gpaco7_mon; eauto.
    }
    {
      eapply gsim_tau_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_tau_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      zprogress with smj_bot smj_bot _ _. gbase. eauto.
    }
    destruct e as [e|e]; rewrite !vis_trigger.
    { destruct e as [P|res1|P].
      { eapply gsim_Assume_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res1 Hres1; rewrite list_insert_insert.
        eapply gsim_Assume_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res1; splits; (try by des); rewrite list_insert_insert.
        ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros ?; rewrite list_insert_insert.
        eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        splits; (try by des); rewrite list_insert_insert.
        ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res1 Hres1; rewrite list_insert_insert.
        eapply gsim_Guarantee_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res1; splits; (try by des); rewrite list_insert_insert.
        ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
    }
    destruct e as [e|e].
    { destruct e as [fn args|fn args|tid|]; ghcNormS;
        try by (eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|]).
    }
    destruct e as [e|e].
    { ghcNormS. ghcNormS.
      eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      ss.
    }
    destruct e as [X|X|I O fn args]; rewrite -!subevent_right !subevent_subevent.
    { eapply gsim_Choose_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghcNormS; ghcNormT.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghcNormS; ghcNormT.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { giter_s; giter_t.
      rewrite /= ?list_lookup_insert //=. gcNormS; gcNormT.
      gstep_s. instantiate (1:=smj_top).
      intros ? ? <-. gsteps_s; gsteps_t. rewrite ?list_insert_insert. ired.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
  Qed.
End props.

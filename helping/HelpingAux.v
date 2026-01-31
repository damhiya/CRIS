Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics GSimAux.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Section props.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  Lemma HoareCall_prologue_sred sp fsp arg :
    ⇓smod(sp) (HoareCall_prologue fsp arg) = HoareCall_prologue fsp arg.
  Proof using.
    rewrite /HoareCall_prologue; destruct fsp as [fsp | ].
    { do 3 (etrans; first hnorm_itr; grind).
      rewrite SRed.ret //.
    }
    rewrite SRed.ret //.
  Qed.

  Lemma HoareCall_epilogue_sred sp fsp x arg :
    ⇓smod(sp) (HoareCall_epilogue fsp x arg) = HoareCall_epilogue fsp x arg.
  Proof using.
    rewrite /HoareCall_prologue; destruct fsp as [? | ].
    { do 3 (etrans; first hnorm_itr; grind).
      rewrite SRed.ret //.
    }
    rewrite SRed.ret //.
  Qed.

  Lemma HoareFun_prologue_sred sp fsp arg :
    ⇓smod(sp) (HoareFun_prologue fsp arg) = HoareFun_prologue fsp arg.
  Proof using.
    rewrite /HoareCall_prologue; destruct fsp as [? | ].
    { do 4 (etrans; first hnorm_itr; grind).
      rewrite SRed.ret //.
    }
    rewrite SRed.ret //.
  Qed.

  Lemma HoareFun_epilogue_sred sp fsp x arg :
    ⇓smod(sp) (HoareFun_epilogue fsp x arg) = HoareFun_epilogue fsp x arg.
  Proof using.
    rewrite /HoareCall_prologue; destruct fsp as [? | ].
    { do 3 (etrans; first hnorm_itr; grind).
      rewrite SRed.ret //.
    }
    rewrite SRed.ret //.
  Qed.

  Lemma gsim_HoareCall_prologue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp fsp k_s k_t (res : Σ) arg :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_prologue fsp arg);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_prologue fsp arg);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s x)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t x)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_prologue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [fsp | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res (tt, arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Choose_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. intros x.
    eapply gsim_Choose_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros varg. rewrite list_insert_insert. gnorm_r.
    eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite list_insert_insert. ghnorm_r.
    eapply gsim_Choose_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. exists x.
    eapply gsim_Choose_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists varg. rewrite list_insert_insert. ghnorm_l.
    eapply gsim_Guarantee_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l.
    eapply gsim_flag; last eapply (Hk res2 (x, varg)).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_HoareCall_epilogue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp k_s k_t (res : Σ) fsp x arg :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_epilogue fsp x arg);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_epilogue fsp x arg);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s x)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t x)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_epilogue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [? | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res (arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Take_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. intros varg.
    eapply gsim_Take_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. exists varg.
    eapply gsim_Assume_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite list_insert_insert. gnorm_l.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l; ghnorm_r.
    eapply gsim_flag; last eapply (Hk res2 (varg)).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_HoareCall_epilogue_HoareFun_prologue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp fsp k_s k_t (res : Σ) x pret :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_epilogue fsp x pret);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareFun_prologue fsp pret);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s ret)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t (x, ret))]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_epilogue /HoareFun_prologue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [fsp | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
      destruct x; ss.
    }
    eapply gsim_Take_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. intros vret.
    eapply gsim_Take_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. exists x.
    eapply gsim_Take_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|]. exists vret.
    eapply gsim_Assume_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite !list_insert_insert. gnorm_l.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l; ghnorm_r.
    eapply gsim_flag; last eapply (Hk res2).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_HoareCall_prologue_HoareFun_epilogue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp fsp k_s k_t (res : Σ) x pret :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_prologue fsp pret);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareFun_epilogue fsp x pret);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s (x, ret))]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t ret)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_prologue /HoareFun_epilogue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [fsp | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
      destruct x; ss.
    }
    eapply gsim_Choose_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. exists x.
    eapply gsim_Choose_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. intros vret.
    eapply gsim_Choose_src; [lookup_tac; do 2 f_equal; hnorm_itr|]. exists vret.
    eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite !list_insert_insert. gnorm_r.
    eapply gsim_Guarantee_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l; ghnorm_r.
    eapply gsim_flag; last eapply (Hk res2).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_jobs_both {retID} r g RR st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      sp k_s k_t (res : Σ) job mn :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ) (ret : retID), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s :=
            ⇓cris (k_s ret)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t :=
            ⇓cris (k_t ret)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true) (⇓smod(sp) (⇓sb(HelpingOn.msk_pure) job));; k_s x)]>
        tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (⇓smod(sp) (⇓sb(HelpingOn.msk_pure) job));; k_t x)]>
        tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hlen_s Hlen_t Hres Hk.
    revert Hres Hk; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres Hk.
    ides job.
    { ghnorm_l; ghnorm_r.
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
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros ?; rewrite list_insert_insert.
        eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        splits; (try by des); rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res1 Hres1; rewrite list_insert_insert.
        eapply gsim_Guarantee_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res1; splits; (try by des); rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
    }
    destruct e as [e|e].
    { ghnorm_l. ghnorm_l.
      eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      ss.
    }
    destruct e as [e|e].
    { ghnorm_l. ghnorm_l.
      eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      ss.
    }
    destruct e as [X|X|I O fn args]; rewrite -!subevent_right !subevent_subevent.
    { eapply gsim_Choose_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghnorm_l; ghnorm_r.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghnorm_l; ghnorm_r.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { giter_l; giter_r.
      rewrite /= ?list_lookup_insert //=. gnorm_l; gnorm_r.
      gstep_l. instantiate (1:=smj_top).
      intros ? ? <-. gsteps_l; gsteps_r. rewrite ?list_insert_insert. ired.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
  Qed.
End props.

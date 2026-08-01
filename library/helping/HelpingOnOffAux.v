From CRIS.common Require Import CRIS.
From CRIS.modules Require Import LMod.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From CRIS.helping Require Export HelpingAux.

Section props.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

  Lemma gsim_Guarantee_both_view (Priv : iProp Σ) (P : iProp Σ)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      k_s k_t (res_t res_s : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- trigger (Guarantee P);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- trigger (Guarantee P);; k_t x)) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (∀ (res_t1 res_s1 : Σ), ✓ res_s1 →
      (Own res_s1 ⊢ |==> Own res_t1 ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, res_s1))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, res_t1))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, res_t)).
  Proof using.
    intros Hin_s Hin_t Hres Hview Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    eapply gsim_Guarantee_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    intros res_t1 [Hres_t1 Hupd].
    eassert (Hsrc : Own res_s ⊢ |==>
      P ∗ (Own res_t1 ∗ Priv)).
    { iIntros "Hrs".
      iMod (Hview with "Hrs") as "[Hrt Hpriv]".
      iMod (Hupd with "Hrt") as "[HP Hrt]".
      iModIntro. iFrame.
    }
    eapply Own_bupd_split in Hsrc as
      [res_p [res_s1 [Hsplit [Hres_p Hview1]]]]; auto.
    assert (Hres_s1 : ✓ res_s1).
    { eapply (Own_wand_valid res_s); [|exact Hres].
      rewrite Hsplit. iIntros "> [_ $]".
      done.
    }
    eapply gsim_Guarantee_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    exists res_s1; splits; eauto.
    { rewrite Hsplit Hres_p //. }
    ghcNormS; ghcNormT.
    eapply (Hk res_t1 res_s1); first exact Hres_s1.
    rewrite Hview1. apply bupd_intro.
  Qed.

  Lemma gsim_Assume_both_view (Priv : iProp Σ) (P : iProp Σ)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      k_s k_t (res_t res_s : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- trigger (Assume P);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- trigger (Assume P);; k_t x)) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (∀ (res_t1 res_s1 : Σ), ✓ res_s1 →
      (Own res_s1 ⊢ |==> Own res_t1 ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, res_s1))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, res_t1))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, res_t)).
  Proof using.
    intros Hin_s Hin_t Hres Hview Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    eapply gsim_Assume_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    intros res_s1 [Hres_s1 Hupd].
    eapply Own_bupd_split in Hupd as
      [res_p [res_f [Hsplit [Hres_p Hres_f]]]]; auto.
    assert (Hres_t1 : ✓ (res_t ⋅ res_p)).
    { eapply (Own_wand_valid res_s1); [|exact Hres_s1].
      iIntros "Hrs".
      iMod (Hsplit with "Hrs") as "[Hp Hf]".
      iPoseProof (Hres_f with "Hf") as "Hrs".
      iMod (Hview with "Hrs") as "[Ht Hpriv]".
      iModIntro. rewrite Own_op. iFrame.
    }
    eapply gsim_Assume_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    exists (res_t ⋅ res_p); splits; first done.
    { rewrite Own_op. iIntros "[Ht Hp]". iModIntro.
      iSplitL "Hp"; [iApply Hres_p|]; done.
    }
    ghcNormS; ghcNormT.
    eapply (Hk (res_t ⋅ res_p) res_s1); first exact Hres_s1.
    iIntros "Hrs".
    iMod (Hsplit with "Hrs") as "[Hp Hf]".
    iPoseProof (Hres_f with "Hf") as "Hrs".
    iMod (Hview with "Hrs") as "[Ht Hpriv]".
    iModIntro. rewrite Own_op. iFrame.
  Qed.

  Lemma gsim_AssumeRes_both_view (Priv : iProp Σ) (x : Σ)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      k_s k_t (res_t res_s : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (y <- trigger (AssumeRes x);; k_s y)) →
    tp_t !! tid_t =
      Some (⇓cris (y <- trigger (AssumeRes x);; k_t y)) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (✓ (x ⋅ res_s) →
      (Own (x ⋅ res_s) ⊢ |==> Own (x ⋅ res_t) ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, x ⋅ res_s))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, x ⋅ res_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, res_t)).
  Proof using.
    intros Hin_s Hin_t Hres Hview Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    eapply gsim_AssumeRes_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    intros Hres1.
    assert (Hview1 : Own (x ⋅ res_s) ⊢ |==> Own (x ⋅ res_t) ∗ Priv).
    { rewrite !Own_op. iIntros "[Hx Hrs]".
      iMod (Hview with "Hrs") as "[Hrt Hpriv]".
      iModIntro. iFrame.
    }
    assert (Hres_t1 : ✓ (x ⋅ res_t)).
    { eapply (Own_wand_valid (x ⋅ res_s)); [|exact Hres1].
      iIntros "Hrs". iMod (Hview1 with "Hrs") as "[$ _]". done.
    }
    eapply gsim_AssumeRes_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    split; first exact Hres_t1.
    ghcNormS; ghcNormT.
    exact (Hk Hres1 Hview1).
  Qed.

  Lemma gsim_option_Guarantee_both_view (Priv : iProp Σ) (N : option namespace)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp k_s k_t (res_t res_s : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Guarantee N);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Guarantee N);; k_t x)) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (∀ (res_t1 res_s1 : Σ), ✓ res_s1 →
      (Own res_s1 ⊢ |==> Own res_t1 ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, res_s1))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, res_t1))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, res_t)).
  Proof using.
    intros Hin_s Hin_t Hres Hview Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct N as [N | ]; cycle 1.
    { ss; rewrite SBRed.ret ?bind_ret_l in Hin_s, Hin_t.
      specialize (Hk res_t res_s Hres Hview); revert Hk.
      rewrite ?list_insert_id //=.
    }
    eapply gsim_Guarantee_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    intros res_t1 [Hres_t1 Hupd].
    eassert (Hsrc : Own res_s ⊢ |==>
      winv (↑N, ↑N) ∗ (Own res_t1 ∗ Priv)).
    { iIntros "Hrs".
      iMod (Hview with "Hrs") as "[Hrt Hpriv]".
      iMod (Hupd with "Hrt") as "[Hwinv Hrt]".
      iModIntro. iFrame.
    }
    eapply Own_bupd_split in Hsrc as
      [res_p [res_s1 [Hsplit [Hres_p Hview1]]]]; auto.
    assert (Hres_s1 : ✓ res_s1).
    { eapply (Own_wand_valid res_s); [|exact Hres].
      rewrite Hsplit. iIntros "> [_ $]".
      done.
    }
    eapply gsim_Guarantee_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    exists res_s1; splits; eauto.
    { rewrite Hsplit Hres_p //. }
    ghcNormS; ghcNormT.
    eapply gsim_flag; last eapply (Hk res_t1 res_s1); et.
    - destruct p_s; rr; ss; eauto.
    - destruct p_t; rr; ss; eauto.
    - rewrite Hview1. apply bupd_intro.
  Qed.

  Lemma gsim_option_Assume_both_view (Priv : iProp Σ) (N : option namespace)
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp k_s k_t (res_t res_s : Σ) :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Assume N);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (option_Assume N);; k_t x)) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (∀ (res_t1 res_s1 : Σ), ✓ res_s1 →
      (Own res_s1 ⊢ |==> Own res_t1 ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s tt)]> tp_s))
          (st_s, res_s1))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t tt)]> tp_t))
          (st_t, res_t1))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, res_t)).
  Proof using.
    intros Hin_s Hin_t Hres Hview Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct N as [N | ]; cycle 1.
    { ss; rewrite SBRed.ret ?bind_ret_l in Hin_s, Hin_t.
      specialize (Hk res_t res_s Hres Hview); revert Hk.
      rewrite ?list_insert_id //=.
    }
    eapply gsim_Assume_src; [rewrite Hin_s; do 2 f_equal; s; hnorm_itr|].
    intros res_s1 [Hres_s1 Hupd].
    eapply Own_bupd_split in Hupd as
      [res_p [res_f [Hsplit [Hres_p Hres_f]]]]; auto.
    assert (Hres_t1 : ✓ (res_t ⋅ res_p)).
    { eapply (Own_wand_valid res_s1); [|exact Hres_s1].
      iIntros "Hrs".
      iMod (Hsplit with "Hrs") as "[Hp Hf]".
      iPoseProof (Hres_f with "Hf") as "Hrs".
      iMod (Hview with "Hrs") as "[Ht Hpriv]".
      iModIntro. rewrite Own_op. iFrame.
    }
    eapply gsim_Assume_tgt; [rewrite Hin_t; do 2 f_equal; s; hnorm_itr|].
    exists (res_t ⋅ res_p); splits; first done.
    { rewrite Own_op. iIntros "[Ht Hp]". iModIntro.
      iSplitL "Hp"; [iApply Hres_p|]; done.
    }
    ghcNormS; ghcNormT.
    eapply gsim_flag; last eapply (Hk (res_t ⋅ res_p) res_s1); et.
    - destruct p_s; rr; ss; eauto.
    - destruct p_t; rr; ss; eauto.
    - iIntros "Hrs".
      iMod (Hsplit with "Hrs") as "[Hp Hf]".
      iPoseProof (Hres_f with "Hf") as "Hrs".
      iMod (Hview with "Hrs") as "[Ht Hpriv]".
      iModIntro. rewrite Own_op. iFrame.
  Qed.

  Lemma gsim_jobs_both_view (Priv : iProp Σ)
      (job : itree crisE (SAny.t + SAny.t))
      r g RR st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      sp k_s k_t (res_t res_s : Σ) mn :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    (∀ (res_t1 res_s1 : Σ) (ret : SAny.t + SAny.t),
      ✓ res_s1 →
      (Own res_s1 ⊢ |==> Own res_t1 ∗ Priv) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s ret)]> tp_s))
          (st_s, res_s1))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t ret)]> tp_t))
          (st_t, res_t1))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_bot smj_bot
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true) (⇓smod(sp) (⇓sb(msk_pure) job));; k_s x)]>
        tp_s)) (st_s, res_s))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (⇓smod(sp) (⇓sb(msk_pure) job));; k_t x)]>
        tp_t)) (st_t, res_t)).
  Proof using.
    intros Hlen_s Hlen_t Hres Hview Hk.
    revert Hres Hview Hk; generalize job res_t res_s.
    clear job res_t res_s.
    gcofix CIH.
    intros job res_t res_s Hres Hview Hk.
    ides job.
    { ghcNormS; ghcNormT.
      eapply gpaco7_mon; eauto.
    }
    {
      eapply gsim_tau_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_tau_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      zprogress with smj_bot smj_bot _ _. gbase.
      eapply CIH; eauto.
    }
    destruct e as [e|e]; rewrite !vis_trigger.
    { destruct e as [P|res1|P].
      { eapply gsim_Assume_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res_s1 [Hres_s1 Hupd]. rewrite list_insert_insert.
        eapply Own_bupd_split in Hupd as
          [res_p [res_f [Hsplit [Hres_p Hres_f]]]]; auto.
        assert (Hres_t1 : ✓ (res_t ⋅ res_p)).
        { eapply (Own_wand_valid res_s1); [|exact Hres_s1].
          iIntros "Hrs".
          iMod (Hsplit with "Hrs") as "[Hp Hf]".
          iPoseProof (Hres_f with "Hf") as "Hrs".
          iMod (Hview with "Hrs") as "[Ht Hpriv]".
          iModIntro. rewrite Own_op. iFrame.
        }
        eapply gsim_Assume_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists (res_t ⋅ res_p); splits; first done.
        { rewrite Own_op. iIntros "[Ht Hp]". iModIntro.
          iSplitL "Hp"; [iApply Hres_p|]; done.
        }
        rewrite list_insert_insert. ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase.
        eapply CIH; try done.
        iIntros "Hrs".
        iMod (Hsplit with "Hrs") as "[Hp Hf]".
        iPoseProof (Hres_f with "Hf") as "Hrs".
        iMod (Hview with "Hrs") as "[Ht Hpriv]".
        iModIntro. rewrite Own_op. iFrame.
      }
      { eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros Hres1; rewrite list_insert_insert.
        eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        splits.
        { eapply (Own_wand_valid (res1 ⋅ res_s)); [|exact Hres1].
          rewrite !Own_op. iIntros "[Hres1 Hrs]".
          iMod (Hview with "Hrs") as "[Hrt Hpriv]".
          iModIntro. iFrame.
        }
        rewrite list_insert_insert. ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase.
        eapply CIH; try done.
        rewrite !Own_op. iIntros "[Hres1 Hrs]".
        iMod (Hview with "Hrs") as "[Hrt Hpriv]".
        iModIntro. iFrame.
      }
      { eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res_t1 [Hres_t1 Hupd]. rewrite list_insert_insert.
        eassert (Hsrc : Own res_s ⊢ |==> P ∗ (Own res_t1 ∗ Priv)).
        { iIntros "Hrs".
          iMod (Hview with "Hrs") as "[Hrt Hpriv]".
          iMod (Hupd with "Hrt") as "[HP Hrt]".
          iModIntro. iFrame.
        }
        eapply Own_bupd_split in Hsrc as
          [res_p [res_s1 [Hsplit [Hres_p Hview1]]]]; auto.
        assert (Hres_s1 : ✓ res_s1).
        { eapply (Own_wand_valid res_s); [|exact Hres].
          rewrite Hsplit. iIntros "> [_ $]".
          done.
        }
        eapply gsim_Guarantee_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res_s1; splits; eauto.
        { rewrite Hsplit Hres_p //. }
        rewrite list_insert_insert. ghcNormS; ghcNormT.
        zprogress with smj_bot smj_bot _ _. gbase.
        eapply CIH; try done.
        rewrite Hview1. apply bupd_intro.
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
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; eauto.
    }
    { eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghcNormS; ghcNormT.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; eauto.
    }
    { giter_s; giter_t.
      rewrite /= ?list_lookup_insert //=. gcNormS; gcNormT.
      gstep_s. instantiate (1:=smj_top).
      intros ? ? <-. gsteps_s; gsteps_t. rewrite ?list_insert_insert. ired.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; eauto.
    }
  Qed.
End props.

From CRIS.common Require Import Common ConcRA StatePredicate.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.msim Require Import MSim MSimFacts MSimCommon ISim
  ISimFacts ISimAdequacy TacticsCommon ITactics.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy.

(** This file contains the main lemma of CRIS, namely ISim.t implies ctx_refines. *)

Lemma inv_sandbox_ktr `{Σ : GRA} {X Y} x msk (ktr : _ → itree crisE Y) (e : crisE X) :
  SB.sandbox msk (trigger e >>= ktr) = trigger e >>= ktr →
  SB.sandbox msk (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_event `{Σ : GRA} {X Y} (x: X) msk (ktr : _ → itree crisE Y) (e : crisE X) :
  SB.sandbox msk (trigger e >>= ktr) = trigger e >>= ktr →
  SB.sandbox msk (ktr x) = ktr x ∧ (msk X e ∨ SB.msk_default X e).
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; bsimpl; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_tau `{Σ : GRA} {X} msk (ktr : itree crisE X) :
  (SB.sandbox msk (tau;; ktr) = tau;; ktr) →
  SB.sandbox msk ktr = ktr.
Proof. rewrite SBRed.tau; grind. Qed.

Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto.

Lemma msim_ctx
    `{Σ : GRA} `{!stateGS Σ} (contextual : contextuality)
    (ms mt ctx : Mod.t) (Ist : iProp Σ) {Rs Rt}
    (RR : retr_type Σ Rs Rt) ps pt
    (itr_src : itree crisE Rs) (itr_tgt : itree crisE Rt) (fmr : Σ) :
  Mod.scopes ms ⊆+ Mod.scopes mt →
  SB.sandbox (msk_scp (Mod.scopes mt) msk_true) itr_src = itr_src →
  SB.sandbox (msk_scp (Mod.scopes mt) msk_true) itr_tgt = itr_tgt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  msim open
    (sandbox_fnsemmap (Mod.fnsems ms))
    (sandbox_fnsemmap (Mod.fnsems mt))
    Ist RR ps pt itr_src itr_tgt fmr →
  @msim _ _ contextual
    (sandbox_fnsemmap (Mod.fnsems (ms ★ ctx)))
    (sandbox_fnsemmap (Mod.fnsems (mt ★ ctx)))
    Ist Rs Rt RR ps pt itr_src itr_tgt fmr.
Proof.
  ginit.
  intros Hscopest Hsbs Hsbt Hwfs Hwft.
  move Hwfs at top. move Hwft at top.
  revert_until RR. gcofix CIH.
  intros ps pt itr_src itr_tgt fmr Hscopest Hsbs Hsbt Hsim.
  move Hsim before CIH. revert_until Hsim. punfold Hsim.
  pattern ps, pt, itr_src, itr_tgt, fmr.
  eapply _msim_tarski, Hsim; clear Hsim fmr.
  intros ps0 pt0 itr_src0 itr_tgt0 fmr Hin.
  guclo msim_wfC_spec. econs. intros Hval.
  guclo msim_nodupC_spec; econs; intros Hfs Hft; hexploit Hin; ss.
  { move: Hfs; rewrite ?map_Forall_lookup => Hfs i x; move: Hfs => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ ms !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }
  { move: Hft; rewrite ?map_Forall_lookup => Hft i x; move: Hft => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ mt !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }

  clear Hin; intros Hin.
  destruct Hin as [fmr1 [Hin Hfmr]]; eauto.
  inv Hin; try by (mstep; eauto using inv_sandbox_ktr, inv_sandbox_tau).
  { mstep; cycle 1.
    { eapply K; eauto using inv_sandbox_ktr.
      ired. rewrite SBRed.bind; ired.
      assert (Hf : SB.sandbox (msk_scp (Mod.scopes mt) msk_true) (f varg) = f varg).
      { move: FUN; rewrite lookup_fmap; destruct (_ ms !! _) as [[[fnmsk ?]|]|] eqn : Hfn; ss.
        i; clarify; eapply sandbox_sandbox; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns ms); rewrite map_Forall_lookup =>
          /(_ (funid fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
          [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide as Hin2; ss;
          intros Hin; eapply elem_of_submseteq in Hscopest; eauto.
      }
      rewrite Hf; grind.
      rewrite SBRed.tau; ired; grind; eauto using inv_sandbox_ktr.
    }
    revert FUN; intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move : FUN => /(Mod.lookup_add_l); move /(_ ctx Hwfs) => /=; rewrite lookup_fmap => -> //=.
  }
  { mstep; cycle 1.
    { eapply K; eauto using inv_sandbox_ktr.
      ired. rewrite SBRed.bind; ired.
      assert (Hf : SB.sandbox (msk_scp (Mod.scopes mt) msk_true) (f varg) = f varg).
      { move: FUN; rewrite lookup_fmap; destruct (_ mt !! _) as [[[fnmsk ?]|]|] eqn : Hfn; ss.
        i; clarify; eapply sandbox_sandbox; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns mt); rewrite map_Forall_lookup =>
          /(_ (funid fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
          [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide; ss;
          intros Hin; eapply elem_of_submseteq in Hin; eauto.
      }
      rewrite Hf; grind.
      rewrite SBRed.tau; ired; grind; eauto using inv_sandbox_ktr.
    }
    revert FUN; intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move : FUN => /(Mod.lookup_add_l); move /(_ ctx Hwft) => /=; rewrite lookup_fmap => -> //=.
  }
  { gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; try refl; eauto.
  }
  Unshelve. all: try exact (()↑).
Qed.

Lemma isim_map_ctx `{Σ : GRA} `{!stateGS Σ}
    (contextual : contextuality) (fs ft : emask * fbody)
    (ms mt ctx : Mod.t) (Ist : iProp Σ) (RR : retr_type Σ Any.t Any.t)
    (arg : Any.t) :
  Mod.scopes ms ⊆+ Mod.scopes mt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  (∃ fno, Mod.fnsems ms !! fno = Some (Some fs) ∧
          Mod.fnsems mt !! fno = Some (Some ft)) →
  isim open
    (sandbox_fnsemmap (Mod.fnsems ms))
    (sandbox_fnsemmap (Mod.fnsems mt))
    Ist ibot RR false false
    (SB.sandbox_body fs arg) (SB.sandbox_body ft arg) ⊢
  @isim _ _ contextual
    (sandbox_fnsemmap (Mod.fnsems (ms ★ ctx)))
    (sandbox_fnsemmap (Mod.fnsems (mt ★ ctx)))
    Ist ibot Any.t Any.t RR false false
    (SB.sandbox_body fs arg) (SB.sandbox_body ft arg).
Proof.
  intros Hscp Hwfs Hwft Hin.
  apply entails_pointwise => r _ Hsim.
  eapply isim_init in Hsim; eauto.
  eapply gpaco8_mon in Hsim; try apply iunlift_ibot; eauto.
  eapply gpaco8_init in Hsim; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco; right.
  destruct fs as [msks bds]; destruct ft as [mskt bdt].
  assert (Hsim' :
    @msim _ _ contextual
      (sandbox_fnsemmap (Mod.fnsems (ms ★ ctx)))
      (sandbox_fnsemmap (Mod.fnsems (mt ★ ctx))) Ist
      Any.t Any.t RR false false
      (SB.sandbox_body (msks, bds) arg)
      (SB.sandbox_body (mskt, bdt) arg) r).
  { eapply (msim_ctx contextual ms mt ctx Ist RR); eauto.
    { destruct Hin as [fno [Hins Hint]].
      eapply sandbox_sandbox; ss.
      intros ? s; depdes s; ss; depdes s; ss; depdes s; ss.
      depdes p; ss; hexploit (Mod.well_scoped_fns ms);
        rewrite map_Forall_lookup =>
        /(_ fno (msks, bds)); rewrite lookup_omap Hins => /(_ eq_refl);
        [intros [Hkey ?]|intros [? Hkey]] => /Hkey;
        case_decide as Hin2; ss;
        intros Hin; eapply elem_of_submseteq in Hscp; eauto.
    }
    { destruct Hin as [fno [Hins Hint]].
      eapply sandbox_sandbox; ss.
      intros ? s; depdes s; ss; depdes s; ss; depdes s; ss.
      depdes p; ss; hexploit (Mod.well_scoped_fns mt);
        rewrite map_Forall_lookup =>
        /(_ fno (mskt, bdt)); rewrite lookup_omap Hint => /(_ eq_refl);
        [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide; ss;
        intros Hin; eapply elem_of_submseteq in Hin; eauto.
    }
  }
  eapply paco8_mon_bot.
  - exact Hsim'.
  - intros; assumption.
Qed.

Lemma isim_ctx `{Σ : GRA} `{!stateGS Σ}
    (contextual : contextuality) fs ft ms mt ctx Ist CtxIst arg :
  Mod.scopes ms ⊆+ Mod.scopes mt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  (∃ fno, Mod.fnsems ms !! fno = Some (Some fs) ∧ Mod.fnsems mt !! fno = Some (Some ft)) →
  CtxIst ∗ isim open
    (sandbox_fnsemmap (Mod.fnsems ms))
    (sandbox_fnsemmap (Mod.fnsems mt))
    Ist ibot (ist_with_eq Ist) false false
    (SB.sandbox_body fs arg) (SB.sandbox_body ft arg) ⊢
  @isim _ _ contextual
    (sandbox_fnsemmap (Mod.fnsems (ms ★ ctx)))
    (sandbox_fnsemmap (Mod.fnsems (mt ★ ctx)))
    (CtxIst ∗ Ist)%I ibot Any.t Any.t (ist_with_eq (CtxIst ∗ Ist)%I)
    false false (SB.sandbox_body fs arg) (SB.sandbox_body ft arg).
Proof.
  intros Hscp Hwfs Hwft Hin.
  iIntros "[CTX SIM]".
  iCombine "CTX SIM" as "SIM".
  iPoseProof (isim_ist_frame with "SIM") as "SIM".
  iApply (isim_mono contextual
    (sandbox_fnsemmap (Mod.fnsems (ms ★ ctx)))
    (sandbox_fnsemmap (Mod.fnsems (mt ★ ctx)))
    (CtxIst ∗ Ist)%I ibot false false
    (λ x y, (CtxIst ∗ ist_with_eq Ist x y)%I)
    (ist_with_eq (CtxIst ∗ Ist)%I)
    (SB.sandbox_body fs arg) (SB.sandbox_body ft arg)).
  - iIntros (vsrc vtgt) "[CTX [-> IST]]".
    iFrame. done.
  - iApply isim_map_ctx; eauto.
Qed.

Local Lemma mod_add_scope_set `{Σ : GRA} (m1 m2 : Mod.t) :
  (list_to_set (Mod.scopes (m1 ★ m2)) : gset string) =
    list_to_set (Mod.scopes m1) ∪ list_to_set (Mod.scopes m2).
Proof.
  apply set_eq. intros scope.
  rewrite elem_of_list_to_set elem_of_union /=.
  rewrite sorting.merge_sort_Permutation elem_of_app.
  by rewrite !elem_of_list_to_set.
Qed.

Local Lemma mod_add_scope_disjoint `{Σ : GRA} (m1 m2 : Mod.t)
    (WF : Mod.wf (m1 ★ m2)) :
  (list_to_set (Mod.scopes m1) : gset string) ##
    list_to_set (Mod.scopes m2).
Proof.
  intros scope IN1 IN2.
  rewrite !elem_of_list_to_set in IN1, IN2.
  pose proof (Mod.wf_scopes _ WF) as ND.
  rewrite /= sorting.merge_sort_Permutation NoDup_app in ND.
  destruct ND as [_ [DISJ _]]. exact (DISJ scope IN1 IN2).
Qed.

Local Lemma state_slice_union_with_l
    (S1 S2 : gset string) (m1 m2 : gmap key (option Any.t))
    (SCOPED2 : set_map fst (dom m2) ⊆ S2) (DISJ : S1 ## S2) :
  state_slice S1 (union_with uwnd m1 m2) = state_slice S1 m1.
Proof.
  apply map_eq. intros k. rewrite !state_slice_lookup.
  destruct (decide (k.1 ∈ S1)) as [IN|NIN]; last done.
  rewrite lookup_union_with.
  destruct (m2 !! k) eqn:LOOK2; last by destruct (m1 !! k).
  exfalso. apply elem_of_dom_2 in LOOK2.
  apply (DISJ k.1 IN), SCOPED2.
  apply elem_of_map. exists k. done.
Qed.

Local Lemma state_slice_union_with_r
    (S1 S2 : gset string) (m1 m2 : gmap key (option Any.t))
    (SCOPED1 : set_map fst (dom m1) ⊆ S1) (DISJ : S1 ## S2) :
  state_slice S2 (union_with uwnd m1 m2) = state_slice S2 m2.
Proof.
  apply map_eq. intros k. rewrite !state_slice_lookup.
  destruct (decide (k.1 ∈ S2)) as [IN|NIN]; last done.
  rewrite lookup_union_with.
  destruct (m1 !! k) eqn:LOOK1; last by destruct (m2 !! k).
  exfalso. apply elem_of_dom_2 in LOOK1.
  apply (DISJ k.1).
  - apply SCOPED1, elem_of_map. exists k. done.
  - exact IN.
Qed.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_ctx_with (contextual : contextuality) (ms mt ctx : Mod.t)
      (Ist CtxIst : stateGS Σ → iProp Σ) :
    (∀ STATE,
      state_init_src (list_to_set (Mod.scopes ctx))
        (Mod.initial_st ctx) STATE -∗
      state_init_tgt (list_to_set (Mod.scopes ctx))
        (Mod.initial_st ctx) STATE -∗
      CtxIst STATE) →
    (∀ STATE k v', k.1 ∈ Mod.scopes ctx →
      CtxIst STATE ⊢
        ∃ ov, @state_cell_src Σ STATE k ov ∗
             @state_cell_tgt Σ STATE k ov ∗
             ((@points_to_src Σ STATE k v' ∗
               @points_to_tgt Σ STATE k v') -∗ CtxIst STATE)) →
    (∀ STATE k, k.1 ∈ Mod.scopes ctx →
      CtxIst STATE ⊢
        ∃ ov, @state_cell_src Σ STATE k ov ∗
             @state_cell_tgt Σ STATE k ov ∗
             ((@state_cell_src Σ STATE k ov ∗
               @state_cell_tgt Σ STATE k ov) -∗ CtxIst STATE)) →
    ISim.t open ms mt Ist ⊢
    ISim.t contextual (ms ★ ctx) (mt ★ ctx)
      (λ STATE, (CtxIst STATE ∗ Ist STATE)%I).
  Proof.
    intros HCTXINIT HCTXPUT HCTXGET.
    apply entails_pointwise => r VALID SIM.
    assert (DOM : Mod.wf mt →
      dom (Mod.fnsems ms) ⊆ dom (Mod.fnsems mt)).
    { intros WFT. eapply Own_pure_soundness; et.
      rewrite SIM. iIntros "SIM".
      iPoseProof (ISim_dom with "SIM") as "DOM".
      iApply "DOM". done. }
    rewrite SIM /ISim.t.
    iIntros "SIM %Hwftctx".
    hexploit Mod.add_wf_inv; eauto.
    intros [Hwft [Hwfctx [Hdom Hnd]]].
    iSpecialize ("SIM" with "[]"); first done.
    iDestruct "SIM" as "[[%Hscp %Hnodup] SIM]".
    assert (Hwfs : Mod.wf ms).
    { econs; et.
      eapply submseteq_NoDup; et. apply Hwft. }
    assert (Hwfsctx : Mod.wf (ms ★ ctx)).
    { apply Mod.add_wf; eauto.
      { intros i His Htctx; eapply DOM in His; eauto. }
      { destruct (submseteq_Permutation _ _ Hscp) as [rest temp].
        rewrite temp comm assoc NoDup_app in Hnd; des; rewrite comm //.
      }
    }
    pose (Sms := (list_to_set (Mod.scopes ms) : gset string)).
    pose (Smt := (list_to_set (Mod.scopes mt) : gset string)).
    pose (Sctx := (list_to_set (Mod.scopes ctx) : gset string)).
    assert (SDISJS : Sms ## Sctx).
    { apply mod_add_scope_disjoint. exact Hwfsctx. }
    assert (SDISJT : Smt ## Sctx).
    { apply mod_add_scope_disjoint. exact Hwftctx. }
    assert (SLICE_SRC_M :
      state_slice Sms (Mod.initial_st (ms ★ ctx)) =
        state_slice Sms (Mod.initial_st ms)).
    { apply state_slice_union_with_l with (S2 := Sctx).
      - apply Mod.well_scoped_init.
      - exact SDISJS. }
    assert (SLICE_SRC_CTX :
      state_slice Sctx (Mod.initial_st (ms ★ ctx)) =
        state_slice Sctx (Mod.initial_st ctx)).
    { apply state_slice_union_with_r with (S1 := Sms).
      - apply Mod.well_scoped_init.
      - exact SDISJS. }
    assert (SLICE_TGT_M :
      state_slice Smt (Mod.initial_st (mt ★ ctx)) =
        state_slice Smt (Mod.initial_st mt)).
    { apply state_slice_union_with_l with (S2 := Sctx).
      - apply Mod.well_scoped_init.
      - exact SDISJT. }
    assert (SLICE_TGT_CTX :
      state_slice Sctx (Mod.initial_st (mt ★ ctx)) =
        state_slice Sctx (Mod.initial_st ctx)).
    { apply state_slice_union_with_r with (S1 := Smt).
      - apply Mod.well_scoped_init.
      - exact SDISJT. }
    iSplit.
    { iPureIntro. split.
      - rewrite /= !sorting.merge_sort_Permutation.
        eapply submseteq_app; eauto.
      - apply Hwfsctx.
    }
    iIntros (STATE).
    iSpecialize ("SIM" $! STATE).
    iDestruct "SIM" as "[Hic #Hsimfun]".
    iSplit.
    { iIntros "SRC TGT".
      iEval (rewrite (mod_add_scope_set ms ctx)) in "SRC".
      iEval (rewrite (mod_add_scope_set mt ctx)) in "TGT".
      iPoseProof (state_init_src_union Sms Sctx
        (Mod.initial_st (ms ★ ctx)) SDISJS with "SRC") as
        "[SRCM SRCC]".
      iPoseProof (state_init_tgt_union Smt Sctx
        (Mod.initial_st (mt ★ ctx)) SDISJT with "TGT") as
        "[TGTM TGTC]".
      iPoseProof (state_init_src_ext Sms (Mod.initial_st (ms ★ ctx))
        (Mod.initial_st ms) SLICE_SRC_M with "SRCM") as "SRCM".
      iPoseProof (state_init_src_ext Sctx (Mod.initial_st (ms ★ ctx))
        (Mod.initial_st ctx) SLICE_SRC_CTX with "SRCC") as "SRCC".
      iPoseProof (state_init_tgt_ext Smt (Mod.initial_st (mt ★ ctx))
        (Mod.initial_st mt) SLICE_TGT_M with "TGTM") as "TGTM".
      iPoseProof (state_init_tgt_ext Sctx (Mod.initial_st (mt ★ ctx))
        (Mod.initial_st ctx) SLICE_TGT_CTX with "TGTC") as "TGTC".
      iSplitL "SRCC TGTC".
      - iApply (HCTXINIT STATE with "SRCC TGTC").
      - iApply ("Hic" with "SRCM TGTM").
    }
    iIntros (fno). rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT" (fs) "%Hsrc".
    rewrite lookup_fmap /= lookup_union_with in Hsrc.
    destruct (Mod.fnsems ms !! fno)
      as [[[fmsk fbd]|]|] eqn:Hfnoms; ss.
    { destruct (Mod.fnsems ctx !! fno) as [ctxf|] eqn:Hctx; ss;
        clarify.
      iEval (rewrite /ISim.sim_fun) in "Hsimfun".
      iSpecialize ("Hsimfun" $! fno with "[] []").
      { done. }
      { done. }
      iSpecialize ("Hsimfun" $! (SB.sandbox_body (fmsk, fbd))
        with "[]").
      { iPureIntro.
        rewrite /sandbox_fnsemmap lookup_fmap Hfnoms //. }
      iDestruct "Hsimfun" as (ft) "[%Hft #Hfsem]".
      rewrite /sandbox_fnsemmap lookup_fmap in Hft.
      destruct (Mod.fnsems mt !! fno)
        as [[[fmskt fbdt]|]|] eqn:Hfnomt; ss; clarify.
      iExists (SB.sandbox_body (fmskt, fbdt)). iSplit.
      { iPureIntro.
        rewrite /sandbox_fnsemmap lookup_fmap /= lookup_union_with
          Hfnomt Hctx //. }
      rewrite /isim_fsem.
      iIntros "!#" (arg) "[CTX IST] W".
      iApply (@isim_ctx Σ STATE contextual (fmsk, fbd) (fmskt, fbdt)
        ms mt ctx (Ist STATE) (CtxIst STATE) arg); eauto.
      iFrame "CTX".
      iEval (rewrite /isim_fsem) in "Hfsem".
      iApply ("Hfsem" $! arg with "IST W").
    }
    { exfalso. eapply Hwfs in Hfnoms. rr in Hfnoms. des; ss. }

    destruct (Mod.fnsems ctx !! fno)
      as [[[fmsk fbd]|]|] eqn:Hfnoctx; ss.
    clarify.
    destruct (Mod.fnsems mt !! fno) eqn:Hmt; ss.
    { exfalso; move: (Mod.wf_fns _ Hwftctx).
      rewrite map_Forall_lookup => /(_ fno None) /=.
      rewrite lookup_union_with Hmt Hfnoctx //= => /(_ eq_refl) => [[??]] //.
    }
    iExists (SB.sandbox_body (fmsk, fbd)). iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap /= lookup_union_with
        Hmt Hfnoctx //. }
    iApply (@isim_reflL Γ Σ α β _S _I STATE).
    - intros k v Hmsk. iApply (HCTXPUT STATE k v).
      hexploit (Mod.well_scoped_fns ctx fno (fmsk, fbd)).
      { rewrite lookup_omap Hfnoctx //. }
      intros [Hput _]. eapply Hput. exact Hmsk.
    - intros k Hmsk. iApply (HCTXGET STATE k).
      hexploit (Mod.well_scoped_fns ctx fno (fmsk, fbd)).
      { rewrite lookup_omap Hfnoctx //. }
      intros [_ Hget]. eapply Hget. exact Hmsk.
  Qed.

  Lemma ISim_ctx contextual (ms mt ctx : Mod.t) Ist :
    ISim.t open ms mt Ist ⊢
    ISim.t contextual (ms ★ ctx) (mt ★ ctx)
      (λ STATE,
        (IstEq ctx STATE ∗ Ist STATE)%I).
  Proof.
    iApply (ISim_ctx_with contextual ms mt ctx Ist
      (IstEq ctx)).
    - intros STATE. iApply state_eq_init_same.
    - intros STATE k v IN. iApply state_eq_put.
      by rewrite elem_of_list_to_set.
    - intros STATE k IN. iApply state_eq_get.
      by rewrite elem_of_list_to_set.
  Qed.

  Theorem main_adequacy (Mt Ms : Mod.t) Ist :
    ISim.t open Ms Mt Ist ⊢ ctx_refines Mt Ms.
  Proof.
    iIntros "SIM" (Ctx).
    iApply ISim_closed_adequacy.
    iApply ISim_ctx. done.
  Qed.

End ADEQUACY.

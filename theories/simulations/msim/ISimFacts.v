From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.msim Require Import MSim MSimFacts
  MSimCommon ISim TacticsCommon ITactics.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Section ISIM_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Lemma isim_ist_frame ctx Ist P Rs Rt RR fl_src fl_tgt
      ps pt (i_s : itree crisE Rs) (i_t : itree crisE Rt) :
    P ∗ isim ctx fl_src fl_tgt Ist ibot RR ps pt i_s i_t ⊢
    isim ctx fl_src fl_tgt
      (P ∗ Ist)%I ibot (λ x y, P ∗ RR x y) ps pt i_s i_t.
  Proof using.
    eapply entails_pointwise. intros res VALID H.
    eapply isim_final.
    eapply Own_split in H as
      [rP [rSIM [EQ [HP HSIM]]]]; eauto.
    eapply isim_init in HSIM; et.
    gfinal. right.
    eapply paco8_mon; [eapply msim_ist_frame|]; ss.
    - ginit. eapply gpaco8_mon; eauto using iunlift_ibot.
    - rewrite EQ Own_op HP. et.
  Qed.
End ISIM_FRAME.

Section STATE_EQ.
  Context {Σ : GRA}.

  Definition state_eq (S : gset string) (STATE : stateGS Σ) : iProp Σ :=
    ∃ st_src st_tgt : gmap key (option Any.t),
      ⌜state_slice S st_src = state_slice S st_tgt⌝ ∗
      state_init_src S st_src STATE ∗ state_init_tgt S st_tgt STATE.

  Definition IstEq (M : Mod.t) : stateGS Σ → iProp Σ :=
    state_eq (list_to_set (Mod.scopes M)).

  Lemma state_eq_acc `{STATE : !stateGS Σ} S k (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        (∀ ov', ⌜state_cell_transition ov ov'⌝ -∗
          state_cell_src k ov' ∗ state_cell_tgt k ov' -∗
          state_eq S STATE).
  Proof.
    rewrite /state_eq /=. iIntros "EQ".
    iDestruct "EQ" as (st_src st_tgt) "(%EQ & SRC & TGT)".
    iPoseProof (state_init_src_acc S st_src k IN with "SRC") as
      (ov_src) "(%Hsrc & SRC & CLOSESRC)".
    iPoseProof (state_init_tgt_acc S st_tgt k IN with "TGT") as
      (ov_tgt) "(%Htgt & TGT & CLOSETGT)".
    assert (Hov : ov_src = ov_tgt).
    { rewrite Hsrc Htgt.
      pose proof (f_equal (fun st => st !! k) EQ) as EQk.
      rewrite (state_slice_lookup_in S st_src k IN)
        (state_slice_lookup_in S st_tgt k IN) in EQk.
      exact EQk. }
    clear Htgt. subst ov_tgt.
    iExists ov_src. iFrame "SRC TGT".
    iIntros (ov') "%TRANS [SRC TGT]".
    iExists (set_state_cell k ov' st_src),
      (set_state_cell k ov' st_tgt).
    iSplit.
    { iPureIntro.
      by apply state_slice_set_state_cell_eq. }
    iSplitL "SRC CLOSESRC".
    - iApply ("CLOSESRC" $! ov' with "[] SRC"). done.
    - iApply ("CLOSETGT" $! ov' with "[] TGT"). done.
  Qed.

  Lemma state_eq_put `{STATE : !stateGS Σ} S k v' (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ state_eq S STATE).
  Proof.
    iIntros "EQ".
    iPoseProof (state_eq_acc S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
    iApply ("CLOSE" $! (Some v') with "[] [SRC TGT]").
    - iPureIntro. right. done.
    - rewrite /state_cell_src /state_cell_tgt /=. iFrame.
  Qed.

  Lemma state_eq_get `{STATE : !stateGS Σ} S k (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗
          state_eq S STATE).
  Proof.
    iIntros "EQ".
    iPoseProof (state_eq_acc S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    iExists ov. iFrame "SRC TGT". iIntros "ST".
    iApply ("CLOSE" $! ov with "[] ST").
    iPureIntro. left. done.
  Qed.

  Lemma state_eq_init `{STATE : !stateGS Σ} S st_src st_tgt
      (EQ : state_slice S st_src = state_slice S st_tgt) :
    state_init_src S st_src STATE -∗
    state_init_tgt S st_tgt STATE -∗
    state_eq S STATE.
  Proof.
    iIntros "SRC TGT". iExists st_src, st_tgt. iFrame. done.
  Qed.

  Lemma state_eq_init_same `{STATE : !stateGS Σ} S st :
    state_init_src S st STATE -∗
    state_init_tgt S st STATE -∗
    state_eq S STATE.
  Proof.
    iApply state_eq_init. done.
  Qed.
End STATE_EQ.

Section ISIM_REFL.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{STATE : !stateGS Σ}.

  (* Reflexivity of the isim relation *)
  Lemma isim_refl g ctx (Ist : iProp Σ) fl_src fl_tgt msk ps pt {R}
      (it : itree crisE R) :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      Ist ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ Ist)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      Ist ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ Ist)) →
    Ist ⊢
    isim ctx fl_src fl_tgt Ist g (ist_with_eq Ist) ps pt
      (SB.sandbox msk it) (SB.sandbox msk it).
  Proof using.
    intros Hset Hget.
    revert it. combine_quant ps. combine_quant pt.
    eapply isim_coind. intros g0 _ CIH [pt [ps it]].
    destruct_quant CIH. iIntros "IST /=".
    assert (CASE := case_itrH it); des; subst.
    - istep. iFrame. done.
    - istep_s. istep_t. iby_coind CIH; eauto.
    - cNormT; cNormS. des_if.
      { istep_s. iforce_t; iFrame "ASM". cNormT. iby_coind CIH. eauto. }
      { istep_s; ss. }
    - cNormT; cNormS. des_if.
      { istep_s. iforce_t; iFrame "ASM". cNormT. iby_coind CIH. eauto. }
      { istep_s; ss. }
    - cNormT; cNormS. des_if.
      { istep_t. iforce_s; iFrame. cNormS. iby_coind CIH. eauto. }
      { istep_s; ss. }
    - depdes c.
      { cNormT; cNormS. des_if.
        { icall "IST" as (?) "IST"; et. iby_coind CIH; eauto. }
        { isteps_s; ss. }
      }
      { cNormT; cNormS. des_if.
        { istep. iby_coind CIH; done. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { iyield "IST" "IST". iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { istep. iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
    - depdes s.
      { cNormT; cNormS.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hset k v); destruct (msk _ _) eqn:Hmsk;
          [cNormS; cNormT|istep_s; ss].
        iPoseProof (Hset eq_refl with "IST") as
          (ov) "(SRC & TGT & CLOSE)".
        destruct ov as [v0|].
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sput_src. iFrame "SRC". iIntros "SRC".
          iApply isim_sput_tgt. iFrame "TGT". iIntros "TGT".
          iby_coind CIH. iApply ("CLOSE" with "[$SRC $TGT]").
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sput_src_uninit. iFrame "SRC". iIntros "SRC".
          iApply isim_sput_tgt_uninit. iFrame "TGT". iIntros "TGT".
          iby_coind CIH. iApply ("CLOSE" with "[$SRC $TGT]").
      }
      { cNormT; cNormS.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hget k); destruct (msk _ _) eqn:Hmsk;
          [cNormS; cNormT|istep_s; ss].
        iPoseProof (Hget eq_refl with "IST") as
          (ov) "(SRC & TGT & CLOSE)".
        destruct ov as [v|].
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sget_src. iFrame "SRC". iIntros "SRC".
          iApply isim_sget_tgt. iFrame "TGT". iIntros "TGT".
          iby_coind CIH.
          iApply ("CLOSE" with "[$SRC $TGT]").
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sget_src_uninit. iFrame "SRC". iIntros "SRC".
          iApply isim_sget_tgt_uninit. iFrame "TGT". iIntros "TGT".
          iby_coind CIH.
          iApply ("CLOSE" with "[$SRC $TGT]").
      }
    - destruct e.
      + cNormT; cNormS. des_if; [cNormS; cNormT|istep_s; ss].
        istep_t. iforce_s. cNormS; cNormT; iby_coind CIH; eauto.
      + cNormT; cNormS. des_if; [cNormS; cNormT|istep_s; ss].
        istep_s. iforce_t. cNormS; cNormT; iby_coind CIH; eauto.
      + cNormT; cNormS. des_if; [cNormS; cNormT|istep_s; ss].
        istep. cNormS; cNormT; iby_coind CIH; eauto.
  Qed.

  Lemma isim_reflL
      (ctx : contextuality) (fl_src fl_tgt : gmap fname (option fbody))
      (msk : emask) (EqL Ist : iProp Σ) itr :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      EqL ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ EqL)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      EqL ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ EqL)) →
    ⊢ isim_fsem fl_src fl_tgt (EqL ∗ Ist)%I ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg) "[E I] _".
    rewrite /SB.sandbox_body /=. iApply isim_refl.
    - intros k v' Hmsk. iIntros "[E I]".
      iPoseProof (Hset k v' Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitR "I"; last done. iApply ("CLOSE" with "[$SRC $TGT]").
    - intros k Hmsk. iIntros "[E I]".
      iPoseProof (Hget k Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitR "I"; last done. iApply ("CLOSE" with "[$SRC $TGT]").
    - iFrame.
  Qed.

  Lemma isim_reflR
      (ctx : contextuality) (fl_src fl_tgt : gmap fname (option fbody))
      (msk : emask) (Ist EqR : iProp Σ) itr :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      EqR ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ EqR)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      EqR ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ EqR)) →
    ⊢ isim_fsem fl_src fl_tgt (Ist ∗ EqR)%I ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg) "[I E] _".
    rewrite /SB.sandbox_body /=. iApply isim_refl.
    - intros k v' Hmsk. iIntros "[I E]".
      iPoseProof (Hset k v' Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitL "I"; first done. iApply ("CLOSE" with "[$SRC $TGT]").
    - intros k Hmsk. iIntros "[I E]".
      iPoseProof (Hget k Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitL "I"; first done. iApply ("CLOSE" with "[$SRC $TGT]").
    - iFrame.
  Qed.

End ISIM_REFL.

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

Section ISIM_MODULE_REFL.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_refl (ctx : contextuality) (M : Mod.t) :
    ⊢ ISim.t ctx M M (IstEq M).
  Proof.
    rewrite /ISim.t. iIntros (WF).
    iSplit.
    { iPureIntro. split; first done. destruct WF; done. }
    iIntros (STATE0).
    iSplit.
    { iIntros "SRC TGT".
      iApply (@state_eq_init_same Σ STATE0 (list_to_set (Mod.scopes M))
        (Mod.initial_st M) with "SRC TGT"). }
    iIntros (fn). rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite lookup_fmap in Hfs.
    destruct (Mod.fnsems M !! fn) as [[[fmsk fbdy]|]|] eqn:Hc; ss.
    hexploit (Mod.well_scoped_fns M fn (fmsk, fbdy)).
    { rewrite lookup_omap Hc //. }
    intros [HPUT HGET].
    clarify. iExists (SB.sandbox_body (fmsk, fbdy)).
    iSplit; first by rewrite /sandbox_fnsemmap lookup_fmap Hc.
    rewrite /isim_fsem. iIntros "!#" (arg) "IST _".
    rewrite /SB.sandbox_body /=. iApply (@isim_refl Σ STATE0).
    - intros k v Hmsk. iApply (@state_eq_put Σ STATE0).
      rewrite elem_of_list_to_set. eapply HPUT. exact Hmsk.
    - intros k Hmsk. iApply (@state_eq_get Σ STATE0).
      rewrite elem_of_list_to_set. eapply HGET. exact Hmsk.
    - iFrame.
  Qed.

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    Mod.scopes A ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (Mod.wf B → map_Forall (const is_Some) (Mod.fnsems A)) →
    (∀ (STATE : stateGS Σ) fn,
      ⌜fn ∈ dom (Mod.fnsems A)⌝ →
      @ISim.sim_fun Γ Σ α β _S _I ctx (C ★ A) (C ★ B)
        (λ STATE, (IstEq C STATE ∗ Ist STATE)%I) STATE fn) -∗
    (∀ STATE,
      state_init_src (list_to_set (Mod.scopes A))
        (Mod.initial_st A) STATE -∗
      state_init_tgt (list_to_set (Mod.scopes B))
        (Mod.initial_st B) STATE -∗
      Ist STATE) -∗
      ISim.t ctx (C ★ A) (C ★ B)
        (λ STATE, (IstEq C STATE ∗ Ist STATE)%I).
  Proof using.
    intros Hscp Hfns Hnodup.
    iIntros "Hsim Hinit". rewrite /ISim.t. iIntros (WFT).
    pose (SC := (list_to_set (Mod.scopes C) : gset string)).
    pose (SA := (list_to_set (Mod.scopes A) : gset string)).
    pose (SB := (list_to_set (Mod.scopes B) : gset string)).
    assert (SDISJ_CB : SC ## SB).
    { subst SC SB. apply mod_add_scope_disjoint. exact WFT. }
    assert (SA_SUB : SA ⊆ SB).
    { intros scope IN.
      rewrite /SA elem_of_list_to_set in IN.
      rewrite /SB elem_of_list_to_set.
      eapply elem_of_submseteq; eauto. }
    assert (SDISJ_CA : SC ## SA) by set_solver.
    assert (SLICE_SRC_C :
      state_slice SC (Mod.initial_st (C ★ A)) =
        state_slice SC (Mod.initial_st C)).
    { apply state_slice_union_with_l with (S2 := SA).
      - apply Mod.well_scoped_init.
      - exact SDISJ_CA. }
    assert (SLICE_SRC_A :
      state_slice SA (Mod.initial_st (C ★ A)) =
        state_slice SA (Mod.initial_st A)).
    { apply state_slice_union_with_r with (S1 := SC).
      - apply Mod.well_scoped_init.
      - exact SDISJ_CA. }
    assert (SLICE_TGT_C :
      state_slice SC (Mod.initial_st (C ★ B)) =
        state_slice SC (Mod.initial_st C)).
    { apply state_slice_union_with_l with (S2 := SB).
      - apply Mod.well_scoped_init.
      - exact SDISJ_CB. }
    assert (SLICE_TGT_B :
      state_slice SB (Mod.initial_st (C ★ B)) =
        state_slice SB (Mod.initial_st B)).
    { apply state_slice_union_with_r with (S1 := SC).
      - apply Mod.well_scoped_init.
      - exact SDISJ_CB. }
    destruct (Mod.add_wf_inv C B WFT) as
      [WFC [WFB [FNSDISJ SCOPEND]]].
    iSplit.
    { iPureIntro. split.
      { rewrite /= !sorting.merge_sort_Permutation.
        apply submseteq_app; [done | exact Hscp]. }
      eapply map_Forall_union_with.
      { set_solver. }
      split; [apply WFC | apply Hnodup, WFB].
    }
    iIntros (STATE). iSplitL "Hinit".
    { iIntros "SRC TGT".
      iEval (rewrite (mod_add_scope_set C A)) in "SRC".
      iEval (rewrite (mod_add_scope_set C B)) in "TGT".
      iPoseProof (state_init_src_union SC SA
        (Mod.initial_st (C ★ A)) SDISJ_CA with "SRC") as
        "[SRCC SRCA]".
      iPoseProof (state_init_tgt_union SC SB
        (Mod.initial_st (C ★ B)) SDISJ_CB with "TGT") as
        "[TGTC TGTB]".
      iPoseProof (state_init_src_ext SC (Mod.initial_st (C ★ A))
        (Mod.initial_st C) SLICE_SRC_C with "SRCC") as "SRCC".
      iPoseProof (state_init_src_ext SA (Mod.initial_st (C ★ A))
        (Mod.initial_st A) SLICE_SRC_A with "SRCA") as "SRCA".
      iPoseProof (state_init_tgt_ext SC (Mod.initial_st (C ★ B))
        (Mod.initial_st C) SLICE_TGT_C with "TGTC") as "TGTC".
      iPoseProof (state_init_tgt_ext SB (Mod.initial_st (C ★ B))
        (Mod.initial_st B) SLICE_TGT_B with "TGTB") as "TGTB".
      iSplitL "SRCC TGTC".
      - rewrite /IstEq.
        iApply (state_eq_init_same with "SRCC TGTC").
      - iApply ("Hinit" $! STATE with "SRCA TGTB"). }
    iIntros (fn).
    destruct (decide (fn ∈ dom (Mod.fnsems A))) as [Hin|Hnin].
    { iApply ("Hsim" $! STATE fn). done. }
    apply not_elem_of_dom in Hnin.
    rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT2" (fs) "%Hsrc".
    rewrite lookup_fmap lookup_union_with Hnin in Hsrc.
    destruct (Mod.fnsems C !! fn)
      as [[[fmsksrc fbdysrc]|]|] eqn:Hc; ss.
    clarify.
    destruct (Mod.fnsems B !! fn) as [fnt|] eqn:Hb.
    { exfalso. inv WFT2.
      rewrite map_Forall_lookup in wf_fns.
      hexploit (wf_fns fn).
      { rewrite lookup_union_with Hc Hb //=. }
      intros []; done.
    }
    hexploit (Mod.well_scoped_fns C fn (fmsksrc, fbdysrc)).
    { rewrite lookup_omap Hc //. }
    intros [HPUT HGET].
    iExists (SB.sandbox_body (fmsksrc, fbdysrc)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap lookup_union_with Hc Hb //. }
    iApply (@isim_reflL Γ Σ α β _S _I STATE).
    - intros k v Hmsk. iApply (@state_eq_put Σ STATE).
      rewrite /IstEq elem_of_list_to_set. eapply HPUT. exact Hmsk.
    - intros k Hmsk. iApply (@state_eq_get Σ STATE).
      rewrite /IstEq elem_of_list_to_set. eapply HGET. exact Hmsk.
  Qed.

  Lemma ISim_reflR
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    Mod.scopes A ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (Mod.wf B → map_Forall (const is_Some) (Mod.fnsems A)) →
    (∀ (STATE : stateGS Σ) fn,
      ⌜fn ∈ dom (Mod.fnsems A)⌝ →
      @ISim.sim_fun Γ Σ α β _S _I ctx (A ★ C) (B ★ C)
        (λ STATE, (Ist STATE ∗ IstEq C STATE)%I) STATE fn) -∗
    (∀ STATE,
      state_init_src (list_to_set (Mod.scopes A))
        (Mod.initial_st A) STATE -∗
      state_init_tgt (list_to_set (Mod.scopes B))
        (Mod.initial_st B) STATE -∗
      Ist STATE) -∗
      ISim.t ctx (A ★ C) (B ★ C)
        (λ STATE, (Ist STATE ∗ IstEq C STATE)%I).
  Proof using.
    intros Hscp Hfns Hnodup.
    iIntros "Hsim Hinit". rewrite /ISim.t. iIntros (WFT).
    pose (SA := (list_to_set (Mod.scopes A) : gset string)).
    pose (SB := (list_to_set (Mod.scopes B) : gset string)).
    pose (SC := (list_to_set (Mod.scopes C) : gset string)).
    assert (SDISJ_BC : SB ## SC).
    { subst SB SC. apply mod_add_scope_disjoint. exact WFT. }
    assert (SA_SUB : SA ⊆ SB).
    { intros scope IN.
      rewrite /SA elem_of_list_to_set in IN.
      rewrite /SB elem_of_list_to_set.
      eapply elem_of_submseteq; eauto. }
    assert (SDISJ_AC : SA ## SC) by set_solver.
    assert (SLICE_SRC_A :
      state_slice SA (Mod.initial_st (A ★ C)) =
        state_slice SA (Mod.initial_st A)).
    { apply state_slice_union_with_l with (S2 := SC).
      - apply Mod.well_scoped_init.
      - exact SDISJ_AC. }
    assert (SLICE_SRC_C :
      state_slice SC (Mod.initial_st (A ★ C)) =
        state_slice SC (Mod.initial_st C)).
    { apply state_slice_union_with_r with (S1 := SA).
      - apply Mod.well_scoped_init.
      - exact SDISJ_AC. }
    assert (SLICE_TGT_B :
      state_slice SB (Mod.initial_st (B ★ C)) =
        state_slice SB (Mod.initial_st B)).
    { apply state_slice_union_with_l with (S2 := SC).
      - apply Mod.well_scoped_init.
      - exact SDISJ_BC. }
    assert (SLICE_TGT_C :
      state_slice SC (Mod.initial_st (B ★ C)) =
        state_slice SC (Mod.initial_st C)).
    { apply state_slice_union_with_r with (S1 := SB).
      - apply Mod.well_scoped_init.
      - exact SDISJ_BC. }
    destruct (Mod.add_wf_inv B C WFT) as
      [WFB [WFC [FNSDISJ SCOPEND]]].
    iSplit.
    { iPureIntro. split.
      { rewrite /= !sorting.merge_sort_Permutation.
        apply submseteq_app; [exact Hscp | done]. }
      eapply map_Forall_union_with.
      { set_solver. }
      split; [apply Hnodup, WFB | apply WFC].
    }
    iIntros (STATE). iSplitL "Hinit".
    { iIntros "SRC TGT".
      iEval (rewrite (mod_add_scope_set A C)) in "SRC".
      iEval (rewrite (mod_add_scope_set B C)) in "TGT".
      iPoseProof (state_init_src_union SA SC
        (Mod.initial_st (A ★ C)) SDISJ_AC with "SRC") as
        "[SRCA SRCC]".
      iPoseProof (state_init_tgt_union SB SC
        (Mod.initial_st (B ★ C)) SDISJ_BC with "TGT") as
        "[TGTB TGTC]".
      iPoseProof (state_init_src_ext SA (Mod.initial_st (A ★ C))
        (Mod.initial_st A) SLICE_SRC_A with "SRCA") as "SRCA".
      iPoseProof (state_init_src_ext SC (Mod.initial_st (A ★ C))
        (Mod.initial_st C) SLICE_SRC_C with "SRCC") as "SRCC".
      iPoseProof (state_init_tgt_ext SB (Mod.initial_st (B ★ C))
        (Mod.initial_st B) SLICE_TGT_B with "TGTB") as "TGTB".
      iPoseProof (state_init_tgt_ext SC (Mod.initial_st (B ★ C))
        (Mod.initial_st C) SLICE_TGT_C with "TGTC") as "TGTC".
      iSplitR "SRCC TGTC".
      - iApply ("Hinit" $! STATE with "SRCA TGTB").
      - rewrite /IstEq.
        iApply (state_eq_init_same with "SRCC TGTC"). }
    iIntros (fn).
    destruct (decide (fn ∈ dom (Mod.fnsems A))) as [Hin|Hnin].
    { iApply ("Hsim" $! STATE fn). done. }
    apply not_elem_of_dom in Hnin.
    rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT2" (fs) "%Hsrc".
    rewrite lookup_fmap lookup_union_with Hnin in Hsrc.
    destruct (Mod.fnsems C !! fn)
      as [[[fmsksrc fbdysrc]|]|] eqn:Hc; ss.
    clarify.
    destruct (Mod.fnsems B !! fn) as [fnt|] eqn:Hb.
    { exfalso. inv WFT2.
      rewrite map_Forall_lookup in wf_fns.
      hexploit (wf_fns fn).
      { rewrite lookup_union_with Hc Hb //=. }
      intros []; done.
    }
    hexploit (Mod.well_scoped_fns C fn (fmsksrc, fbdysrc)).
    { rewrite lookup_omap Hc //. }
    intros [HPUT HGET].
    iExists (SB.sandbox_body (fmsksrc, fbdysrc)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap lookup_union_with Hc Hb //. }
    iApply (@isim_reflR Γ Σ α β _S _I STATE).
    - intros k v Hmsk. iApply (@state_eq_put Σ STATE).
      rewrite /IstEq elem_of_list_to_set. eapply HPUT. exact Hmsk.
    - intros k Hmsk. iApply (@state_eq_get Σ STATE).
      rewrite /IstEq elem_of_list_to_set. eapply HGET. exact Hmsk.
  Qed.

End ISIM_MODULE_REFL.

Section STATE_EQ_RULES.

  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{STATE : !stateGS Σ}.

  #[local] Set Implicit Arguments.

  Lemma isim_sput_eq ctx fl_s fl_t S g {Rs Rt} RR ps pt k v' k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (state_eq S STATE -∗
        @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR
          true true (k_s tt) (k_t tt)) ⊢
    @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR ps pt
      (trigger (SPut k v') >>= k_s) (trigger (SPut k v') >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_put S k v' IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sput_src. iFrame "SRC". iIntros "SRC".
      iApply isim_sput_tgt. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sput_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply isim_sput_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.

  Lemma isim_sget_eq ctx fl_s fl_t S g {Rs Rt} RR ps pt k k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (∀ v, state_eq S STATE -∗
        @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR
          true true (k_s v) (k_t v)) ⊢
    @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR ps pt
      (trigger (SGet k) >>= k_s) (trigger (SGet k) >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_get S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sget_src. iFrame "SRC". iIntros "SRC".
      iApply isim_sget_tgt. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! v). iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sget_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply isim_sget_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! (tt↑)). iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.

End STATE_EQ_RULES.

(* Section LAT.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma isim_lat_real_to_img
      peeking img fsp lbody_s lbody_t body_s body_t fl_s fl_t msk scp ps pt st arg
      (EQITL: eqit eq false true
              (SB.sandbox true msk scp (SModTr.trans img sp_none lbody_s))
              (SB.sandbox false msk scp (SModTr.trans img sp_none lbody_t)))
      (EQIT: eqit eq false true
              (SB.sandbox true msk scp (SModTr.trans img sp_none (body_s arg)))
              (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img peeking fsp lbody_s body_s arg)))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real peeking fsp lbody_t body_t arg))).
  Proof using.
    destruct fsp as [m pre post].
    iApply isim_reset. clear ps pt. iStopProof. revert st.
    eapply isim_coind. intros g Hg CIH st. iIntros. destruct_quant CIH.
    rewrite /lat_img /lat_real.
    unfoldIterS. unfoldIterT. rewrite {1}/lat_img_body {1}/lat_real_body.
    cNormS. cNormT. iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    destruct (peeking); cycle 1.
    {
      isteps_s. isteps_t.
      iApply isim_bind. iSplitL "".
      { iApply isim_eqit_tgt; et.
        iApply isim_refl; et; i; iIntros "%"; subst; et.
      }

      iIntros (????) "%"; des; subst.
      isteps_s. isteps_t.
      iforce_t. iFrame. iIntros "GRT".
      iforce_s. iFrame. isteps_s. isteps_t.
      istep; et.
    }

    isteps_t. destruct _q0.
    { iforce_t. iFrame. iIntros "GRT".
      iforce_s true. isteps_s. iforce_s. iFrame. isteps_s. isteps_t.
      iby_coind CIH; et.
    }

    iforce_s false. isteps_s. isteps_t.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }

    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    iforce_t. iFrame. iIntros "GRT".
    iforce_s. iFrame. isteps_s. isteps_t.
    istep; et.
  Qed.

  Lemma isim_lat_img_to_hoare fsp img body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox true msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_s. rewrite /lat_img /lat_img_body. unfoldIterT. isteps_t.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iforces_r. iFrame. isteps_t.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (?????). des; subst.
    isteps_t. iforces_l. iFrame.
    istep. et.
  Qed.

  Lemma isim_lat_real_to_hoare fsp img body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_s. rewrite /lat_real /lat_real_body. unfoldIterT. isteps_t.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    iforce_t. iFrame. iIntros "GRT".
    iforces_l. iFrame.
    isteps_s. isteps_t. istep; et.
  Qed.
End LAT. *)

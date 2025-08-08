Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod.
Require Import ISim ISimFacts.
Require Import CtxRefine MainAdequacy.
Require Import Tactics TacticsInit.

Set Implicit Arguments.

(*******
  Commutativity Proof
 *******)

Definition perm_Ist `{Σ: GRA} : alist key Any.t -> alist key Any.t -> iProp Σ :=
  λ l0 l1, ⌜l0 ≡ₚ l1⌝%I.  

Lemma alist_upd_perm {K V} l0 l1 `{Dec K} (k : K) (v : V)
    (ND : List.NoDup (List.map fst l0))
    (PERM : l0 ≡ₚ l1) :
  alist_upd k v l0 ≡ₚ alist_upd k v l1.
Proof.
  destruct (classic (In k (List.map fst l0))); cycle 1.
  {
    rewrite! alist_upd_not_in; eauto. ii.
    eapply H0. eapply Permutation_in; cycle 1; eauto.
    eapply Permutation_map. symmetry. eauto.
  }
  assert (List.NoDup (List.map fst l1)).
  { 
    eapply Permutation_NoDup; cycle 1; eauto. 
    eapply Permutation_map. eauto.
  }
  eapply alist_find_fst_in in H0. des.
  eapply alist_find_some in H0.
  assert (In (k, v0) l1).
  { eapply Permutation_in; eauto. }
  eapply in_split in H0, H2. des. subst.
  replace (l4 ++ (k, v0) :: l5) with ((l4 ++ [(k, v0)] ++ l5)); eauto.
  replace (l2 ++ (k, v0) :: l3) with ((l2 ++ [(k, v0)] ++ l3)); eauto.
  rewrite! alist_upd_with_nodup; eauto.
  eapply Permutation_app_middle, Permutation_app_inv. eauto.
  Unshelve. eauto.
Qed.

Lemma alist_permutation_find K `{Dec K} V (l0 l1 : alist K V)
      (ND : List.NoDup (List.map fst l0))
      (PERM : Permutation l0 l1)
      k
  :
    alist_find k l0 = alist_find k l1.
Proof.
  revert ND k. induction PERM; ss.
  { i. inv ND. destruct x. rewrite eq_rel_dec_correct. des_ifs. et. }
  { i. inv ND. inv H3. destruct x, y. rewrite eq_rel_dec_correct. des_ifs.
    rewrite eq_rel_dec_correct in Heq0. des_ifs. f_equal. exfalso. eapply H2. ss. auto. }
  { i. rewrite IHPERM1; auto. rewrite IHPERM2; auto.
    eapply Permutation_NoDup; [|apply ND].
    eapply Permutation_map. auto.
  }
Qed.

Lemma alist_find_comm {K V} `{Dec K}
      (l0 l1 : list (K*V)) fn f
      (NODUP : List.NoDup (List.map fst (l0 ++ l1)))
      (FIND : alist_find fn (l0 ++ l1) = Some f)
    :
      alist_find fn (l1 ++ l0) = Some f.
Proof.
  move: FIND; rewrite ?alist_find_app_o; intros FIND. des_ifs.
  eapply alist_find_fst_some in Heq, Heq0.
  rewrite map_app in NODUP.
  exfalso.
  eapply NoDup_app_disjoint in NODUP; eauto.
Qed.

Section CtxRefineFacts.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma mod_add_scopes md0 md1:
  Mod.scopes (md0 ★ md1) = Mod.scopes md0 ++ Mod.scopes md1.
Proof using. ss. Qed.

Lemma mod_add_comm contextual ms0 ms1:
  ISim.t contextual (ms0 ★ ms1) (ms1 ★ ms0) (emp%I)
    (IstSB (Mod.scopes (ms0 ★ ms1)) perm_Ist).
Proof using.
  econs; ss; i.
  { apply sub_perm_comm. }
  { rewrite ?map_app; i. apply sub_perm_comm. }
  { ii. ss. rewrite !map_app !alist_find_app_o in H0 |- *.
    des_ifs. esplits; et.
    iPureIntro. i. esplits; et.
    - rewrite /state_scopes map_app.
      eapply incl_app; [apply incl_appl|apply incl_appr];
        eapply Mod.well_scoped_init.
    - rewrite /state_scopes map_app.
      eapply incl_app; [apply incl_appr|apply incl_appl];
        eapply Mod.well_scoped_init.
    - eapply Permutation_app_comm.
  }

  destruct fn; cycle 1.
  {
    ii. ss. dup FIND.
    eapply alist_find_comm in FIND0; et. rewrite FIND0. esplits; et.
    ii. iIntros "% I". des; subst.
    iApply isim_mono; cycle 1.
    - iApply isim_nodup. iIntros (? ? ? ?).
      iApply isim_refl.
      + ii. iIntros "%". iPureIntro. des. eapply alist_permutation_find; et.
      + ii. iIntros "%". iPureIntro. des. esplits; et.
        * rewrite state_scopes_update. et.
        * rewrite state_scopes_update. et.
        * eapply alist_upd_perm; et.
      + iPureIntro. esplits; et.
        * rewrite /state_scopes map_app.
          eapply incl_app; [apply incl_appl|apply incl_appr];
            eapply Mod.well_scoped_init.
        * rewrite /state_scopes map_app.
          eapply incl_app; [apply incl_appr|apply incl_appl];
            eapply Mod.well_scoped_init.
        * eapply Permutation_app_comm.
    - i. iIntros "%". iPureIntro. des; et.
  }

  ii. eapply alist_find_comm in FIND; et. rewrite FIND. esplits; et.

  (* simulation *)
  ii. iIntros "S I". iStopProof.
  destruct fs as [[[img msk] scp] bd]. unfold SB.sandbox_body. s.
  generalize (bd arg) as it. clear FIND bd arg.
  combine_quant NODT.
  combine_quant NODS.
  combine_quant st_tgt.
  combine_quant st_src.
  eapply isim_coind. i.
  destruct a as [st_src [st_tgt [NODS [NODT it]]]]. s.
  destruct_quant.
  iIntros "((%IST & I) & #CIH)". des.
  assert (CASE := case_itrH it); des; subst.
  - step. eauto.
  - steps_l. steps_r. by_coind "CIH"; et.
  - destruct img.
    + steps_l. force_r. iFrame. steps_r. by_coind "CIH"; et.
    + rewrite SBRed.bind SBRed.Assume. s. steps_l. ss.
  - steps_l. force_r. iFrame. steps_l; steps_r. by_coind "CIH"; eauto.
  - steps_r. force_l. iFrame. steps_l. by_coind "CIH"; et.
  - destruct c.
    + norm_l. norm_r. rewrite! SBRed.call. des_ifs; ss.
      * iApply isim_call. iSplit; eauto. iIntros (? ? ? ? ?) "IST0".
        steps_l. steps_r. by_coind "CIH"; et.
      * steps_l. ss.
    + norm_l. norm_r. rewrite! SBRed.spawn. des_ifs; ss.
      * iApply isim_spawn. iIntros "%".
        steps_l. steps_r. by_coind "CIH"; et.
      * steps_l. ss.
    + yield ""; eauto. by_coind "CIH"; et.
  - depdes s0.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sput_src. iApply isim_sput_tgt.
      by_coind "CIH"; et.
      * rewrite alist_upd_keys. et.
      * rewrite ?alist_upd_keys. et.
      * iFrame. unfold perm_Ist. iPureIntro.
        rewrite !state_scopes_update. esplits; eauto. 
        eapply alist_upd_perm; eauto.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝)%I as "%".
      { iPureIntro. eapply alist_permutation_find; eauto. }
      rewrite H1. by_coind "CIH"; et.
  - destruct e.
    + steps_r. force_l. instantiate (1:= _q). steps_l. by_coind "CIH"; et.
    + rewrite SBRed.bind SBRed.take. des_ifs.
      * steps_l. force_r. instantiate (1:= _q). steps_r. by_coind "CIH"; et.
      * steps_l. ss.
    + step. by_coind "CIH"; et.
Qed.

(*******
  Properties of Contextual Refinements
 *******)

Global Program Instance refines_mod_PreOrder : PreOrder (@refines_lmod).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H. eapply H0. ss. Qed.

Global Program Instance refines_PreOrder : PreOrder refines.
Next Obligation.
  ii. esplits; eauto. ii. esplits; eauto. refl.
Qed.
Next Obligation.
  ii.
  edestruct H; eauto; edestruct H0; eauto. des.
  esplits; eauto. ii.
  specialize (H2 rs WFR SRC). des.
  specialize (H4 rt H2 H5). des. 
  exists rt0. esplits; eauto.
  etrans; eauto.
Qed.

(*** vertical composition ***)
Global Program Instance ctx_refines_PreOrder : PreOrder ctx_refines.
Next Obligation. r. r. i. refl. Qed.
Next Obligation.
  r. r. i. etrans.
  - apply H.
  - apply H0.
Qed.

Global Program Instance ctx_refines_Proper : Proper ((≡) ==> (≡) ==> iff) ctx_refines.
Next Obligation.
  intros ms1 ms2 mseq mt1 mt2 mteq; split; intros CTXR.
  { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
    { apply CTXR; s; eauto. }
    { ii. destruct (CTXR _ WFM). hexploit (H1 rs); eauto; ss.
      { rewrite H0; done. }
      { intros [rt Hrt]; rewrite H2 in Hrt; des; exists rt; esplits; eauto. }
    }
  }
  { destruct ms1, ms2, mt1, mt2; inv mseq; inv mteq; ii; ss; split; auto; clarify.
    { apply CTXR; s; eauto. }
    { ii. destruct (CTXR _ WFM). hexploit (H1 rs); eauto; ss.
      { rewrite -H0; done. }
      { intros [rt Hrt]; rewrite -H2 in Hrt; des; exists rt; esplits; eauto. }
    }
  }
Qed.

Global Program Instance ctx_refines_Proper2 mc : Proper ((≡) ==> iff) (ctx_refines mc).
Next Obligation.
  i. eapply ctx_refines_Proper. et.
Qed.

Lemma ctxr_refines mcs mct (REF : ctx_refines mcs mct) :
  refines mcs mct.
Proof using.
  i. specialize (REF Mod.empty_mc).
  destruct mcs, mct. ss.
  rewrite -!mod_add_empty_r in REF.
  ii; split; ii; des; ss; red in REF; hexploit REF; eauto; i; des; ss.
  hexploit (H0 rs); ss.
  { rewrite SRC. iIntros ">[? ?]"; iFrame; et. }
  i; des; esplits; eauto.
  rewrite H2. iIntros ">[? [? ?]]". iFrame. et.
Qed.

(*** weakening for initial condition ***)
Lemma ctxr_cond_strengthen (m : Mod.t) (P Q : iProp Σ) (IMPL : P ⊢ Q) :
  ctx_refines (m, P) (m, Q).
Proof using.
  ii. ss; split; first done. ii; ss; exists rs. esplits; eauto.
  + rewrite SRC IMPL. et.
  + refl.
Qed.

(*** frame rule for initial condition ***)
Lemma ctxr_cond_frameR (ms mt : Mod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms, Ps ∗ Q)%I (mt, Pt ∗ Q)%I.
Proof using.
  ii. specialize (REF (ctx.1, Q ∗ ctx.2)%I).
  destruct ctx. ss.
  split.
  { red in REF. hexploit REF; ss; i; des; eauto. }
  ii. ss. des. red in REF. hexploit REF; ss; i; des; eauto.
  hexploit (H0 rs); ss.
  { rewrite SRC. iIntros ">[? [[? ?] ?]]". iFrame. et. }
  i; des; esplits; eauto.
  rewrite H2. iIntros ">[? [? [? ?]]]". iFrame. et.
Qed.

Lemma ctxr_cond_frameL (ms mt : Mod.t) Ps Pt Q (REF : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms, Q ∗ Ps)%I (mt, Q ∗ Pt)%I.
Proof using.
  etrans; [|etrans]; cycle 1.
  { apply ctxr_cond_frameR with (Q:=Q) in REF. apply REF. }
  { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
  { eapply ctxr_cond_strengthen. i. iIntros "(H1 & H2)". iFrame. }
Qed.

(*** commutativity ***)
Theorem ctxr_comm (ma mb : Mod.t) P:
  ctx_refines (Mod.add ma mb, P) (Mod.add mb ma, P).
Proof using.
  etrans.
  { eapply ctxr_cond_strengthen.
    instantiate (1:= ((emp ∗ P)%I)). eauto. }
  etrans.
  { eapply ctxr_cond_frameR, main_adequacy, mod_add_comm. }
  eapply ctxr_cond_strengthen. iIntros "[_ ?]"; et.
Qed.

(*** frame rules ***)
Lemma ctxr_frameR ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
Proof using.
  intro. specialize (REFA (Mod.add mc ctx.1, ctx.2)). ss.
  move: REFA; rewrite !mod_add_assoc; eauto.
Qed.

Lemma ctxr_frameL ms Ps mt Pt mc (REFA : ctx_refines (ms, Ps) (mt, Pt)) :
  ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
Proof using.
  etrans. { eapply ctxr_comm. }
  etrans. { eapply ctxr_frameR. apply REFA. }
  apply ctxr_comm.
Qed.

(*** horizontal composition ***)
Lemma ctxr_compose_hor msa Psa mta Pta msb Psb mtb Ptb
    (REFA : ctx_refines (msa, Psa) (mta, Pta))
    (REFB : ctx_refines (msb, Psb) (mtb, Ptb)) :
  ctx_refines (msa ★ msb, Psa ∗ Psb)%I
              (mta ★ mtb, Pta ∗ Ptb)%I.
Proof using.
  etrans.
  - eapply ctxr_frameR, ctxr_cond_frameR. apply REFA.
  - eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. 
Qed.

(*** mixed composition ***)
Lemma ctxr_compose_mix msa Psa mta Pta msb Psb mtb Ptb mc
    (REFA : ctx_refines (msa ★ mc, Psa) (mta ★ mc, Pta))
    (REFB : ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb)) :
  ctx_refines (msa ★ msb ★ mc, Psa ∗ Psb)%I
              (mta ★ mtb ★ mc, Pta ∗ Ptb)%I.
Proof using.
  etrans.
  { eapply ctxr_frameL, ctxr_cond_frameL. apply REFB. }
  etrans.
  { eapply ctxr_frameL, ctxr_comm. }
  etrans.
  { rewrite <-mod_add_assoc.
    eapply ctxr_frameR, ctxr_cond_frameR. apply REFA. }
  rewrite mod_add_assoc.
  apply ctxr_frameL, ctxr_comm.
Qed.

(*** Corollaries for tactics ***)

Corollary ctxr_compose_hor_simplR msa mta msb mtb P Pa
    (REFA : ctx_refines (msa, Pa) (mta, P))
    (REFB : ctx_refines (msb, emp%I) (mtb, emp%I)) :
  ctx_refines (msa ★ msb, Pa)%I
              (mta ★ mtb, P)%I.
Proof using.
  rewrite (mod_addc_empty_r _ P) (mod_addc_empty_r _ Pa).
  eapply ctxr_compose_hor; et.
Qed.

Corollary ctxr_cond_frameR_simpl (ms mt : Mod.t) P Q
  (REF : ctx_refines (ms, P) (mt, emp%I))
  :
  ctx_refines (ms, P ∗ Q)%I (mt, Q)%I.
Proof using.
  rewrite (mod_addc_empty_l _ Q).
  eapply ctxr_cond_frameR. et.
Qed.

End CtxRefineFacts.

(*******
 tactics for composing ctx_refines
 *******)

Ltac ctxr_norm :=
  try rewrite <-!mod_add_assoc;
  try rewrite ->!mod_add_assoc;
  (hrepeat do 1 first [rewrite -!mod_addc_empty_l|rewrite -!mod_addc_empty_r]);
  try(try (match goal with [|-_ (_,emp%I)] => fail 2 end);
      eapply ctxr_cond_frameR_simpl).

Ltac _ctxr_swap :=
  try (rewrite -mod_add_assoc; eapply ctxr_compose_hor_simplR; [|refl]);
  eapply ctxr_comm.

Ltac ctxr_swap :=
  ctxr_norm;
  etrans; [|_ctxr_swap];
  ctxr_norm.

Ltac ctxr_rotate :=
  ctxr_norm;
  (etrans; [|eapply ctxr_comm]);
  ctxr_norm.

Ltac ctxr_drop :=
  ctxr_norm;
  eapply ctxr_frameL.

Ltac ctxr_refl :=
  ctxr_norm;
  refl.

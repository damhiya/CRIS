Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr SMod HMod Tactics.
Require Import ISim ISimInit CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import HModInline.

Set Implicit Arguments.

Lemma inline_intro `{Σ: GRA} md P
  :
  refines (HModInline.inline md, P) (md, P).
Proof.
  eapply closed_adequacy2. clear P.

  cut (∀ f (WF: HMod.wf md) (SCP: incl f.1.2 md.(HMod.scopes)),
   isim_fsem
    (map (map_snd SB.sandbox_body)
       (map (map_snd (inline_fsem md)) (HMod.fnsems md)))
    (map (map_snd SB.sandbox_body) (HMod.fnsems md)) IstEq closed
    (SB.sandbox_body (inline_fsem md f)) (SB.sandbox_body f)).
  {
    econs; ss; try refl; eauto; i.
    { r. s. destruct (HMod.initial_code md) eqn: E; ss.
      - i. r in H.
        iIntros "_". iApply isim_nodup. iIntros (? ? ? ?).
        iApply isim_mono; cycle 1.
        + iApply H; et.
          ss. ii. exploit HMod.well_scoped_initcode; et. rewrite E. s. et.
        + i. iIntros "%". iPureIntro. des; subst; et.
      - iIntros "_". iPureIntro. et.
    }
    { i. rewrite List.map_map fst_map_snd. exists []. ss. }
    { ii. rewrite alist_find_map_snd in FIND.
      destruct (alist_find fn (HMod.fnsems md)) eqn:FINDT; ss.
      inv FIND. esplits; eauto.
      ii. iIntros "%". subst. iApply H; et.
      ss. ii. exploit HMod.well_scoped_fns; et.
      rewrite /fnsems_scopes. erewrite FINDT. destruct f as [[][]]. et.
    }
  }
  
  ii. iIntros "%". subst.
  destruct f as [[msk scp][img bd]].
  rewrite /SB.sandbox_body; s. rewrite /SB.sandbox_body; s.

  generalize false at 1 as ps. generalize false at 1 as pt.
  generalize (bd arg) as it. i.
  ss. clear bd arg NODD NODS. rename st_tgt into st.

  iStopProof. revert it.
  combine_quant st.
  combine_quant pt.
  combine_quant ps.
  combine_quant nths.
  combine_quant msk.
  combine_quant img.
  combine_quant SCP.
  combine_quant scp.
  
  eapply isim_coind. i.
  destruct a as [scp [SCP [img [msk [nths [ps [pt [st it]]]]]]]]. s.

  iIntros "(_ & #CIH)". destruct_quant.

  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret HIRed.ret. step. eauto.
  - rewrite SBRed.tau HIRed.tau. steps_l. steps_r. by_coind "CIH"; et.
  - rewrite SBRed.bind SBRed.Assume. destruct img; cycle 1.
    { s. rewrite bind_bind HIRed.core. steps_l. ss. }
    rewrite HIRed.ag. steps_l. force_r. iFrame.
    steps_r. by_coind "CIH"; et.
  - rewrite SBRed.bind SBRed.AssumePrecise HIRed.ag. steps_l.
    step. steps_l. by_coind "CIH"; et.
  - rewrite SBRed.bind SBRed.Guarantee HIRed.ag.
    steps_r. force_l. iFrame. steps_l. by_coind "CIH"; et.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.call. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite HIRed.core. steps_l. ss. }

      rewrite HIRed.call. steps_l. rewrite {3}/sandboxed_prog.
      destruct (alist_find fn (HMod.fnsems md)) eqn:FIND; cycle 1.
      { s. ired. rewrite HIRed.core. steps_l. ss. }
      destruct f as [[msk0 scp0][img0 bd0]]. iApply isim_inline_tgt.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite /SB.sandbox_body. s.

      rewrite HIRed.bind SBRed.bind.
      iApply isim_bind; iSplitL.
      - by_coind "CIH"; et.
        iPureIntro. ii. exploit HMod.well_scoped_fns; et.
        rewrite /fnsems_scopes. erewrite FIND. et.
      - iIntros (? ? ? ? ?) "%". des; subst.
        rewrite HIRed.tau. steps_l. steps_r. ired.
        by_coind "CIH"; et.
    }
    {
      rewrite !SBRed.bind !SBRed.spawn. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite HIRed.core. steps_l. ss. }
      rewrite HIRed.spawn SBRed.bind SBRed.spawn.
      iApply isim_spawn.
      steps_l. by_coind "CIH"; et.
    }
    {
      rewrite SBRed.bind SBRed.yield HIRed.yield !SBRed.bind !SBRed.yield.
      iApply isim_yield. iSplit; et. iIntros (? ? ? ? ?) "%". subst.
      steps_l. by_coind "CIH"; et.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1. 
      { unfold triggerUB; ired. rewrite HIRed.core. steps_l. ss. }
      rewrite HIRed.pg SBRed.bind SBRed.put. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        eapply SCP in Heq. edestruct existsb_exists.
        erewrite Heq0 in H1. exploit H1; ss. esplits; et.
        eapply String.eqb_eq. et.
      } 
      iApply isim_sput_src. iApply isim_sput_tgt.
      steps_l. by_coind "CIH"; et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { unfold triggerUB; ired. rewrite HIRed.core. steps_l. ss. }
      rewrite HIRed.pg SBRed.bind SBRed.get. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des. 
        eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
        rewrite XEQ1 in Heq0; ss; eauto.
      } 
      iApply isim_sget_src. iApply isim_sget_tgt.
      steps_l. by_coind "CIH"; et.
  - depdes e.
    + rewrite SBRed.bind SBRed.choose HIRed.core. 
      steps_r. force_l. steps_l. by_coind "CIH"; et.
    + rewrite SBRed.bind SBRed.take.
      des_ifs; cycle 1.
      { rewrite bind_bind HIRed.core. steps_l; ss. }
      rewrite HIRed.core.  steps_l. force_r.
      by_coind "CIH"; et.
    + rewrite SBRed.bind SBRed.io HIRed.core.
      step. steps_l. by_coind "CIH"; et.
(*SLOW*)Admitted.

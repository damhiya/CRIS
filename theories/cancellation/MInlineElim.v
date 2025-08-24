Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr SMod Mod Tactics.
Require Import ISim ISimFacts CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import MInline.

Set Implicit Arguments.

Section INLINE.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma inline_elim md P : refines (md, P) (MInline.inline md, P).
Proof using.
  eapply closed_adequacy_emp.

  cut (∀ f (WF: Mod.wf md) (SCP: incl f.1.2 md.(Mod.scopes)),
  isim_fsem
    (map (map_snd SB.sandbox_body) (Mod.fnsems md))            
    (map (map_snd SB.sandbox_body)
       (map (map_snd (inline_fsem md)) (Mod.fnsems md)))
     IstEq closed IstEq IstEq
    (SB.sandbox_body f) (SB.sandbox_body (inline_fsem md f))).
  {
    econs; ss; try refl; eauto; i.
    { i. rewrite List.map_map fst_map_snd. exists []. ss. }
    { ii. split.
      - rewrite !alist_find_map_snd !/o_map in H1 |- *. des_ifs.
      - iIntros. iPureIntro. et.
    }
    { ii. s. rewrite !alist_find_map_snd FIND. esplits; eauto.
      ii. iIntros "H I". iAssert (⌜st_src = st_tgt⌝)%I as "%EQ".
      { destruct fn; iDestruct "H" as "%"; des; subst; et. }
      subst. iApply isim_mono; cycle 1.
      - iApply H; et.
        ii. exploit Mod.well_scoped_fns; et.
        rewrite /fnsems_scopes. erewrite FIND. destruct fs as [[[] ?] ?]. et.
      - i. iIntros "%". des; subst. destruct fn; et.
    }
  }

  ii. iIntros "% I". subst. iStopProof. 
  destruct f as [[[img msk] scp] bd].
  rewrite /SB.sandbox_body; s. rewrite /SB.sandbox_body; s.

  generalize false at 1 as ps. generalize false at 1 as pt.
  generalize (bd arg) as it. i.
  ss. clear bd arg. rename st_tgt into st.

  revert it.
  combine_quant st.
  combine_quant pt.
  combine_quant ps.
  combine_quant msk.
  combine_quant img.
  combine_quant SCP.
  combine_quant scp.
  
  eapply isim_coind. intros ? _ CIH [scp [SCP [img [msk [ps [pt [st it]]]]]]]; s.
  destruct_quant CIH. iIntros "I".

  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret MIRed.ret. step. eauto.
  - rewrite SBRed.tau MIRed.tau. steps_l. steps_r. by_coind CIH; et.
  - rewrite SBRed.bind SBRed.Assume. destruct img; cycle 1.
    { s. rewrite bind_bind MIRed.core. steps_l. ss. }
    rewrite MIRed.ag. steps_l. force_r. iFrame.
    steps_r. by_coind CIH; et.
  - rewrite SBRed.bind SBRed.Guarantee MIRed.ag.
    steps_r. force_l. iFrame. norm_l. by_coind CIH; et.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.call. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite MIRed.core. steps_l. ss. }

      rewrite MIRed.call. steps_r. rewrite {2}/sandboxed_prog.
      destruct (alist_find (Some fn) (Mod.fnsems md)) eqn:FIND; cycle 1.
      { iApply isim_call_none; et. rewrite !alist_find_map_snd FIND. et. }
      destruct f as [[[img0 msk0] scp0] bd0]. iApply isim_inline_src.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite /SB.sandbox_body. s.

      rewrite MIRed.bind SBRed.bind.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iApply isim_bind. iSplitL "I".
      - by_coind CIH; et.
        ii. exploit Mod.well_scoped_fns; et.
        rewrite /fnsems_scopes. erewrite FIND. et.
      - iIntros (? ? ? ?) "%". des; subst.
        rewrite MIRed.tau. steps_l. steps_r. ired.
        by_coind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.spawn. des_ifs; cycle 1.
      { unfold triggerUB. ired. rewrite MIRed.core. steps_l. ss. }
      rewrite MIRed.spawn SBRed.bind SBRed.spawn.
      iApply isim_spawn.
      iIntros (?); steps_r. by_coind CIH; et.
    }
    {
      rewrite SBRed.bind SBRed.yield MIRed.yield !SBRed.bind !SBRed.yield.
      iApply isim_yield. iSplit; et. iIntros (? ?) "%". subst.
      steps_r. by_coind CIH; et.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1. 
      { unfold triggerUB; ired. rewrite MIRed.core. steps_l. ss. }
      rewrite MIRed.pg SBRed.bind SBRed.put. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des.
        eapply String.eqb_eq in Heq1. subst.
        eapply SCP in Heq. edestruct existsb_exists.
        erewrite Heq0 in H0. exploit H0; ss. esplits; et.
        eapply String.eqb_eq. et.
      } 
      iApply isim_sput_src. iApply isim_sput_tgt.
      steps_r. by_coind CIH; et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { unfold triggerUB; ired. rewrite MIRed.core. steps_l. ss. }
      rewrite MIRed.pg SBRed.bind SBRed.get. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des. 
        eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
        rewrite XEQ1 in Heq0; ss; eauto.
      } 
      iApply isim_sget_src. iApply isim_sget_tgt.
      steps_r. by_coind CIH; et.
  - depdes e.
    + rewrite SBRed.bind SBRed.choose MIRed.core. 
      steps_r. force_l. steps_l. by_coind CIH; et.
    + rewrite SBRed.bind SBRed.take.
      des_ifs; cycle 1.
      { rewrite bind_bind MIRed.core. steps_l; ss. }
      rewrite MIRed.core. steps_l. steps_r. force_r. steps_r.
      by_coind CIH; et.
    + rewrite SBRed.bind SBRed.io MIRed.core.
      step. steps_r. norm_l. by_coind CIH; et.
Qed.

End INLINE.

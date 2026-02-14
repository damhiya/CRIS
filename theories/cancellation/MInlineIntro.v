Require Import Common ConcRA.
Require Import SModTr SMod Mod Tactics.
Require Import MSimCommon ISim ISimFacts CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import MInline.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Set Implicit Arguments.

Section INLINE.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma inline_intro (md : Mod.t) P :
  refines (MInline.inline md, P) (md, P).
Proof using.
  eapply closed_adequacy_emp with (Ist:=IstEq). clear P.

  cut (∀ f (WF: Mod.wf md) (* (SCP: f.1 ∈ md.(Mod.scopes)) *),
   isim_fsem
    (fmap (λ v: option (emask * fbody), SB.sandbox_body <$> v) (fmap (option_map (inline_fsem md)) (Mod.fnsems md)))
    (fmap (λ v: option (emask * fbody), SB.sandbox_body <$> v) (Mod.fnsems md))
    IstEq closed
    (SB.sandbox_body (inline_fsem md f)) (SB.sandbox_body f)).
  { econs; ss; try refl; eauto; i.
    r. rewrite !lookup_fmap.
    destruct (Mod.fnsems md !! fn) eqn:FINDT; ss.
    destruct o; ss.
    { destruct p; ss. ii. esplits; eauto. }
    intros [? ?]; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns fn None); eauto.
    intros t; inv t.
  }

  ii. iIntros "% I". subst. iStopProof.
  destruct f as [msk bd].
  do 2 (rewrite /SB.sandbox_body; s).

  generalize false at 1 as ps. generalize false at 1 as pt.
  generalize (bd arg) as it. i.
  ss. clear bd arg. rename st_tgt into st.

  revert it.
  combine_quant st.
  combine_quant pt.
  combine_quant ps.
  combine_quant msk.
  eapply isim_coind. intros ? _ CIH [msk [ps [pt [st it]]]]; s.
  destruct_quant CIH. iIntros "I".
  
  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret MIRed.ret. istep. eauto.
  - rewrite SBRed.tau MIRed.tau !SBRed.tau. steps_l. steps_r. by_coind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
    ired. rewrite -(bind_ret_r (trigger (Assume _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. istep_l. istep_l.
    rewrite MIRed.ret. istep_l. rewrite !SBRed.ret bind_ret_l.
    iforce_r. iFrame. isteps_r.
    by_coind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
    ired. rewrite -(bind_ret_r (trigger (AssumeRes _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. istep_l. istep_l.
    rewrite MIRed.ret. istep_l. rewrite !SBRed.ret bind_ret_l.
    iforce_r. iFrame. isteps_r.
    by_coind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
    ired. rewrite -(bind_ret_r (trigger (Guarantee _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. istep_r. istep_r.
    iforce_l. iFrame. isteps_l.
    rewrite MIRed.ret. istep_l. istep_l. rewrite !SBRed.ret bind_ret_l.
    by_coind CIH; eauto.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.call. istep_l. rewrite {2}/sandboxed_prog.
      destruct ((Mod.fnsems md) !! fid fn) eqn:FIND; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      destruct o; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      destruct p as [msk0 bd0]. iApply isim_inline_tgt.
      { rewrite lookup_fmap FIND //. }
      rewrite lookup_omap FIND /=. ired. rewrite /SB.sandbox_body. s.

      rewrite MIRed.bind SBRed.bind.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iApply isim_bind. iSplitL "I".
      - by_coind CIH; et.
      - iIntros (? ? ? ?) "%". des; subst.
        rewrite bind_tau bind_ret_l !MIRed.tau. ired. rewrite !SBRed.ret !bind_ret_l. do 2 istep_l. istep_r.
        by_coind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.spawn SBRed.bind SBRed.vis !vis_trigger. des_ifs. ired.
      iApply isim_spawn. iIntros (?). istep_l. istep_r.
      rewrite !SBRed.ret !bind_ret_l. by_coind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.yield !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_yield. iSplit; et. iIntros (??) "%". subst.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.gettid !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_gettid. iIntros (?).
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. istep_l; ss. }
      ired. iApply isim_sput_src. iApply isim_sput_tgt.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. istep_l; ss. }
      ired. iApply isim_sget_src. iApply isim_sget_tgt.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
  - depdes e.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. istep_r. iforce_l _q. ired. rewrite !SBRed.ret !bind_ret_l.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. istep_l. iforce_r _q. ired. rewrite !SBRed.ret !bind_ret_l.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. istep_l; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. istep. ired. rewrite !SBRed.ret !bind_ret_l.
      istep_l. istep_r. rewrite !SBRed.ret bind_ret_l. by_coind CIH; et.
(*SLOW*)Qed.

End INLINE.

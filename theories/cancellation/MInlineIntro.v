From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import SModTr SMod Mod.
From CRIS.simulations.msim Require Import Tactics SimNotations MSimCommon ISim ISimFacts.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy.
From CRIS.cancellation Require Import MInline.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Set Implicit Arguments.

Section INLINE.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma inline_intro md :
  ⊢ refines md (MInline.inline md).
Proof using.
  iApply (ISim_closed_adequacy md (MInline.inline md) IstEq).

  cut (⊢ ∀ f : emask * fbody,
    isim_fsem
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (fmap (option_map (inline_fsem md)) (Mod.fnsems md)))
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (Mod.fnsems md))
      IstEq closed
      (SB.sandbox_body (inline_fsem md f)) (SB.sandbox_body f)).
  { intros FSIMS. iPoseProof FSIMS as "#FSIMS".
    rewrite /ISim.t.
    iIntros (WF). iSplit.
    { iPureIntro. split; first done.
      eapply map_Forall_fmap, map_Forall_impl; first apply WF.
      intros ? [[??]|]; ss. }
    iSplit; first done.
    iIntros (fn). rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite /sandbox_fnsemmap !lookup_fmap in Hfs.
    destruct (Mod.fnsems md !! fn) as [[[msk body]|]|]
      eqn:FINDT; ss; clarify.
    iExists (SB.sandbox_body (msk, body)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap FINDT //. }
    iApply ("FSIMS" $! (msk, body)).
  }

  iIntros (f). rewrite /isim_fsem.
  iIntros "!#" (arg st_src st_tgt) "-> I".
  destruct f as [msk bd].
  generalize false at 1 as ps. generalize false at 1 as pt.
  do 2 (rewrite /SB.sandbox_body; s). generalize (bd arg) as it. i; ss. clear bd arg.
  cCoind CIH g __ with ps pt it st_tgt msk. iIntros "I".

  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret MIRed.ret. cStep. eauto.
  - rewrite SBRed.tau MIRed.tau !SBRed.tau. cStepsS. cStepsT. cByCoind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Assume _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. cStepS.
    rewrite MIRed.ret. cStepS. rewrite !SBRed.ret bind_ret_l.
    iforce_t. iFrame. cStepsT.
    cByCoind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (AssumeRes _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. cStepS.
    rewrite MIRed.ret. cStepS. rewrite !SBRed.ret bind_ret_l.
    iforce_t. iFrame. cStepsT.
    cByCoind CIH; eauto.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Guarantee _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepT. cStepT.
    iforce_s. iFrame. cStepsS.
    rewrite MIRed.ret. cStepS. cStepS. rewrite !SBRed.ret bind_ret_l.
    cByCoind CIH; eauto.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.call. cStepS. rewrite {2}/sandboxed_prog.
      destruct ((Mod.fnsems md) !! funid fn) eqn:FIND; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      destruct o; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      destruct p as [msk0 bd0]. iApply isim_inline_tgt.
      { rewrite lookup_fmap FIND //. }
      rewrite lookup_omap FIND /=. ired. rewrite /SB.sandbox_body. s.

      rewrite MIRed.bind SBRed.bind.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iApply isim_bind. iSplitL "I".
      - cByCoind CIH; et.
      - iIntros (? ? ? ?) "%". des; subst.
        rewrite bind_tau bind_ret_l !MIRed.tau. ired. rewrite !SBRed.ret !bind_ret_l. do 2 cStepS. cStepT.
        cByCoind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.spawn SBRed.bind SBRed.vis !vis_trigger. des_ifs. ired.
      iApply isim_spawn. iIntros (?). cStepS. cStepT.
      rewrite !SBRed.ret !bind_ret_l. cByCoind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.yield !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_yield. iSplit; et. iIntros (??) "%". subst.
      cStepS. cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.gettid !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_gettid. iIntros (?).
      cStepS. cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. cStepS; ss. }
      ired. iApply isim_sput_src. iApply isim_sput_tgt.
      cStepS. cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. cStepS; ss. }
      ired. iApply isim_sget_src. iApply isim_sget_tgt.
      cStepS. cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et.
  - depdes e.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepT. cForceS _q. cStepsS. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepsS. cForceT _q. ired. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStep. cStepsS. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et.
(*SLOW*)Qed.

End INLINE.

From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import SModTr SMod HMod ITactics.
Require Import ISim ISimInit CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import HModInline.

Set Implicit Arguments.

Lemma cancel_call `{Σ: GRA} md P
:
  refines (HModInline.inline md, P) (md, P).
Proof.
  eapply closed_adequacy2.
  econs; ss; try refl; eauto.
  { i. rewrite List.map_map fst_map_snd. exists []. ss. }
  ii. rewrite alist_find_map_snd in FIND.
  destruct (alist_find fn (HMod.fnsems md)) eqn:FINDT; ss.
  inv FIND. rename p into ft. esplits; eauto.
  ii. subst. destruct ft.
  assert(SCP := md.(HMod.well_scoped_fns)).
  specialize (SCP fn). rewrite/fnsems_scopes FINDT in SCP.
  remember (HMod.scopes md) as scopeS. i.
  rename l into scopeT. 
  unfold wrap_elimI. s. unfold HModTr.sandbox_body, inline_hp_fun. s.
  generalize false at 1 as ps.
  generalize false at 1 as pt. intros pt ps.
  generalize (i y) as it. clear IN fn FINDT i y NODD NODS.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant SCP.
  combine_quant scopeT.
  combine_quant pt.
  combine_quant ps.
  combine_quant nths.
  eapply isim_coind. i.
  destruct a as [nths [ps [pt [scopeT [SCP [st_src [st_tgt it]]]]]]]. s.
  iIntros "(Ist & #CIH)".
  
  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret HIRed.ret. step. eauto.
  - rewrite SBRed.tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
  - rewrite SBRed.bind SBRed.ag HIRed.bind_ag. steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
  - rewrite SBRed.bind SBRed.ag HIRed.bind_ag. steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.call.
      rewrite HIRed.call. steps_l.
      destruct (alist_find fn (HMod.fnsems md)) eqn:FIND; cycle 1.
      { ss. unfold triggerUB. ired. rewrite HIRed.bind_core. steps_l. ss. }
      destruct p. iApply isim_inline_tgt.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite HIRed.bind SBRed.bind.
      iApply isim_bind; iSplitL.
      {
        iApply isim_RR_frame. 
        iSplitR; [iApply "CIH"|]. by_coind "CIH". eauto.  
      }
      unfold bindRR. iIntros (? ? ? ? ?) "(_ & % & IST)". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    }    
    {
      rewrite !SBRed.bind !SBRed.spawn.
      rewrite HIRed.bind_spawn SBRed.bind SBRed.spawn.
      iApply isim_spawn. steps_l. by_coind "CIH". auto.
    }
    {
      rewrite SBRed.bind SBRed.yield HIRed.bind_yield !SBRed.bind !SBRed.yield.
      iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
      steps_l. by_coind "CIH". auto.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1. 
      { steps_r. unfold triggerUB; ired.
        rewrite HIRed.bind_core. steps_l. ss. }
      rewrite HIRed.bind_pg SBRed.bind SBRed.put. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des. 
        eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
        rewrite XEQ1 in Heq0; ss; eauto.
      } 
      iApply isim_sput_src. iApply isim_sput_tgt.
      steps_l. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { steps_r. unfold triggerUB; ired.
        rewrite HIRed.bind_core. steps_l. ss. }
      rewrite HIRed.bind_pg SBRed.bind SBRed.get. des_ifs; cycle 1.
      { 
        exfalso. eapply existsb_exists in Heq. des. 
        eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
        rewrite XEQ1 in Heq0; ss; eauto.
      } 
      iApply isim_sget_src. iApply isim_sget_tgt.
      steps_l. iDestruct "Ist" as "%". subst. 
      by_coind "CIH". eauto.
  - rewrite SBRed.bind SBRed.core HIRed.bind_core. depdes e.
    + steps_r. force_l. steps_l.
      instantiate (1:= q). by_coind "CIH". eauto.
    + steps_l. force_r. instantiate (1:= q). steps_r.
      by_coind "CIH". auto.
    + step. steps_l. steps_r. by_coind "CIH". auto.
  Unshelve. all: eauto.
  {
    assert(SCP0 := md.(HMod.well_scoped_fns) fn).
    rewrite/fnsems_scopes FIND in SCP0. eauto.
  }
(*SLOW*)Qed.


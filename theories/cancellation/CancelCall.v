Require Import Common.
Require Import SMod2HMod SMod HMod ITactics.
Require Import ISim CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import HModInline.

Set Implicit Arguments.

Section CANCEL.
  Context `{Σ: GRA}.
  Variable md: HMod.t.

  Lemma cancel_call P
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
    unfold wrap_elimI. s. unfold HMod.sandbox_body, inline_hp_fun. s.
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
    - rewrite SBRed.transl_ret HIRed.ret. step. eauto.
    - rewrite SBRed.transl_tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite SBRed.transl_bind SBRed.transl_ag HIRed.bind_ag. steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
    - rewrite SBRed.transl_bind SBRed.transl_ag HIRed.bind_ag. steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
    - rewrite SBRed.transl_bind SBRed.transl_sch HIRed.bind_sch. depdes s.
      + step. steps_l. steps_r. by_coind "CIH". auto.
      + rewrite !SBRed.transl_bind !SBRed.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_l. by_coind "CIH". auto.
    - destruct c. rewrite SBRed.transl_bind SBRed.transl_call HIRed.call. steps_l. 
      destruct (alist_find fn (HMod.fnsems md)) eqn:FIND; cycle 1.
      { ss. unfold triggerUB. ired. rewrite HIRed.bind_core. steps_l. ss. }
      destruct p. iApply isim_inline_tgt.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite HIRed.bind SBRed.transl_bind.
      iApply isim_bind; iSplitL.
      {
        iApply isim_RR_frame. 
        iSplitR; [iApply "CIH"|]. by_coind "CIH". eauto.  
      }
      unfold bindRR. iIntros (? ? ? ? ?) "(_ & % & IST)". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - depdes s.
      + rewrite !SBRed.transl_bind !SBRed.transl_put. des_ifs; cycle 1. 
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg SBRed.transl_bind SBRed.transl_put. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_l. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
      + rewrite !SBRed.transl_bind !SBRed.transl_get. des_ifs; cycle 1.
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg SBRed.transl_bind SBRed.transl_get. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_l. iDestruct "Ist" as "%". subst. 
        by_coind "CIH". eauto.
    - rewrite SBRed.transl_bind SBRed.transl_core HIRed.bind_core. depdes e.
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
  Qed.


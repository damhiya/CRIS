Require Import Common.
Require Import SMod2HMod SMod HMod Skeleton ITactics.
Require Import ISim CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import HModInline.

Set Implicit Arguments.

Section CANCEL.
  Context `{Σ: GRA}.
  Variable md: HMod.t.

  Lemma cancel_call_rev P
  :
    refines (md, P) (HModInline.inline md, P).
  Proof. 
    eapply closed_adequacy2.
    econs; ss. i. r.
    econs; ss; try refl; eauto.
    { i. rewrite List.map_map fst_map_snd. exists []. ss. }
    ii. rewrite alist_find_map_snd in FIND.
    destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk))) eqn:FINDT; ss.
    inv FIND. rename p into ft. esplits; eauto.
    ii. subst. destruct ft.
    assert(SCP := (HMod.modsem md sk).(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes FINDT in SCP.
    remember (HModSem.scopes (HMod.modsem md sk)) as scopeS. i.
    rename l into scopeT. 
    unfold wrap_elimI. s. unfold HModSem.sandbox_body, inline_hp_fun. s.
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
    - rewrite HModSB.transl_ret HIRed.ret. step. eauto.
    - rewrite HModSB.transl_tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_r. force_l. iFrame. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch. depdes s.
      + step. steps_r. by_coind "CIH". auto.
      + rewrite !HModSB.transl_bind !HModSB.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_r. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite HModSB.transl_bind HModSB.transl_call HIRed.call. steps_r. 
      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk))) eqn:FIND; cycle 1.
      { s. unfold triggerNB. ired. rewrite HIRed.bind_core. steps_r. ss. }
      destruct p. iApply isim_inline_src.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite HIRed.bind HModSB.transl_bind.
      iApply isim_bind; iSplitL.
      {
        iApply isim_RR_frame.
        iSplitR; [iApply "CIH"|]. by_coind "CIH". eauto.  
      }
      i. iIntros (? ? ? ? ?) "(_ & % & IST)". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - depdes s.
      + rewrite !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1. 
        { rewrite HIRed.bind_core. steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_put. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_r. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
      + rewrite !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { rewrite HIRed.bind_core. steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_get. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_r. iDestruct "Ist" as "%". subst. 
        by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core. depdes e.
      + steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. steps_r. instantiate (1:= q). by_coind "CIH". auto.
      + step. steps_r. by_coind "CIH". auto.
    Unshelve. all: try refl; eauto.
    {
      assert(SCP0 := (HMod.modsem md sk).(HModSem.well_scoped_fns) fn).
      rewrite/fnsems_scopes FIND in SCP0. eauto.
    }
  Qed.

End CANCEL.


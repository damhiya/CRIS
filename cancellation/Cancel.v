Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Behavior.
Require Import SMod2HMod HMod2Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import HPSim ISim.
Require Import ModSimFacts.
Require Import MainAdequacy CtxRefine CtxRefineFacts ClosedAdequacy.
Require Import Events SMod HMod Mod.
Require Import HModInline.

Set Implicit Arguments.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Lemma wrap_elimI_well_scoped
      ms fn sb
      (FIND: alist_find fn ms.(HModSem.fnsems) = Some sb)
    :
    HModSem.sandbox_body (wrap_elimI ms sb)
    = 
    inline_hp_fun (prog ms) (HModSem.sandbox_body sb).
  Proof.
    extensionality args. 
    unfold wrap_elimI, inline_hp_fbody. s.
    unfold HModSem.sandbox_body, inline_hp_fun. destruct sb. s.
    assert(SCP := ms.(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes FIND in SCP.
    
    (* remember (HModSem.scopes ms) as scopeS. i. *)
    rename l into scopeT. 
    apply bisim_is_eq. move scopeT at bottom.
    eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
    generalize (i args) as itr. clear FIND fn i args.
    revert_until ms. gcofix CIH. i.
    ides itr.
    - rewrite !HModSB.transl_ret HIRed.ret HModSB.transl_ret. gstep. econs. refl.
    - rewrite !HModSB.transl_tau HIRed.tau !HModSB.transl_tau. 
      gstep. econs. gstep. econs. gbase. eauto.
    - rewrite -bind_trigger !HModSB.transl_bind.
      destruct e.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind. 
        rewrite H !HModSB.transl_ag HIRed.bind_ag HModSB.transl_bind HModSB.transl_ag !bind_trigger.
        gstep. econs. i. r.
        rewrite HModSB.transl_tau. gstep. econs. gbase. eauto.
      }
      destruct p.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inl1 s))) = trigger s) by grind.
        rewrite H !HModSB.transl_sch HIRed.bind_sch HModSB.transl_bind HModSB.transl_sch !bind_trigger.
        gstep. econs. i. r.
        rewrite HModSB.transl_tau. gstep. econs. gbase. eauto.
      }
      destruct s.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inl1 c)))) = trigger c) by grind.
        destruct c. rewrite H.
        rewrite !HModSB.transl_call HIRed.call HModSB.transl_tau. s.
        gstep. econs.
        destruct (alist_find fn (HModSem.fnsems ms)) eqn: FIND.
        { 
          ired. assert (X:=@sandbox_well_scoped). 
          unfold HModSem.sandbox_body. destruct p. s.
          gbase.
          match goal with
          [|- _ _ (_ _ ?itr)] => assert (EX: exists itr', itr = HModSem.sandbox (HModSem.scopes ms) itr')
          end.
          {
            eexists. instantiate (1:= _ >>= _). 
            rewrite HModSB.transl_bind. f_equal.
            { 
              erewrite <-(@sandbox_well_scoped _ _ l); eauto. 
              assert(SCP0 := ms.(HModSem.well_scoped_fns)).
              specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0.
              eauto.
            }
            extensionality x.
            instantiate (1:= fun x => tau;;(_ x)). s.
            rewrite HModSB.transl_tau. do 2 f_equal.
            ired.
            erewrite <-(@sandbox_well_scoped _ _ scopeT); eauto. 
            instantiate (1:= fun x => HModSem.sandbox scopeT (k x)). 
            s. refl.
          }
          des. rewrite EX. eapply CIH. refl.
        }
        ired. unfold triggerNB. ired. 
        rewrite !HIRed.bind_core !HModSB.transl_bind HModSB.transl_core !bind_trigger.
        gstep. econs. i. ss.
      }
      destruct s.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inl1 p))))) = trigger p) by grind.
        destruct p; rewrite H.
        {
          rewrite !HModSB.transl_put. des_ifs.
          {
            rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_put. des_ifs; cycle 1.
            {
              exfalso. assert (existsb (eqb k0.1) (HModSem.scopes ms) = true).
              {
                eapply existsb_exists. eapply existsb_exists in Heq. des.
                esplits; eauto.
              }
              rewrite H0 in Heq0. ss.
            }
            rewrite !bind_trigger. gstep. econs. i.
            rewrite HModSB.transl_tau. gstep. econs. gbase; eauto. 
          }
          rewrite HIRed.bind_core HModSB.transl_bind HModSB.transl_core !bind_trigger. 
          gstep. econs. i. r. 
          rewrite HModSB.transl_tau. gstep. econs. gbase; eauto.
        }
        rewrite !HModSB.transl_get. des_ifs.
        {
          rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_get. des_ifs; cycle 1.
          {
            exfalso. assert (existsb (eqb k0.1) (HModSem.scopes ms) = true).
            {
              eapply existsb_exists. eapply existsb_exists in Heq. des.
              esplits; eauto.
            }
            rewrite H0 in Heq0. ss.
          }
          rewrite !bind_trigger. gstep. econs. i.
          rewrite HModSB.transl_tau. gstep. econs. gbase; eauto. 
        }
        rewrite HIRed.bind_core HModSB.transl_bind HModSB.transl_core !bind_trigger. 
        gstep. econs. i. r. 
        rewrite HModSB.transl_tau. gstep. econs. gbase; eauto.
      }
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inr1 c))))) = trigger c) by grind.
      rewrite H HModSB.transl_core HIRed.bind_core HModSB.transl_bind HModSB.transl_core !bind_trigger.
      gstep. econs. i. r.
      rewrite HModSB.transl_tau. gstep. econs. gbase; eauto.
    Unshelve.
      eapply eqit__mono; eauto.
  Qed.

  Definition bindRR {R} RR P : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp :=
    fun nths '(st0, ret0) '(st1, ret1) => (P ∗ RR nths (st0, ret0) (st1, ret1))%I.

  Definition IstRR {R} Ist : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp :=
    fun nths '(st0, ret0) '(st1, ret1) => (⌜ret0 = ret1⌝ ∗ Ist nths st0 st1)%I.

  Lemma isim_RR_frame
      fls flt my_tid is_closed r g nths
      {R} Ist (P: iProp)
      ps pt sti_src sti_tgt
    :
      (P ∗ @isim _ fls flt Ist my_tid is_closed r g R 
            (fun nths '(sts, vs) '(stt, vt) => ⌜vs = vt⌝ ∗ Ist nths sts stt)%I
            ps pt nths sti_src sti_tgt)  
      ⊢ isim fls flt Ist my_tid is_closed r g 
         (bindRR (IstRR Ist) P) ps pt nths sti_src sti_tgt.
  Proof.
    iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto.
  Qed.

  Definition progI fl : callE ~> itree hmodE :=
    fun _ '(Call fn args) =>
      lbody <- (alist_find fn fl)!;;
      lbody args.

End CANCEL.

Section CANCEL.
  Context `{Σ: GRA.t}.

  Variable md: HMod.t.

  Let sk: Sk.t := HMod.sk md.

  Lemma cancel_call
  :
    refines (HModAux.inline md, const(emp%I)) (md, const(emp%I)).
  Proof.
    eapply closed_adequacy.
    instantiate (1:= IstEq).
    econs; ss. i. r.
    econs; ss; try refl; eauto.
    { exists []. s. refl. }
    { i. rewrite map_map_compose fst_map_snd. exists []. ss. }
    ii. ss. exists (wrap_elimI (HMod.modsem md sk0) ft).
    esplits.
    { rewrite alist_find_map_snd FIND. ss. } 
    ii. subst. destruct ft.
    assert(SCP := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes FIND in SCP.
    rename l into scopeT. 
    unfold HModSem.sandbox_body, inline_hp_fun. s.
    unfold HModSem.sandbox_body, inline_hp_fun. s.
    generalize false at 1 as ps.
    generalize false at 1 as pt. intros pt ps.
    generalize (i y) as it. clear IN fn FIND i y NODD NODS.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert SCP. apply combine_quant.
    revert scopeT. apply combine_quant_dep.
    revert pt. apply combine_quant.
    revert ps. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    destruct a as [nths [ps [pt [scopeT [SCP [st_src [st_tgt it]]]]]]]. s.
    iIntros "(Ist & #CIH)".
    
    assert (CASE := case_itrH _ it); des; subst.
    - rewrite HModSB.transl_ret HIRed.ret. step. eauto.
    - rewrite HModSB.transl_tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch. depdes s.
      + step. steps_l. by_coind "CIH". auto.
      + rewrite !HModSB.transl_bind !HModSB.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_l. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite HModSB.transl_bind HModSB.transl_call HIRed.call. steps_l. 
      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FIND; cycle 1.
      { 
        iApply isim_call_none; ss.
        { rewrite alist_find_map_snd FIND. ss. }
        unfold triggerNB. steps_r. ss.
      }
      destruct p. iApply isim_inline_tgt.
      { rewrite alist_find_map_snd FIND. ss. }
      s. ired. rewrite HIRed.bind HModSB.transl_bind.
      (* iStopProof.
      match goal with
      | [|-context[(□ ?P)%I]] => remember (□P)%I
      end.
      rewrite Heqb. iIntros "[#CIH Ist]".  *)
      iApply isim_bind; iSplitL.
      {
        (* instantiate (1:= bindRR (IstRR IstEq0) b).  *)
        iApply isim_RR_frame. 
        (* instantiate(1:= b). rewrite Heqb.   *)
        iSplitR; [iApply "CIH"|]. by_coind "CIH". eauto.  
      }
      (* rewrite Heqb.  *)
      unfold bindRR. iIntros (? ? ? ? ?) "(_ & % & IST)". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - depdes s.
      + rewrite !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1. 
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_put. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_l. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
      + rewrite !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite HIRed.bind_pg HModSB.transl_bind HModSB.transl_get. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_l. iDestruct "Ist" as "%". subst. 
        by_coind "CIH". eauto.
    - rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core. depdes e.
      + steps_r. force_l. steps_l.
        instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. instantiate (1:= q).
        by_coind "CIH". auto.
      + step. steps_l. by_coind "CIH". auto.
    Unshelve. all: eauto.
    {
      assert(SCP0 := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
      specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0. eauto.
    }
  Qed.

  Lemma cancel_call_rev
  :
    refines (md, const(emp%I)) (HModAux.inline md, const(emp%I)).
  Proof. 
    eapply closed_adequacy.
    instantiate (1:= IstEq).
    econs; ss. i. r.
    econs; ss; try refl; eauto.
    { exists []. s. refl. }
    { i. rewrite map_map_compose fst_map_snd. exists []. ss. }
    ii. rewrite alist_find_map_snd in FIND.
    destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FINDT; ss.
    inv FIND. rename p into ft. esplits; eauto.
    ii. subst. destruct ft.
    assert(SCP := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes FINDT in SCP.
    remember (HModSem.scopes (HMod.modsem md sk0)) as scopeS. i.
    rename l into scopeT. 
    unfold wrap_elimI. s. unfold HModSem.sandbox_body, inline_hp_fun. s.
    generalize false at 1 as ps.
    generalize false at 1 as pt. intros pt ps.
    generalize (i y) as it. clear IN fn FINDT i y NODD NODS.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert SCP. apply combine_quant.
    revert scopeT. apply combine_quant_dep.
    revert pt. apply combine_quant.
    revert ps. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    destruct a as [nths [ps [pt [scopeT [SCP [st_src [st_tgt it]]]]]]]. s.

    iIntros "(Ist & #CIH)".

    assert (CASE := case_itrH _ it); des; subst.
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
      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FIND; cycle 1.
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
      assert(SCP0 := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
      specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0. eauto.
    }
  Qed.

End CANCEL.
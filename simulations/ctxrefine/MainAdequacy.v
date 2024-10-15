Require Import Coqlib AList.
Require Export sflib.
Require Export ITreelib.
Require Import Any.

Require Import IRed.
Require Import STS.
Require Import Behavior Skeleton.
Require Import PCM IPM.

Require Import ModSim ModSimFacts.
Require Import HPSim HPSimFacts.

Require Import HMod Mod HMod2Mod Events.
Require Import SubPerm.

Require Import ISim ISimFacts.
Require Import CtxRefine.
Require Import ITactics.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section AUX.

  Context `{Σ: GRA.t}.

  Lemma alist_upd_fst_in {V} a (k: key) (v: V) l
    (IN: In a (map (fst <*> fst) l))
    :
    In a (map (fst <*> fst) (alist_upd k v l)).
  Proof.
    unfold alist_upd in *.
    induction l; ss; i; rewrite eq_rel_dec_correct; des_ifs; ss; des; eauto.
  Qed.
  
  Lemma sandbox_well_scoped {A}
        scopes0 scopes1 (itr: itree hmodE A) 
        (SCP: incl scopes0 scopes1)
    :
      HModSem.sandbox scopes1 (HModSem.sandbox scopes0 itr) = HModSem.sandbox scopes0 itr.
  Proof.
    apply bisim_is_eq.
    revert_until Σ. ginit. gcofix CIH. i.
    ides itr.
    - rewrite! HModSB.transl_ret. gstep. econs. eauto.
    - rewrite! HModSB.transl_tau. gstep. econs. gbase. eauto.
    - rewrite <- bind_trigger. rewrite! HModSB.transl_bind.
      destruct e.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind.
        rewrite H.
        rewrite! HModSB.transl_ag. rewrite! bind_trigger.
        gstep. econs. i. r. gbase. eauto.
      }
      destruct p.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inl1 s))) = trigger s) by grind.
        rewrite H. rewrite! HModSB.transl_sch. rewrite! bind_trigger.
        gstep. econs. i. r. gbase. eauto.     
      }
      destruct s.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inl1 c)))) = trigger c) by grind.
        rewrite H. rewrite! HModSB.transl_call. rewrite! bind_trigger.
        gstep. econs. i. r. gbase. eauto.     
      }
      destruct s.
      {
        assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inl1 p))))) = trigger p) by grind.
        rewrite H. destruct p.
        - rewrite! HModSB.transl_put. des_ifs.
          + rewrite HModSB.transl_put. des_ifs. 
            * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
            * exfalso. eapply existsb_exists in Heq. des.
              eapply SCP in Heq. 
              assert (XEQ:=existsb_exists).
              hdes. rewrite XEQ1 in Heq0; ss; eauto.
          + rewrite HModSB.transl_core.
            rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
        - rewrite! HModSB.transl_get. des_ifs.
          + rewrite! HModSB.transl_get. des_ifs.
            * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
            * exfalso. eapply existsb_exists in Heq. des.
              eapply SCP in Heq. 
              assert (XEQ:=existsb_exists).
              hdes. rewrite XEQ1 in Heq0; ss; eauto.
          + rewrite HModSB.transl_core.
            rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
      }
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inr1 c))))) = trigger c) by grind.
      rewrite H. rewrite! HModSB.transl_core. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.
  Qed.

  Lemma inv_sandbox_tau {X}
        scp (itr: itree hmodE X)
        (SB: HModSem.sandbox scp (tau;; itr) = tau;; itr)
      :
        HModSem.sandbox scp itr = itr.
  Proof.
    rewrite HModSB.transl_tau in SB. inv SB.
    rewrite sandbox_well_scoped; refl.
  Qed.

  Lemma inv_sandbox_core {X Y}
        x scp (ktr: X -> itree hmodE Y) (c: coreE X)
        (SB: HModSem.sandbox scp (trigger c >>= ktr) = trigger c >>= ktr)
      :
        HModSem.sandbox scp (ktr x) = ktr x.
  Proof.
    rewrite/__ HModSB.transl_bind HModSB.transl_core in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  Qed.

  Lemma inv_sandbox_call {X Y}
        x scp (ktr: X -> itree hmodE Y) (c: callE X)
        (SB: HModSem.sandbox scp (trigger c >>= ktr) = trigger c >>= ktr)
      :
        HModSem.sandbox scp (ktr x) = ktr x.
  Proof.
    destruct c.
    rewrite/__ HModSB.transl_bind HModSB.transl_call in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  Qed.

  Lemma inv_sandbox_pg {X Y}
        x scp (ktr: X -> itree hmodE Y) (pg: pgE X)
        (SB: HModSem.sandbox scp (trigger pg >>= ktr) = trigger pg >>= ktr)
      :
        HModSem.sandbox scp (ktr x) = ktr x.
  Proof.
    destruct pg.
    { 
      rewrite/__ HModSB.transl_bind HModSB.transl_put in SB.
      des_ifs; rewrite! bind_trigger in SB; inv SB.
      eapply inj_pair2, equal_f in H0. eauto.
    }
    { 
      rewrite/__ HModSB.transl_bind HModSB.transl_get in SB.
      des_ifs; rewrite! bind_trigger in SB; inv SB.
      eapply inj_pair2, equal_f in H0. eauto.
    }
  Qed.
  Lemma inv_sandbox_ag {X}
        scp (ktr: unit -> itree hmodE X) (ag: agE unit)
        (SB: HModSem.sandbox scp (trigger ag >>= ktr) = trigger ag >>= ktr)
      :
        HModSem.sandbox scp (ktr tt) = ktr tt.
  Proof.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  Qed.    

  Lemma alist_upd_not_exists
        k v st scopes
        (NOTEXT: existsb (String.eqb k.1) scopes = false)
        (INSCP: incl (state_scopes st) scopes) 
      :
        alist_upd k v st = st.
  Proof.
    eapply alist_upd_not_in. 
    ii. eapply in_map with (f:=fst) in H. 
    rewrite map_map in H. eapply INSCP in H.
    assert (∃x, In x scopes /\ String.eqb k.1 x = true).
    { exists k.1. esplits; [eauto|]. eapply String.eqb_refl. }
    eapply existsb_exists in H0. clarify.
  Qed.

  Lemma alist_find_existsb
        st scopes k v 
        (INSCP: incl (state_scopes st) scopes) 
        (FIND: alist_find k st = Some v)
      :
        existsb (String.eqb k.1) scopes = true.
  Proof.
    eapply existsb_exists.
    eapply alist_find_fst_some, in_map in FIND.
    rewrite map_map in FIND.
    exists k.1. esplits; eauto. eapply String.eqb_refl.
  Qed.

  Lemma alist_find_not_exists
        st scopes k
        (INSCP: incl (state_scopes st) scopes) 
        (NOTEXT: existsb (String.eqb k.1) scopes = false)
      :
        alist_find k st = None.
  Proof.
    eapply alist_find_fst_notin.
    ii. eapply in_map with (f:=fst) in H. 
    rewrite map_map in H. eapply INSCP in H.
    assert (∃x, In x scopes /\ String.eqb k.1 x = true).
    { exists k.1. esplits; [eauto|]. eapply String.eqb_refl. }
    eapply existsb_exists in H0. clarify.
  Qed.

  Lemma alist_find_exists_l
        st ctx scopeS scopeC (k: key)
        (DISJ: NoDup (scopeS ++ scopeC))
        (INS: incl (state_scopes st) scopeS)
        (INC: incl (state_scopes ctx) scopeC)
        (EXT: existsb (String.eqb k.1) scopeS = true)
      :
        alist_find k (st ++ ctx) = alist_find k st.
  Proof.
    rewrite alist_find_app_o. des_ifs.
    eapply alist_find_fst_notin. ii.
    eapply existsb_exists in EXT. des.
    eapply NoDup_app_disjoint; eauto.
    eapply INC. unfold state_scopes. rewrite <- map_map. 
    eapply in_map with (f:=fst) in H.
    eapply String.eqb_eq in EXT0. subst. eauto.
  Qed.

  Lemma wf_eq_solve (a b: Σ) :
    URA.wf a -> a = b -> URA.wf b.
  Proof.
    i. rewrite <- H0. eauto.
  Qed.

  Lemma wf_inv_l ms0 ms1
        (WF: HModSem.wf (HModSem.add ms0 ms1))
      :
        HModSem.wf ms0.
  Proof.
    inv WF; ss. rewrite map_app in wf_fns. 
    econs; eauto using nodup_app_l.
  Qed.

  Lemma sk_equiv_ctx sk0 sk1 ctx
    (EQV: Sk.equiv sk0 sk1)
  :
    Sk.equiv (Sk.add sk0 ctx) (Sk.add sk1 ctx).
  Proof.
    eapply Permutation_app_tail. eauto.
  Qed.

End AUX.


Section AUX.
  Context `{Σ: GRA.t}.

  Ltac hstep := guclo hpsimC_spec; econs; econs; eauto; econs; eauto.

  Lemma hpsim_ctx
    fnsems_src fnsems_tgt fl_src fl_tgt fl_ctx Ist my_tid
    scopes scopeC
    (FLS: fl_src = (List.map (map_snd HModSem.sandbox_body) fnsems_src))
    (FLT: fl_tgt = (List.map (map_snd HModSem.sandbox_body) fnsems_tgt))
    (WS: ∀ (fn: gname) p (IN: alist_find fn fnsems_src = Some p), incl p.1 scopes)
    (WT: ∀ (fn: gname) p (IN: alist_find fn fnsems_tgt = Some p), incl p.1 scopes)
    (DISJ: List.NoDup (scopes ++ scopeC))

    ps pt nths st_src st_tgt st_ctx itr_src itr_tgt fmr
    (SCPS: incl (state_scopes st_src) scopes)
    (SCPT: incl (state_scopes st_tgt) scopes)
    (SCPC: incl (state_scopes st_ctx) scopeC)
    (ITRS: HModSem.sandbox scopes itr_src = itr_src)
    (ITRT: HModSem.sandbox scopes itr_tgt = itr_tgt)
    (SIM: hpsim_body fl_src fl_tgt Ist my_tid ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
    :
    hpsim_body (fl_src ++ fl_ctx) (fl_tgt ++ fl_ctx) 
    (IstProd0 (IstSB0 scopes Ist) (IstSB0 scopeC IstEq0)) my_tid
    ps pt nths (st_src ++ st_ctx, itr_src) (st_tgt ++ st_ctx, itr_tgt) fmr.
  Proof.
    guardH FLS. guardH FLT.
    ginit. s. revert_until DISJ. gcofix CIH. i.
    exploit SIM; s; i.
    { eapply nodup_app_l. rewrite <- map_app. eauto. }
    { eapply nodup_app_l. rewrite <- map_app. eauto. }
    { subst. eapply nodup_app_l. rewrite <- map_app. eauto. }
    { subst. eapply nodup_app_l. rewrite <- map_app. eauto. }
    clear SIM. rename x0 into SIM.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before CIH. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo hpsim_wfC_spec. econs. i. 
    exploit IN; i; des; eauto. clear IN.
    destruct x0; i; des; inv Heqp; try inv Heqp0.
    - hstep. iIntros "H". iPoseProof (RET with "H") as ">[% H]".
      iModIntro. iSplit; eauto. iExists st_src, st_tgt, st_ctx, st_ctx.
      iSplit; eauto. iFrame. eauto.
    - hstep.
      { 
        instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iExists st_src, st_tgt, st_ctx, st_ctx.
        iSplit; eauto. iFrame. eauto.
      }
      i. guclo hpsim_wfC_spec. econs. i.
      eapply iProp_sepconj_upd in INV0. des.
      uiprop in INV1. exploit (INV1 rp).
      { eapply own_wf in INV0; eauto. eapply URA.wf_mon. eauto. }
      { refl. }
      clear INV1. intros INV1.
      unfold IstProd, IstProd0 in INV1.
      uiprop in INV1. 
      repeat (rr in INV1; unseal "iProp"; des). ss. des. subst. 
      repeat (rr in INV3; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV6; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV1; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV3; unseal "iProp"; des). ss. des. subst.

      eapply iProp_Own in INV5.
      (* 
        new states after call should maintain the scope of previous states. 
        ctx state should maintain its own scope.
      *)
      eapply K; try refl; eauto using inv_sandbox_call; cycle 3.
      {
        uiprop in INV5. exploit (INV5 a0); try refl.
        { 
          eapply URA.wf_mon with (b:= a ⋅ a1 ⋅ b ⋅ rq). 
          eapply own_wf in INV0; eauto.
          eapply wf_eq_solve; [eapply INV0|r_solve].
        }
        clear INV5. intros INV5.
        repeat (rr in INV5; unseal "iProp"; des). ss. des. subst.
        rr in INV3; unseal "iProp"; des. ss. 
      }
      {
        uiprop in INV5. exploit (INV5 a0); try refl.
        { 
          eapply URA.wf_mon with (b:= a ⋅ a1 ⋅ b ⋅ rq). 
          eapply own_wf in INV0; eauto.
          eapply wf_eq_solve; [eapply INV0|r_solve].
        }
        clear INV5. intros INV5.
        repeat (rr in INV5; unseal "iProp"; des). ss. des. subst.
        rr in INV3; unseal "iProp"; des. ss. 
      }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      iIntros "H". iPoseProof (INV0 with "H") as ">H".
      iDestruct "H" as "[[_ [A _]] Q]".
      iPoseProof (INV2 with "Q") as "FR".
      iPoseProof (INV5 with "A") as "(% & IST)".
      iFrame; eauto.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core. 
    - hstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! HModSB.transl_bind.
      move FLS at bottom. move FUN at bottom.
      rewrite FLS in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs.
      unfold HModSem.sandbox_body.
      rewrite sandbox_well_scoped; eauto.
      f_equal. extensionalities.
      rewrite/__ !HModSB.transl_bind !HModSB.transl_ret !HModSB.transl_tau !HModSB.transl_ret.
      f_equal. extensionalities. eapply inv_sandbox_call; eauto. 

    - hstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! HModSB.transl_bind.
      move FLT at bottom. move FUN at bottom.
      rewrite FLT in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs.
      unfold HModSem.sandbox_body.
      rewrite sandbox_well_scoped; eauto.
      f_equal. extensionalities.
      rewrite/__ !HModSB.transl_bind !HModSB.transl_ret !HModSB.transl_tau !HModSB.transl_ret.
      f_equal. extensionalities. eapply inv_sandbox_call; eauto. 
    - hstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - hstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. eapply K; try refl; eauto using inv_sandbox_core.
    - assert (H1:= ITRS).
      rewrite /__ -ITRS HModSB.transl_bind HModSB.transl_put. des_ifs.
      + hstep.
        assert (UPD: alist_upd k v (st_src ++ st_ctx) = alist_upd k v st_src ++ st_ctx).
        { 
          move SCPS at bottom. move SCPC at bottom. 
          eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0.
          rewrite alist_upd_not_tail; eauto.
          ii. eapply NoDup_app_disjoint; eauto.
          eapply in_map with (f:=fst) in H2.
          rewrite map_map in H2. eapply SCPC in H2.
          rewrite <- Heq0. eauto.
        }
        rewrite UPD. eapply K; try refl; eauto.
        { rewrite state_scopes_update. eauto. }
        { eapply sandbox_well_scoped. refl. }
        { rewrite <-UPD. eapply alist_upd_nodup. eauto. }
        { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
      + hstep. eapply K; try refl; eauto.
        { eapply sandbox_well_scoped. refl. }
        { 
          f_equal. 
          { eapply alist_upd_not_exists; eauto. }
          { symmetry. eapply inv_sandbox_pg. eauto. }
        }

    - assert (H1:=ITRT).
      rewrite/__ -ITRT HModSB.transl_bind HModSB.transl_put. des_ifs.
      + hstep.
        assert (UPD: alist_upd k v (st_tgt ++ st_ctx) = alist_upd k v st_tgt ++ st_ctx).
        {
          move SCPS at bottom. move SCPC at bottom. 
          eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0.
          eapply alist_upd_not_tail. eauto.
          ii. eapply NoDup_app_disjoint; eauto.
          eapply in_map with (f:=fst) in H2.
          rewrite map_map in H2. eapply SCPC in H2.
          rewrite <- Heq0. eauto.  
        }
        rewrite UPD. eapply K; try refl; eauto.
        { rewrite state_scopes_update. eauto. }
        { eapply sandbox_well_scoped. refl. }
        { rewrite <-UPD. eapply alist_upd_nodup. eauto. }
        { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
      + rewrite/__ HModSB.transl_bind HModSB.transl_put Heq !bind_trigger in H1.
      exfalso. ss.   

    - assert (H1:=ITRS). 
      rewrite/__  -ITRS HModSB.transl_bind HModSB.transl_get. des_ifs.
      + hstep. eapply K; try refl; eauto.
        { eapply sandbox_well_scoped. refl. }
        erewrite alist_find_exists_l; eauto.
        repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
      + hstep. eapply K; try refl; eauto.
        { eapply sandbox_well_scoped. refl. }
        repeat f_equal. symmetry. unfold or_else. 
        erewrite alist_find_not_exists; eauto.
        eapply inv_sandbox_pg; eauto.

    - assert (H1:=ITRT). 
      rewrite/__  -ITRT HModSB.transl_bind HModSB.transl_get. des_ifs.
      + hstep. eapply K; try refl; eauto.
        { eapply sandbox_well_scoped. refl. }
        erewrite alist_find_exists_l; eauto.
        repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
      + rewrite/__ HModSB.transl_bind HModSB.transl_get Heq !bind_trigger in H1.
        exfalso. ss.

    - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
    - hstep. eapply K; try refl; eauto.
      + rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRS.
        depdes ITRS. eapply equal_f in x. eauto.
      + rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRT.
        depdes ITRT. eapply equal_f in x. eauto.
    - hstep.
      { 
        instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iExists st_src, st_tgt, st_ctx, st_ctx.
        iSplit; eauto. iFrame. eauto.
      }
      i. guclo hpsim_wfC_spec. econs. i.
      eapply iProp_sepconj_upd in INV0. des.
      uiprop in INV1. exploit (INV1 rp).
      { eapply own_wf in INV0; eauto. eapply URA.wf_mon. eauto. }
      { refl. }
      clear INV1. intros INV1.
      unfold IstProd, IstProd0 in INV1.
      uiprop in INV1. 
      repeat (rr in INV1; unseal "iProp"; des). ss. des. subst. 
      repeat (rr in INV3; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV6; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV1; unseal "iProp"; des). ss. des. subst.
      repeat (rr in INV3; unseal "iProp"; des). ss. des. subst.

      eapply iProp_Own in INV5.
      (* 
        new states after call should maintain the scope of previous states. 
        ctx state should maintain its own scope.
      *)
      eapply K; try refl; eauto using inv_sandbox_call; cycle 3.
      {
        uiprop in INV5. exploit (INV5 a0); try refl.
        { 
          eapply URA.wf_mon with (b:= a ⋅ a1 ⋅ b ⋅ rq). 
          eapply own_wf in INV0; eauto.
          eapply wf_eq_solve; [eapply INV0|r_solve].
        }
        clear INV5. intros INV5.
        repeat (rr in INV5; unseal "iProp"; des). ss. des. subst.
        rr in INV3; unseal "iProp"; des. ss. 
      }
      {
        uiprop in INV5. exploit (INV5 a0); try refl.
        { 
          eapply URA.wf_mon with (b:= a ⋅ a1 ⋅ b ⋅ rq). 
          eapply own_wf in INV0; eauto.
          eapply wf_eq_solve; [eapply INV0|r_solve].
        }
        clear INV5. intros INV5.
        repeat (rr in INV5; unseal "iProp"; des). ss. des. subst.
        rr in INV3; unseal "iProp"; des. ss. 
      }
      { rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRS.
        depdes ITRS. eapply equal_f in x. eauto. }
      { rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRT.
        depdes ITRT. eapply equal_f in x. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      iIntros "H". iPoseProof (INV0 with "H") as ">H".
      iDestruct "H" as "[[_ [A _]] Q]".
      iPoseProof (INV2 with "Q") as "FR".
      iPoseProof (INV5 with "A") as "(% & IST)".
      iFrame; eauto.

    - hstep. eapply K; try refl; eauto.
      rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRS.
      depdes ITRS. eapply equal_f in x. eauto.
      
    - hstep. eapply K; try refl; eauto.
      rewrite/__ HModSB.transl_bind HModSB.transl_sch !bind_trigger in ITRT.
      depdes ITRT. eapply equal_f in x. eauto.
      
    - gstep. econs. econs. econs; eauto. econs; eauto. 
      gbase. pclearbot. eapply CIH; try refl; eauto.
      ii. eauto.
  Qed.

  Lemma isim_ctx
    fs ft ms mt ctx Ist fn
    (WFS: HModSem.wf (HModSem.add ms ctx))
    (WFT: HModSem.wf (HModSem.add mt ctx))
    (FINDS: alist_find fn (HModSem.fnsems ms) = Some fs)
    (FINDT: alist_find fn (HModSem.fnsems mt) = Some ft)
    (SCOPES: sub_perm (HModSem.scopes mt) (HModSem.scopes ms))
    (NODUPFS: NoDup (map fst (HModSem.fnsems ms ++ HModSem.fnsems ctx)))
    (NODUPFT: NoDup (map fst (HModSem.fnsems mt ++ HModSem.fnsems ctx)))
    (IMON: ∀ nths0 nths', nths0 <= nths' → ∀ st_src st_tgt,
           Ist nths0 st_src st_tgt -∗ Ist nths' st_src st_tgt)
    (SIM: isim_fsem
       (map (map_snd HModSem.sandbox_body) (HModSem.fnsems ms))
       (map (map_snd HModSem.sandbox_body) (HModSem.fnsems mt))
       Ist
       (HModSem.sandbox_body fs)
       (HModSem.sandbox_body ft))
    :
      isim_fsem
        (map (map_snd HModSem.sandbox_body)
           (HModSem.fnsems ms ++ HModSem.fnsems ctx))
        (map (map_snd HModSem.sandbox_body)
           (HModSem.fnsems mt ++ HModSem.fnsems ctx))
        (IstProd0 (IstSB0 (HModSem.scopes ms) Ist) (IstSB0 (HModSem.scopes ctx) IstEq0))
        (HModSem.sandbox_body fs) (HModSem.sandbox_body ft).
  Proof.
    ii. specialize (SIM x y H). subst.
    iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & IST) & %)". des. subst.
    rewrite map_app in *. 
    assert (NODA := NODS). assert (NODB := NODD). assert (NODC:= NODS).
    eapply nodup_app_l in NODA, NODB. eapply nodup_app_r in NODC.
    specialize (SIM my_tid nths st_srcL st_tgtL IMON NODA NODB).
    rewrite <- map_app in *.
    iPoseProof (SIM with "IST") as "SIM".
    iStopProof. Local Transparent isim.
    uiprop. i.
    gfinal. right. eapply paco8_mon_bot; eauto.
    rewrite! List.map_app.
    assert (EQ: (λ x, (map_snd HModSem.sandbox_body x).1) = @fst string _).
    { extensionalities. destruct H2. eauto. }
    eapply hpsim_ctx; eauto; ss; cycle 6.
    { rewrite/__ -map_app map_map EQ. eauto. }
    { rewrite/__ -map_app map_map EQ. eauto. }
    { 
      ii. eapply ms.(HModSem.well_scoped_fns).
      unfold fnsems_scopes. rewrite IN. ss.
    }
    {
      i. etrans; cycle 1.
      { eapply sub_perm_incl; eauto. }
      ii. eapply mt.(HModSem.well_scoped_fns).
      unfold fnsems_scopes. rewrite IN. ss.
    }
    { eapply WFS. }
    { 
      eapply sandbox_well_scoped. ii.
      eapply ms.(HModSem.well_scoped_fns). 
      unfold fnsems_scopes. rewrite FINDS. ss.
    }
    { 
      eapply sandbox_well_scoped. etrans; cycle 1.
      { eapply sub_perm_incl; eauto. }
      ii. eapply mt.(HModSem.well_scoped_fns). 
      unfold fnsems_scopes. rewrite FINDT. ss.
    }
    ginit. i. eapply gpaco8_mon; eauto using iunlift_ibot.
  Qed.

  Lemma hmod_sim_ctx (ms mt ctx: HMod.t) IC Ist
    (SIM: HSim.t ms mt IC Ist)
    :
    HSim.t (ms ★ ctx) (mt ★ ctx) IC 
      (fun sk => IstProd0 (IstSB0 (HMod.modsem ms sk).(HModSem.scopes) (Ist sk))
                          (IstSB0 (HMod.modsem ctx sk).(HModSem.scopes) IstEq0)).
  Proof.
    inv SIM.
    econs; cycle 1.
    { ss. r. eapply sk_equiv_ctx. eauto. }
    i. hexploit sim_modsem; eauto.
    { 
      r in SKINCL. ii. hexploit (SKINCL a); eauto.
      ss. eapply in_or_app; eauto.
    }
    i. inv H. econs; ss.
    { 
      iIntros "H". iPoseProof (sim_initial with "H") as "H".
      unfold IstProd. iExists _, _, _, _. iFrame. iPureIntro.
      esplits; eauto; try eapply HModSem.well_scoped_init.
      etrans; [eapply HModSem.well_scoped_init|].
      eapply sub_perm_incl, sim_scopes.
    }
    { i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)". des; subst.
      iPoseProof ((sim_mon _ _ LE) with "H") as "H".
      repeat iExists _. iFrame. iPureIntro. esplits; eauto.
    }
    { eapply sub_perm_cancel_tail. eauto. }
    { rewrite! app_length. nia. }
    {
      i. rewrite map_app in *. eapply in_app_or in IN.
      des; eapply in_or_app; eauto.  
    }
    r. i. ss. rewrite alist_find_app_o in FIND. des_ifs.
    {
      (* find in src/tgt module *)
      hexploit sim_fnsems; i.
      { eapply alist_find_fst_some. eauto. }
      r in H. hexploit H; eauto; i.
      { 
        inv WFS; ss. econs.  
        { rewrite map_app in wf_fns. eapply nodup_app_l. eauto. }
        { eapply nodup_app_l; eauto. }
      }
      { 
        inv WFT; ss. econs.  
        { rewrite map_app in wf_fns. eapply nodup_app_l. eauto. }
        { eapply nodup_app_l; eauto. }
      }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      des. esplits.
      { rewrite alist_find_app_o. des_ifs. }
      eapply isim_ctx; eauto.
    } 
    {
      destruct fs as [scp itr]. esplits; ss.
      { rewrite alist_find_app_o. des_ifs; eauto.
        exfalso.
        eapply alist_find_fst_some, hssim_match, alist_find_fst_in in Heq0.
        - des. rewrite Heq in Heq0. ss.
        - econs; eauto.
        - rewrite map_app in NODUPFS. eapply nodup_app_l. eauto.
      }
      inv WFS. eapply isim_reflR; ss; i; eauto.
      - replace scp with (fnsems_scopes fn (HMod.modsem ctx sk).(HModSem.fnsems)).
        { eapply (HMod.modsem ctx sk).(HModSem.well_scoped_fns). }
        { unfold fnsems_scopes. des_ifs. }
      - iIntros "%". des; subst; eauto.
      - iIntros "%". des; subst; eauto. iPureIntro.  esplits; eauto.
        + rewrite state_scopes_update. eauto.
        + rewrite state_scopes_update. eauto.
    }
  Qed.

End AUX.

Section ADEQUACY.

  Context `{Σ: GRA.t}.

  Theorem main_adequacy (ms mt: HMod.t) IC Ist
    (SIM: HSim.t ms mt IC Ist)
    :
    ctx_refines (ms,IC) (mt, const(emp%I)).
  Proof.
    ii. s. split.
    { s. eapply sk_equiv_ctx. apply SIM. }

    destruct ctx as [ctx cond].
    assert (SIMC := SIM).
    ii. eapply hmod_sim_ctx with (ctx := ctx) in SIMC.
    hexploit (HSim.sim_modsem SIMC); eauto.
    { eapply Sk.equiv_incl in EQV. etrans; eauto. refl. }
    i. ss.

    eapply iProp_sepconj in SRC; eauto. des.
    esplits. 
    { rewrite SRC in WFR. rewrite URA.add_comm in WFR. eapply URA.wf_mon. eauto. }
    { 
      eapply iProp_Own in SRC1. iIntros "H".
      iPoseProof (SRC1 with "H") as "H". iFrame. eauto.
    }
    { eapply hssim_wf; eauto. }
    ii. subst. eapply adequacy_modsem, PR.
    - eapply hssim_adequacy; eauto.
      eapply hssim_wf; eauto.
    - inv WFM. econs. ss. unfold map_snd.
      rewrite !List.map_map. eapply eq_ind; [apply wf_fns|].
      f_equal. extensionalities. destruct H0. ss.
  Qed.

End ADEQUACY.

Section COMM.

  Context `{Σ: GRA.t}.

  Definition perm_Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ l0 l1 => ⌜l0 ≡ₚ l1⌝%I.  
  
  Lemma alist_upd_perm {K V} l0 l1 `{Dec K} (k: K) (v: V)
        (ND: List.NoDup (map fst l0))
        (PERM: l0 ≡ₚ l1)
      :
        alist_upd k v l0 ≡ₚ alist_upd k v l1.
  Proof.
    destruct (classic (In k (map fst l0))); cycle 1.
    {
      rewrite! alist_upd_not_in; eauto. ii.
      eapply H0. eapply Permutation_in; cycle 1; eauto.
      eapply Permutation_map. symmetry. eauto.
    }
    assert (List.NoDup (map fst l1)).
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

  Lemma alist_permutation_find K `{Dec K} V (l0 l1: alist K V)
        (ND: List.NoDup (List.map fst l0))
        (PERM: Permutation l0 l1)
        k
    :
      alist_find k l0 = alist_find k l1.
  Proof.
    revert ND k. induction PERM; ss.
    { i. inv ND. destruct x. rewrite eq_rel_dec_correct. des_ifs. et. }
    { i. inv ND. inv H3. destruct x, y. rewrite eq_rel_dec_correct. des_ifs.
      rewrite eq_rel_dec_correct in *. des_ifs. f_equal. exfalso. eapply H2. ss. auto. }
    { i. rewrite IHPERM1; auto. rewrite IHPERM2; auto.
      eapply Permutation_NoDup; [|apply ND].
      eapply Permutation_map. auto.
    }
  Qed.

  Lemma alist_find_comm {K V} `{Dec K}
        (l0 l1: list (K*V)) fn f
        (NODUP: List.NoDup (map fst (l0 ++ l1)))
        (FIND: alist_find fn (l0 ++ l1) = Some f)
      :
        alist_find fn (l1 ++ l0) = Some f.
  Proof.
    rewrite alist_find_app_o in *. des_ifs.
    eapply alist_find_fst_some in Heq, Heq0.
    rewrite map_app in NODUP.
    exfalso.
    eapply NoDup_app_disjoint in NODUP; eauto.
  Qed.

  Lemma hmod_add_scopes sk md0 md1:
    HMod.scopes (md0 ★ md1) sk = HMod.scopes md0 sk ++ HMod.scopes md1 sk.
  Proof. ss. Qed.

  Lemma hmod_add_comm
    ms0 ms1
    :
    HSim.t (ms0 ★ ms1) (ms1 ★ ms0) (const(emp%I))
      (fun sk => IstSB0 (HMod.scopes (ms0 ★ ms1) sk) perm_Ist).
  Proof.
    econs; cycle 1.
    { rr. eapply Permutation_app_comm. }
    i. econs; ss.
    {
      iIntros "_". iPureIntro. esplits.
      { eapply (HMod.modsem ms0 ★ ms1 sk).(HModSem.well_scoped_init). }
      { ii. eapply (HMod.modsem ms0 ★ ms1 sk).(HModSem.well_scoped_init); ss.
        unfold state_scopes in *. rewrite map_app in *.
        eapply in_app_or in H. eapply in_or_app. des; eauto.
      }
      { eapply Permutation.Permutation_app_comm. }
    }
    {
      r. exists []. rewrite app_nil_l.
      eapply Permutation.Permutation_app_comm.
    }
    { rewrite! app_length. nia. }
    {
      i. rewrite map_app in *. eapply in_app_iff, Logic.or_comm.
      eapply in_app_iff. eauto.
    }

    ii. eapply alist_find_comm in FIND; cycle 1. 
    { inv WFT; ss. }
    esplits; eauto.

    (* simulation *)
    ii. subst. destruct fs. unfold HModSem.sandbox_body. s.
    generalize (i y) as it. clear FIND i y.
    revert NODD. apply combine_quant.
    revert NODS. apply combine_quant.
    revert st_tgt. apply combine_quant.
    revert st_src. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.
    destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
    iIntros "(#(_ & CIH) & IST)".
    assert (CASE := case_itrH _ it); des; subst.
    - step. iFrame. eauto.
    - steps_l. steps_r. by_coind "CIH". eauto.
    - steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - steps_r. force_l. iFrame. by_coind "CIH". eauto.
    - destruct s.
      + step. by_coind "CIH". eauto.
      + yield "IST"; eauto. by_coind "CIH". eauto.
      + steps_l. steps_r. by_coind "CIH". eauto.
    - destruct c. call "IST"; eauto. by_coind "CIH". eauto.
    - depdes s.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1.
        { steps_r. force_l. instantiate (1:=q). by_coind "CIH". eauto. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        by_coind "CIH". iClear "CIH". unfold perm_Ist. 
        iDestruct "IST" as "%". des. 
        iPureIntro. rewrite !state_scopes_update. esplits; eauto. 
        eapply alist_upd_perm; eauto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { steps_r. force_l. instantiate (1:=q). by_coind "CIH". eauto. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
        iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝)%I with "[IST]" as "%".
        { iDestruct "IST" as "%". des. iPureIntro.
          eapply alist_permutation_find; eauto. }
        rewrite H. by_coind "CIH". eauto.
    - destruct e.
      + steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto. 
      + steps_l. force_r. instantiate (1:= q). by_coind "CIH". eauto. 
      + step. by_coind "CIH". eauto. 
    Unshelve. all: eauto. 
    { eapply alist_upd_nodup. eauto. }
    { eapply alist_upd_nodup. eauto. }
  Qed.

End COMM.

Require Import Common.
Require Import Mod HMod.
Require Import ModSim ModSimFacts HPSim HPSimFacts ISim ISimInit ISimFacts.
Require Import CtxRefine.

Set Implicit Arguments.

(* AUX *)

Lemma alist_upd_fst_in {V} a (k : key) (v : V) l
    (IN : In a (List.map (fst ∘ fst) l)) :
  In a (List.map (fst ∘ fst) (alist_upd k v l)).
Proof.
  unfold alist_upd in *.
  induction l; ss; i; rewrite eq_rel_dec_correct; des_ifs; ss; des; eauto.
Qed.

Lemma sandbox_well_scoped `{Σ: GRA} {A} scopes0 scopes1 (itr : itree hmodE A) 
    (SCP : incl scopes0 scopes1) :
  HMod.sandbox scopes1 (HMod.sandbox scopes0 itr) = HMod.sandbox scopes0 itr.
Proof.
  apply bisim_is_eq.
  revert_until Σ. ginit. gcofix CIH. i.
  ides itr.
  - rewrite! SBRed.ret. gstep. econs. eauto.
  - rewrite! SBRed.tau. gstep. econs. gbase. eauto.
  - rewrite <- bind_trigger. rewrite! SBRed.bind.
    destruct e.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind.
      rewrite H.
      rewrite! SBRed.ag. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.
    }
    destruct p.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inl1 s))) = trigger s) by grind.
      rewrite H. rewrite! SBRed.sch. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.     
    }
    destruct s.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inl1 c)))) = trigger c) by grind.
      rewrite H. rewrite! SBRed.call. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.     
    }
    destruct s.
    {
      assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inl1 p))))) = trigger p) by grind.
      rewrite H. destruct p.
      - rewrite! SBRed.put. des_ifs.
        + rewrite SBRed.put. des_ifs. 
          * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
          * exfalso. eapply existsb_exists in Heq. des.
            eapply SCP in Heq. 
            assert (XEQ:=existsb_exists).
            hdes. rewrite XEQ1 in Heq0; ss; eauto.
        + rewrite SBRed.core.
          rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
      - rewrite! SBRed.get. des_ifs.
        + rewrite! SBRed.get. des_ifs.
          * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
          * exfalso. eapply existsb_exists in Heq. des.
            eapply SCP in Heq. 
            assert (XEQ:=existsb_exists).
            hdes. rewrite XEQ1 in Heq0; ss; eauto.
        + rewrite SBRed.core.
          rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
    }
    assert ((@ITree.trigger (@hmodE Σ) X (inr1 (inr1 (inr1 (inr1 c))))) = trigger c) by grind.
    rewrite H. rewrite! SBRed.core. rewrite! bind_trigger.
    gstep. econs. i. r. gbase. eauto.
Qed.

Lemma inv_sandbox_tau `{Σ: GRA} {X} sc (itr : itree hmodE X)
    (SB : HMod.sandbox sc (tau;; itr) = tau;; itr) :
  HMod.sandbox sc itr = itr.
Proof.
  rewrite SBRed.tau in SB. inv SB.
  rewrite sandbox_well_scoped; refl.
Qed.

Lemma inv_sandbox_core `{Σ: GRA} {X Y} x sc (ktr : X -> itree hmodE Y) (c : coreE X)
    (SB : HMod.sandbox sc (trigger c >>= ktr) = trigger c >>= ktr) :
  HMod.sandbox sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.core in SB.
  rewrite! bind_trigger in SB. inv SB.
  eapply inj_pair2, equal_f in H0. eauto.
Qed.

Lemma inv_sandbox_call `{Σ: GRA} {X Y} x sc (ktr : X -> itree hmodE Y) (c : callE X)
    (SB : HMod.sandbox sc (trigger c >>= ktr) = trigger c >>= ktr) :
  HMod.sandbox sc (ktr x) = ktr x.
Proof.
  destruct c.
  rewrite SBRed.bind SBRed.call in SB.
  rewrite! bind_trigger in SB. inv SB.
  eapply inj_pair2, equal_f in H0. eauto.
Qed.

Lemma inv_sandbox_pg `{Σ: GRA} {X Y} x sc (ktr : X -> itree hmodE Y) (pg : pgE X)
    (SB : HMod.sandbox sc (trigger pg >>= ktr) = trigger pg >>= ktr) :
  HMod.sandbox sc (ktr x) = ktr x.
Proof.
  destruct pg.
  { rewrite SBRed.bind SBRed.put in SB.
    des_ifs; rewrite! bind_trigger in SB; inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  }
  { rewrite SBRed.bind SBRed.get in SB.
    des_ifs; rewrite! bind_trigger in SB; inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  }
Qed.

Lemma inv_sandbox_ag `{Σ: GRA} {X} sc (ktr : unit -> itree hmodE X) (ag : agE unit)
    (SB : HMod.sandbox sc (trigger ag >>= ktr) = trigger ag >>= ktr) :
  HMod.sandbox sc (ktr tt) = ktr tt.
Proof.
  rewrite SBRed.bind SBRed.ag in SB.
  rewrite! bind_trigger in SB. inv SB.
  eapply inj_pair2, equal_f in H0. eauto.
Qed.    

Lemma alist_upd_not_exists k v st scopes
    (NOTEXT : existsb (String.eqb k.1) scopes = false)
    (INSCP : incl (state_scopes st) scopes) :
  alist_upd k v st = st.
Proof.
  eapply alist_upd_not_in. 
  ii. eapply in_map with (f:=fst) in H. 
  rewrite List.map_map in H. eapply INSCP in H.
  assert (∃x, In x scopes /\ String.eqb k.1 x = true).
  { exists k.1. esplits; [eauto|]. eapply String.eqb_refl. }
  eapply existsb_exists in H0. clarify.
Qed.

Lemma alist_find_existsb st scopes k v
    (INSCP : incl (state_scopes st) scopes)
    (FIND : alist_find k st = Some v) :
  existsb (String.eqb k.1) scopes = true.
Proof.
  eapply existsb_exists.
  eapply alist_find_fst_some, in_map in FIND.
  rewrite List.map_map in FIND.
  exists k.1. esplits; eauto. eapply String.eqb_refl.
Qed.

Lemma alist_find_not_exists st scopes k
    (INSCP : incl (state_scopes st) scopes)
    (NOTEXT : existsb (String.eqb k.1) scopes = false) :
  alist_find k st = None.
Proof.
  eapply alist_find_fst_notin.
  ii. eapply in_map with (f:=fst) in H. 
  rewrite List.map_map in H. eapply INSCP in H.
  assert (∃x, In x scopes /\ String.eqb k.1 x = true).
  { exists k.1. esplits; [eauto|]. eapply String.eqb_refl. }
  eapply existsb_exists in H0. clarify.
Qed.

Lemma alist_find_exists_l st ctx scopeS scopeC (k : key)
    (DISJ : List.NoDup (scopeS ++ scopeC))
    (INS : incl (state_scopes st) scopeS)
    (INC : incl (state_scopes ctx) scopeC)
    (EXT : existsb (String.eqb k.1) scopeS = true) :
  alist_find k (st ++ ctx) = alist_find k st.
Proof.
  rewrite alist_find_app_o. des_ifs.
  eapply alist_find_fst_notin. ii.
  eapply existsb_exists in EXT. des.
  eapply NoDup_app_disjoint; eauto.
  eapply INC. unfold state_scopes. rewrite -List.map_map. 
  eapply in_map with (f:=fst) in H.
  eapply String.eqb_eq in EXT0. subst. eauto.
Qed.

Lemma wf_eq_solve `{Σ: GRA} (a b : Σ) : ✓ a -> a = b -> ✓ b.
Proof. i. rewrite <- H0. eauto. Qed.

Lemma wf_inv_l `{Σ: GRA} ms0 ms1
    (WF : HMod.wf (HMod.add ms0 ms1)) :
  HMod.wf ms0.
Proof.
  inv WF; ss. rewrite map_app in wf_fns. 
  econs; eauto using nodup_app_l.
Qed.

Ltac hstep := guclo hpsimC_spec; econs; econs; eauto; econs; eauto.

Lemma hpsim_ctx `{Σ: GRA} fnsems_src fnsems_tgt fl_src fl_tgt fl_ctx Ist contextual scopes scopeC
    (FLS : fl_src = (List.map (map_snd HMod.sandbox_body) fnsems_src))
    (FLT : fl_tgt = (List.map (map_snd HMod.sandbox_body) fnsems_tgt))
    (WS : ∀ (fn : string) p (IN : alist_find fn fnsems_src = Some p), incl p.1 scopes)
    (WT : ∀ (fn : string) p (IN : alist_find fn fnsems_tgt = Some p), incl p.1 scopes)
    (DISJ : List.NoDup (scopes ++ scopeC))

    ps pt nths st_src st_tgt st_ctx itr_src itr_tgt fmr
    (SCPT : incl (state_scopes st_tgt) scopes)
    (SCPS : incl (state_scopes st_src) scopes)
    (SCPC : incl (state_scopes st_ctx) scopeC)
    (ITRT : HMod.sandbox scopes itr_tgt = itr_tgt)
    (ITRS : HMod.sandbox scopes itr_src = itr_src)
    (SIM : hpsim_body open fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
    :
    hpsim_body contextual (fl_src ++ fl_ctx) (fl_tgt ++ fl_ctx) 
    (IstProd (IstSB scopes Ist) (IstSB scopeC IstEq))
    ps pt nths (st_src ++ st_ctx, itr_src) (st_tgt ++ st_ctx, itr_tgt) fmr.
  Proof.
    guardH FLS. guardH FLT.
    ginit. s. revert_until DISJ. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before CIH. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo hpsim_wfC_spec. econs. i.
    guclo hpsim_nodupC_spec. econs. i.
    exploit IN; i; des; eauto.
    { rewrite map_app in NODFS. eapply NoDup_app_remove_r. eauto. }
    { rewrite map_app in NODFT. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODS. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODD. eapply NoDup_app_remove_r. eauto. }
    clear IN. destruct x0; i; des; inv Heqp; try inv Heqp0.
    - hstep. iIntros "H". iPoseProof (RET with "H") as ">[% H]".
      iModIntro. iSplit; eauto. iExists st_src, st_tgt, st_ctx, st_ctx.
      iSplit; eauto. iFrame. eauto.
    - hstep.
      { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iExists st_ctx, st_ctx.
        iSplit; eauto.
      }
      i. guclo hpsim_wfC_spec. econs. i.
      eapply Own_bupd_split in INV0; eauto. des.
      eapply Own_general_soundness in INV1; eauto; cycle 1.
      { by eapply Own_wand_valid; first by iIntros "F"; iMod (INV0 with "F") as "[? _]"; iFrame. }
      rewrite /IstProd in INV1. uPred.unseal_in INV1; destruct INV1 as [st_srcL [st_tgtL [st_srcR [st_tgtR INV1]]]].
      destruct INV1 as [a1' [a1'' [INV1 [INV1' INV1'']]]]; inv INV1'.
      rewrite /IstSB in INV1''; rr in INV1''; uPred.unseal_in INV1''; des.
      destruct INV1''0 as [x0' [x0'' [? [INV1''0 ?]]]]; inv INV1''0.
      destruct INV1''1 as [x1' [x1'' [? [INV1''1 ?]]]]; inv INV1''1.
      rewrite /IstEq in H7; uPred.unseal_in H7; inv H7.
      (* 
        new states after call should maintain the scope of previous states. 
        ctx state should maintain its own scope.
      *)
      eapply K; try refl; eauto using inv_sandbox_call; cycle 3.
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      iIntros "H". iPoseProof (INV0 with "H") as ">H".
      iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H1".
      { rewrite INV1 INV1'' H2; iDestruct "H1" as "[_ [[_ H] _]]";
          iPoseProof (Own_general_completeness with "H") as "H"; eauto. }
      { iApply INV2; done. }
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core. 
    - hstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! SBRed.bind.
      move FLS at bottom. move FUN at bottom.
      rewrite FLS in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs.
      unfold HMod.sandbox_body.
      rewrite sandbox_well_scoped; eauto.
      f_equal. extensionalities.
      rewrite ?SBRed.bind !SBRed.tau SBRed.ret.
      do 4 f_equal. extensionalities. eapply inv_sandbox_call; eauto. 
    - hstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! SBRed.bind.
      move FLT at bottom. move FUN at bottom.
      rewrite FLT in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs.
      unfold HMod.sandbox_body.
      rewrite sandbox_well_scoped; eauto.
      f_equal. extensionalities.
      rewrite ?SBRed.bind !SBRed.tau SBRed.ret.
      do 4 f_equal. extensionalities. eapply inv_sandbox_call; eauto.
    - hstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - hstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. eapply K; try refl; eauto using inv_sandbox_core.
    - hstep. eapply K; try refl; eauto using inv_sandbox_core.
    - assert (H1:= ITRS).
      rewrite  -ITRS SBRed.bind SBRed.put. des_ifs.
      + hstep.
        assert (UPD : alist_upd k v (st_src ++ st_ctx) = alist_upd k v st_src ++ st_ctx).
        { 
          move SCPS at bottom. move SCPC at bottom. 
          eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0.
          rewrite alist_upd_not_tail; eauto.
          ii. eapply NoDup_app_disjoint; eauto.
          eapply in_map with (f:=fst) in H2.
          rewrite List.map_map in H2. eapply SCPC in H2.
          rewrite <- Heq0. eauto.
        }
        rewrite UPD. eapply K; try refl; eauto.
        { rewrite state_scopes_update. eauto. }
        { eapply sandbox_well_scoped. refl. }
        { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
      + hstep. eapply K; try refl; eauto.
        { eapply sandbox_well_scoped. refl. }
        { 
          f_equal. 
          { eapply alist_upd_not_exists; eauto. }
          { symmetry. eapply inv_sandbox_pg. eauto. }
        }

  - assert (H1:=ITRT).
    rewrite -ITRT SBRed.bind SBRed.put. des_ifs.
    + hstep.
      assert (UPD : alist_upd k v (st_tgt ++ st_ctx) = alist_upd k v st_tgt ++ st_ctx).
      {
        move SCPS at bottom. move SCPC at bottom. 
        eapply existsb_exists in Heq. des. eapply String.eqb_eq in Heq0.
        eapply alist_upd_not_tail. eauto.
        ii. eapply NoDup_app_disjoint; eauto.
        eapply in_map with (f:=fst) in H2.
        rewrite List.map_map in H2. eapply SCPC in H2.
        rewrite <- Heq0. eauto.  
      }
      rewrite UPD. eapply K; try refl; eauto.
      { rewrite state_scopes_update. eauto. }
      { eapply sandbox_well_scoped. refl. }
      { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
    + rewrite SBRed.bind SBRed.put Heq !bind_trigger in H1.
    exfalso. ss.   

  - assert (H1:=ITRS). 
    rewrite  -ITRS SBRed.bind SBRed.get. des_ifs.
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
    rewrite  -ITRT SBRed.bind SBRed.get. des_ifs.
    + hstep. eapply K; try refl; eauto.
      { eapply sandbox_well_scoped. refl. }
      erewrite alist_find_exists_l; eauto.
      repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
    + rewrite SBRed.bind SBRed.get Heq !bind_trigger in H1.
      exfalso. ss.

  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. eapply K; try refl; eauto.
    + rewrite SBRed.bind SBRed.sch !bind_trigger in ITRT.
      depdes ITRT. eapply equal_f in x. eauto.
    + rewrite SBRed.bind SBRed.sch !bind_trigger in ITRS.
      depdes ITRS. eapply equal_f in x. eauto.
  - hstep.
    { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
      iModIntro. iFrame. iExists st_ctx, st_ctx.
      iSplit; eauto.
    }
    i. guclo hpsim_wfC_spec. econs. i.
    eapply Own_bupd_split in INV0; eauto. des.
    eapply Own_general_soundness in INV1; eauto; cycle 1.
    { by eapply Own_wand_valid; first by iIntros "F"; iMod (INV0 with "F") as "[? _]"; iFrame. }
    rewrite /IstProd in INV1. uPred.unseal_in INV1; destruct INV1 as [st_srcL [st_tgtL [st_srcR [st_tgtR INV1]]]].
    destruct INV1 as [a1' [a1'' [INV1 [INV1' INV1'']]]]; inv INV1'.
    rewrite /IstSB in INV1''; rr in INV1''; uPred.unseal_in INV1''; des.
    destruct INV1''0 as [x0' [x0'' [? [INV1''0 ?]]]]; inv INV1''0.
    destruct INV1''1 as [x1' [x1'' [? [INV1''1 ?]]]]; inv INV1''1.
    rewrite /IstEq in H7; uPred.unseal_in H7; inv H7.
    (* 
      new states after call should maintain the scope of previous states. 
      ctx state should maintain its own scope.
    *)
    eapply K; try refl; eauto; cycle 3.
    { rewrite SBRed.bind SBRed.sch !bind_trigger in ITRT.
      depdes ITRT. eapply equal_f in x. eauto. }
    { rewrite SBRed.bind SBRed.sch !bind_trigger in ITRS.
      depdes ITRS. eapply equal_f in x. eauto. }
    { eapply nodup_app_l. rewrite <- map_app. eauto. }
    { eapply nodup_app_l. rewrite <- map_app. eauto. }
    iIntros "H". iPoseProof (INV0 with "H") as ">H".
    iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H1".
    { rewrite INV1 INV1'' H2; iDestruct "H1" as "[_ [[_ H] _]]";
        iPoseProof (Own_general_completeness with "H") as "H"; eauto. }
    { iApply INV2; done. }
  - gstep. econs. econs. econs; eauto. econs; eauto. 
    gbase. pclearbot. eapply CIH; try refl; eauto.
Qed.

Lemma isim_ctx `{Σ: GRA}
  fs ft ms mt ctx Ist fn contextual
  (WFS : HMod.wf (HMod.add ms ctx))
  (WFT : HMod.wf (HMod.add mt ctx))
  (FINDT : alist_find fn (HMod.fnsems mt) = Some ft)
  (FINDS : alist_find fn (HMod.fnsems ms) = Some fs)
  (SCOPES : sub_perm (HMod.scopes ms) (HMod.scopes mt))
  (NODUPFT : List.NoDup (List.map fst (HMod.fnsems mt ++ HMod.fnsems ctx)))
  (NODUPFS : List.NoDup (List.map fst (HMod.fnsems ms ++ HMod.fnsems ctx)))
  (IMON : ∀ nths0 nths', nths0 <= nths' → ∀ st_src st_tgt,
         Ist nths0 st_src st_tgt -∗ Ist nths' st_src st_tgt)
  (SIM : isim_fsem
     (List.map (map_snd HMod.sandbox_body) (HMod.fnsems ms))
     (List.map (map_snd HMod.sandbox_body) (HMod.fnsems mt))
     Ist open
     (HMod.sandbox_body fs)
     (HMod.sandbox_body ft))
  :
    isim_fsem
      (List.map (map_snd HMod.sandbox_body)
         (HMod.fnsems ms ++ HMod.fnsems ctx))
      (List.map (map_snd HMod.sandbox_body)
         (HMod.fnsems mt ++ HMod.fnsems ctx))
      (IstProd (IstSB (HMod.scopes mt) Ist) (IstSB (HMod.scopes ctx) IstEq)) contextual
      (HMod.sandbox_body fs) (HMod.sandbox_body ft).
Proof.
  ii. specialize (SIM x y H). subst.
  iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & IST) & %)". des. subst.
  move: NODUPFS NODUPFT NODS NODD; rewrite ?map_app; intros NODUPFS NODUPFT NODS NODD.
  assert (NODA := NODS). assert (NODB := NODD). assert (NODC:= NODS).
  eapply nodup_app_l in NODA, NODB. eapply nodup_app_r in NODC.
  specialize (SIM nths st_srcL st_tgtL IMON NODA NODB).
  rewrite <- map_app in *.
  iPoseProof (SIM with "IST") as "SIM".
  iStopProof. Local Transparent isim.
  split; intros x wfx ISIM.
  gfinal. right. eapply paco9_mon_bot; eauto.
  rewrite! List.map_app.
  assert (EQ : (λ x, (map_snd HMod.sandbox_body x).1) = @fst string _).
  { extensionalities. destruct H. eauto. }
  eapply hpsim_ctx; eauto; ss.
  {
    i. etrans; cycle 1.
    { eapply sub_perm_incl; eauto. }
    ii. eapply ms.(HMod.well_scoped_fns).
    unfold fnsems_scopes. erewrite IN. ss.
  }
  { 
    ii. eapply mt.(HMod.well_scoped_fns).
    unfold fnsems_scopes. erewrite IN. ss.
  }
  { eapply WFT. }
  { 
    eapply sandbox_well_scoped. ii.
    eapply mt.(HMod.well_scoped_fns). 
    unfold fnsems_scopes. erewrite FINDT. ss.
  }
  { 
    eapply sandbox_well_scoped. etrans; cycle 1.
    { eapply sub_perm_incl; eauto. }
    ii. eapply ms.(HMod.well_scoped_fns). 
    unfold fnsems_scopes. erewrite FINDS. ss.
  }
  ginit. i. eapply gpaco9_mon; first eapply ISIM; eauto using iunlift_ibot.
Qed.

Lemma hmod_sim_ctx `{Σ: GRA} (ms mt ctx : HMod.t) IC Ist contextual
  (SIM : HSim.t open ms mt IC Ist)
  :
  HSim.t contextual (ms ★ ctx) (mt ★ ctx) IC 
    (IstProd (IstSB mt.(HMod.scopes) Ist)
             (IstSB ctx.(HMod.scopes) IstEq)).
Proof.
  inv SIM.
  econs; ss.
  { 
    iIntros "H". iPoseProof (sim_initial with "H") as "H".
    unfold IstProd. iExists _, _, _, _. iFrame. iPureIntro.
    esplits; eauto; try eapply HMod.well_scoped_init.
    etrans; [eapply HMod.well_scoped_init|].
    eapply sub_perm_incl, sim_scopes.
  }
  { i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)". des; subst.
    iPoseProof ((sim_mon _ _ LE) with "H") as "H".
    repeat iExists _. iFrame. iPureIntro. esplits; eauto.
  }
  { eapply sub_perm_cancel_tail. eauto. }
  { rewrite ?map_app. eapply sub_perm_cancel_tail. eauto. }
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
    exists fs. esplits; ss.
    { rewrite alist_find_app_o. des_ifs. exfalso.
      eapply alist_find_some in FIND, Heq0.
      eapply in_map with (f:=fst) in FIND, Heq0.
      rewrite map_app in NODUPFT.
      eapply NoDup_app_disjoint; eauto.
    }
    destruct fs as [sc itr].
    inv WFT. eapply isim_reflR; ss; i; eauto.
    - replace sc with (fnsems_scopes fn ctx.(HMod.fnsems)).
      { eapply ctx.(HMod.well_scoped_fns). }
      { unfold fnsems_scopes. des_ifs. }
    - iIntros "%". des; subst; eauto.
    - iIntros "%". des; subst; eauto. iPureIntro.  esplits; eauto.
      + rewrite state_scopes_update. eauto.
      + rewrite state_scopes_update. eauto.
  }
Qed.

Theorem main_adequacy `{Σ: GRA} (ms mt : HMod.t) IC Ist
    (SIM : HSim.t open ms mt IC Ist) :
  ctx_refines (ms, IC) (mt, emp%I).
Proof.
  ii. s.
  destruct ctx as [ctx cond].
  assert (SIMC := SIM).
  ii. ss. eapply hmod_sim_ctx with (ctx := ctx) in SIMC.
  split.
  { eapply hsim_wf; eauto. }
  ii. hexploit Own_split; eauto; intros [a1 [a2 [Ha [H1 H2]]]].
  exists a2; splits; eauto.
  { eapply cmra_valid_op_r; erewrite <- Ha; ss. }
  { iIntros "H"; iSplitR "H"; ss; iApply H2; done. }
  ii. subst. eapply adequacy_modsem, PR.
  - eapply (hsim_adequacy _ _ rs a1 a2); eauto.
    { rewrite Ha; iIntros "[H1 H2]"; iFrame. }
    { eapply hsim_wf; eauto. }
  - inv WFM. econs. ss. unfold map_snd.
    rewrite !List.map_map.
    eapply eq_ind; [|].
    { inv SIM. eapply sub_perm_nodup. eapply sub_perm_cancel_tail. eapply sim_match.
      rewrite map_app in wf_fns. eapply wf_fns. }
    rewrite -map_app.
    f_equal. extensionalities. destruct H. ss.
Qed.

(* COMM *)

Definition perm_Ist `{Σ: GRA} : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
  fun _ l0 l1 => ⌜l0 ≡ₚ l1⌝%I.  

Lemma alist_upd_perm {K V} l0 l1 `{Dec K} (k : K) (v : V)
      (ND : List.NoDup (List.map fst l0))
      (PERM : l0 ≡ₚ l1)
    :
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

Lemma hmod_add_scopes `{Σ: GRA} md0 md1:
  HMod.scopes (md0 ★ md1) = HMod.scopes md0 ++ HMod.scopes md1.
Proof. ss. Qed.

Lemma hmod_add_comm `{Σ: GRA} ms0 ms1 contextual:
  HSim.t contextual (ms0 ★ ms1) (ms1 ★ ms0) (emp%I)
    (IstSB (HMod.scopes (ms0 ★ ms1)) perm_Ist).
Proof.
  econs; ss.
  {
    iIntros "_". iPureIntro. esplits.
    { eapply (ms0 ★ ms1).(HMod.well_scoped_init). }
    { ii. eapply (ms0 ★ ms1).(HMod.well_scoped_init); ss.
      move: H; rewrite /state_scopes ?map_app; intros H.
      eapply in_app_or in H. eapply in_or_app. des; eauto.
    }
    { eapply Permutation.Permutation_app_comm. }
  }
  { i. r. rewrite /IstSB /perm_Ist; iIntros "_ [% %]". iSplit; iPureIntro; eauto. }
  { apply sub_perm_comm. }
  { rewrite ?map_app; i. apply sub_perm_comm. }

  ii. eapply alist_find_comm in FIND; cycle 1. 
  { inv WFT; ss. }
  esplits; eauto.

  (* simulation *)
  ii. subst. destruct fs. unfold HMod.sandbox_body. s.
  generalize (i y) as it. clear FIND i y.
  combine_quant NODD.
  combine_quant NODS.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant nths.
  eapply isim_coind. i.
  destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
  iIntros "(#IST & CIH)".
  assert (CASE := case_itrH it); des; subst.
  - step. iFrame. eauto.
  - steps_l. steps_r. by_coind "CIH". eauto.
  - steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
  - steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
  - destruct s.
    + step. by_coind "CIH". eauto.
    + yield "IST"; eauto. by_coind "CIH". eauto.
  - destruct c. call "IST"; eauto. by_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { steps_r. force_l. instantiate (1:=q). steps_l. by_coind "CIH". eauto. }
      iApply isim_sput_src. iApply isim_sput_tgt.
      by_coind "CIH". unfold perm_Ist. 
      iDestruct "IST" as "%". des. 
      iPureIntro. rewrite !state_scopes_update. esplits; eauto. 
      eapply alist_upd_perm; eauto.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { steps_r. force_l. instantiate (1:=q). steps_l. by_coind "CIH". eauto. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝)%I with "[IST]" as "%".
      { iDestruct "IST" as "%". des. iPureIntro.
        eapply alist_permutation_find; eauto. }
      rewrite H0. by_coind "CIH". eauto.
  - destruct e.
    + steps_r. force_l. instantiate (1:= q). steps_l. by_coind "CIH". eauto. 
    + steps_l. force_r. instantiate (1:= q). steps_r. by_coind "CIH". eauto.
    + step. by_coind "CIH". eauto. 
  Unshelve. all : eauto. 
  { eapply alist_upd_nodup. eauto. }
  { eapply alist_upd_nodup. eauto. }
Qed.

Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimFacts MSim MSimFacts.
Require Import ISim ISimFacts Tactics TacticsInit.
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

Lemma sandbox_well_scoped `{Σ: GRA} {A} (img0 img1: bool) (msk0 msk1: _->bool) scp0 scp1 (itr : itree crisE A)
    (IMPL: img0 → img1)
    (MASK : ∀ fn, msk0 fn → msk1 fn)
    (SCP : incl scp0 scp1) :
  SB.sandbox img1 msk1 scp1 (SB.sandbox img0 msk0 scp0 itr) = SB.sandbox img0 msk0 scp0 itr.
Proof.
  apply bisim_is_eq.
  revert_until Σ. ginit. gcofix CIH. i.
  ides itr.
  { rewrite! SBRed.ret. gstep. econs. eauto. }
  { rewrite! SBRed.tau. gstep. econs. gbase. eauto. }
  rewrite <- bind_trigger. rewrite! SBRed.bind.
  destruct e.
  {
    assert ((@ITree.trigger (@crisE Σ) X (inl1 a)) = trigger a) by grind.
    rewrite H. destruct a.
    - rewrite !SBRed.Assume !bind_trigger. des_ifs.
      + rewrite SBRed.Assume. des_ifs.
        * gstep. r; s. econs. i. ired. gbase; eauto.
        * exploit IMPL; et; i; inv x0.
      + rewrite SBRed.vis_take. des_ifs.
        * gstep. r; s. econs. ss.
        * gstep. r; s. econs. ss.
    - rewrite !SBRed.AssumePrecise !bind_trigger.
      gstep. econs. i. gbase. eauto.
    - rewrite !SBRed.Guarantee !bind_trigger.
      gstep. econs. i. gbase. eauto.
  }
  destruct s; [destruct c|].
  {
    rewrite! SBRed.call. des_ifs; ss.
    + rewrite SBRed.call. des_ifs.
      * rewrite! bind_trigger.
        gstep. econs. i. r. gbase. eauto.
      * exfalso. rewrite (MASK fn) in Heq0; ss.
    + rewrite /triggerUB SBRed.unwrapU.
      ired; rewrite !bind_trigger. gstep. econs. i. ss.
  }
  {
    rewrite! SBRed.spawn. des_ifs; ss.
    + rewrite SBRed.spawn. des_ifs.
      * rewrite! bind_trigger.
        gstep. econs. i. r. gbase. eauto.
      * exfalso. rewrite (MASK fn) in Heq0; ss.
    + rewrite /triggerUB SBRed.unwrapU.
      ired; rewrite !bind_trigger. gstep. econs. i. ss.
  }
  {
    rewrite! SBRed.yield. rewrite! bind_trigger.
    gstep. econs. i. r. gbase. eauto.
  }
  destruct s; [destruct p|].
  {
    rewrite! SBRed.put. des_ifs.
    + rewrite SBRed.put. des_ifs. 
      * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
      * exfalso. eapply existsb_exists in Heq. des. eapply SCP in Heq. 
        assert (XEQ:=existsb_exists).
        hdes. rewrite XEQ1 in Heq0; ss; eauto.
    + rewrite /triggerUB SBRed.unwrapU.
      ired; rewrite !bind_trigger. gstep. econs. i. ss.
  }
  {
    rewrite! SBRed.get. des_ifs.
    + rewrite! SBRed.get. des_ifs.
      * rewrite! bind_trigger. gstep. econs. i. r. gbase. eauto.
      * exfalso. eapply existsb_exists in Heq. des. eapply SCP in Heq. 
        assert (XEQ:=existsb_exists).
        hdes. rewrite XEQ1 in Heq0; ss; eauto.
    + rewrite /triggerUB SBRed.unwrapU.
      ired; rewrite !bind_trigger. gstep. econs. i. ss.
  }
  {
    destruct c.
    - rewrite! SBRed.choose. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.
    - rewrite !SBRed.take !bind_trigger.
      destruct (excluded_middle_informative _) eqn: E; s.
      + rewrite orb_true_r SBRed.take E orb_true_r.
        gstep. r; s. econs. i. ired. gbase. eauto.
      + destruct img0; s.
        * rewrite SBRed.take. destruct img1; s.
          { gstep. r; s. econs. i. ired. gbase. et. }
          { exploit IMPL; et; i. inv x0. }
        * rewrite SBRed.vis_take. des_ifs.
          { gstep. r; s. econs. ss. }
          { gstep. r; s. econs. ss. }
    - rewrite! SBRed.io. rewrite! bind_trigger.
      gstep. econs. i. r. gbase. eauto.
  }
Qed.

Lemma inv_sandbox_tau `{Σ: GRA} {X} img msk sc (itr : itree crisE X)
    (SB : SB.sandbox img msk sc (tau;; itr) = tau;; itr) :
  SB.sandbox img msk sc itr = itr.
Proof.
  rewrite SBRed.tau in SB. inv SB.
  rewrite sandbox_well_scoped; ss.
Qed.

Lemma inv_sandbox_core `{Σ: GRA} {X Y} x img msk sc (ktr : X -> itree crisE Y) (e: coreE X)
    (SB : SB.sandbox img msk sc (trigger e >>= ktr) = trigger e >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  destruct e.
  - rewrite SBRed.bind SBRed.choose in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  - rewrite SBRed.bind SBRed.take in SB. des_ifs.
    + rewrite! bind_trigger in SB. inv SB.
      eapply inj_pair2, equal_f in H0. eauto.
    + bsimpl. des; subst; ss.
      rewrite !bind_trigger bind_vis in SB. depdes SB.
      exfalso. destruct (excluded_middle_informative _); ss.
  - rewrite SBRed.bind SBRed.io in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
Qed.

Lemma inv_sandbox_call `{Σ: GRA} {Y} x img msk sc (ktr : _ -> itree crisE Y) f a
    (SB : SB.sandbox img msk sc (trigger (Call f a) >>= ktr) = trigger (Call f a) >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.call in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
  - rewrite bind_bind bind_vis in x. depdes x.
Qed.

Lemma inv_sandbox_spawn `{Σ: GRA} {Y} x img msk sc (ktr : _ -> itree crisE Y) f a
    (SB : SB.sandbox img msk sc (trigger (Spawn f a) >>= ktr) = trigger (Spawn f a) >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.spawn in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
  - rewrite bind_bind bind_vis in x. depdes x.
Qed.

Lemma inv_sandbox_pg `{Σ: GRA} {X Y} x img msk sc (ktr : X -> itree crisE Y) (pg : pgE X)
    (SB : SB.sandbox img msk sc (trigger pg >>= ktr) = trigger pg >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  destruct pg.
  { rewrite SBRed.bind SBRed.put in SB.
    des_ifs; rewrite! bind_trigger in SB; depdes SB.
    - eapply equal_f in x. eauto.
    - rewrite bind_bind bind_vis in x. depdes x.
  }
  { rewrite SBRed.bind SBRed.get in SB.
    des_ifs; rewrite! bind_trigger in SB; depdes SB.
    - eapply equal_f in x. eauto.
    - rewrite bind_bind bind_vis in x. depdes x.
  }
Qed.

Lemma inv_sandbox_ag `{Σ: GRA} {X R} x img msk sc (ktr : X -> itree crisE R) (e: agE X)
    (SB : SB.sandbox img msk sc (trigger e >>= ktr) = trigger e >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  destruct e.
  - rewrite SBRed.bind SBRed.Assume in SB. des_ifs.
    + rewrite! bind_trigger in SB. inv SB.
      eapply inj_pair2, equal_f in H0. eauto.
    + rewrite !bind_trigger bind_vis in SB. depdes SB.
  - rewrite SBRed.bind SBRed.AssumePrecise in SB.
    rewrite! bind_trigger in SB. inv SB.
    eapply inj_pair2, equal_f in H0. eauto.
  - rewrite SBRed.bind SBRed.Guarantee in SB.
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
    (WF : Mod.wf (Mod.add ms0 ms1)) :
  Mod.wf ms0.
Proof.
  inv WF; ss. rewrite map_app in wf_fns. 
  econs; eauto using nodup_app_l.
Qed.

Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto.

Lemma msim_ctx `{Σ: GRA} contextual fnsems_src fnsems_tgt (fl_src fl_tgt fl_ctx: alist (option string) _) Ist (img:bool) (msk: _->bool) scp scpC RR
    (FLS : fl_src = (List.map (map_snd SB.sandbox_body) fnsems_src))
    (FLT : fl_tgt = (List.map (map_snd SB.sandbox_body) fnsems_tgt))
    (WS : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_src = Some (img0,msk0,scp0,bd0)), (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (WT : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_tgt = Some (img0,msk0,scp0,bd0)), (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (DISJ : List.NoDup (scp ++ scpC))

    ps pt nths st_src st_tgt st_ctx itr_src itr_tgt fmr
    (SCPT : incl (state_scopes st_tgt) scp)
    (SCPS : incl (state_scopes st_src) scp)
    (SCPC : incl (state_scopes st_ctx) scpC)
    (ITRT : SB.sandbox img msk scp itr_tgt = itr_tgt)
    (ITRS : SB.sandbox img msk scp itr_src = itr_src)
    (SIM : msim open fl_src fl_tgt Ist (ist_with_eq RR) ps pt nths
             (st_src, itr_src) (st_tgt, itr_tgt) fmr)
  :
  @msim _ contextual (fl_src ++ fl_ctx) (fl_tgt ++ fl_ctx)
    (IstProd (IstSB scp Ist) (IstSB scpC IstEq)) Any.t Any.t
    (ist_with_eq (IstProd (IstSB scp RR) (IstSB scpC IstEq))) ps pt nths
    (st_src ++ st_ctx, itr_src) (st_tgt ++ st_ctx, itr_tgt) fmr.
  Proof.
    guardH FLS. guardH FLT. hdes.
    move WS0 at top. move WS2 at top. move WS3 at top.
    move WT0 at top. move WT2 at top. move WT3 at top.
    ginit. s. revert_until DISJ. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before CIH. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo msim_wfC_spec. econs. i.
    guclo msim_nodupC_spec. econs. i.
    exploit IN; i; des; eauto.
    { rewrite map_app in NODFS. eapply NoDup_app_remove_r. eauto. }
    { rewrite map_app in NODFT. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODS. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODD. eapply NoDup_app_remove_r. eauto. }
    clear IN. destruct x0; i; des; inv Heqp; try inv Heqp0.
    - mstep. iIntros "H". rewrite RET. iMod "H" as "[% H]". subst.
      iModIntro. iSplit; eauto. iExists st_src, st_tgt, st_ctx, st_ctx.
      repeat (iSplit; et).
    - mstep.
      { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iExists st_ctx, st_ctx.
        iSplit; eauto.
      }
      i. guclo msim_wfC_spec. econs. i.
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
      eapply K; try refl; eauto using inv_sandbox_call; try nia; cycle 3.
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      { eapply nodup_app_l. rewrite <- map_app. eauto. }
      iIntros "H". iPoseProof (INV0 with "H") as ">H".
      iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H1".
      { rewrite INV1 INV1'' H2; iDestruct "H1" as "[_ [[_ H] _]]";
          iPoseProof (Own_general_completeness with "H") as "H"; eauto. }
      { iApply INV2; done. }
    - mstep. i. eapply K; try refl; eauto using inv_sandbox_core. 
    - mstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! SBRed.bind.
      move FLS at bottom. move FUN at bottom.
      rewrite FLS in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs. unfold SB.sandbox_body.
      destruct f0 as [[[img0 msk0] scp0] bd0]. s.
      rewrite sandbox_well_scoped; eauto; cycle 1.
      f_equal. extensionalities.
      rewrite ?SBRed.bind !SBRed.tau SBRed.ret.
      do 4 f_equal. extensionalities. eapply inv_sandbox_call; eauto. 
    - mstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! SBRed.bind.
      move FLT at bottom. move FUN at bottom.
      rewrite FLT in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs. unfold SB.sandbox_body.
      destruct f0 as [[[img0 msk0] scp0] bd0]. s.
      rewrite sandbox_well_scoped; eauto.
      f_equal. extensionalities.
      rewrite ?SBRed.bind !SBRed.tau SBRed.ret.
      do 4 f_equal. extensionalities. eapply inv_sandbox_call; eauto.
    - mstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - mstep. eapply K; try refl; eauto using inv_sandbox_tau.
    - mstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - mstep. i. eapply K; try refl; eauto using inv_sandbox_core.
    - mstep. eapply K; try refl; eauto using inv_sandbox_core.
    - mstep. eapply K; try refl; eauto using inv_sandbox_core.

    - assert (H1:= ITRS).
      rewrite  -ITRS SBRed.bind SBRed.put. des_ifs.
      + mstep.
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
        { eapply sandbox_well_scoped; et; refl. }
        { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
      + unfold triggerUB. ired. mstep. ss.

  - assert (H1:=ITRT).
    rewrite -ITRT SBRed.bind SBRed.put. des_ifs.
    + mstep.
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
      { eapply sandbox_well_scoped; et. refl. }
      { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
    + rewrite SBRed.bind SBRed.put Heq !bind_trigger in H1.
      exfalso. unfold triggerUB in H1. rewrite bind_bind bind_vis in H1. ss.

  - assert (H1:=ITRS). 
    rewrite  -ITRS SBRed.bind SBRed.get. des_ifs.
    + mstep. eapply K; try refl; eauto.
      { eapply sandbox_well_scoped; et. refl. }
      erewrite alist_find_exists_l; eauto.
      repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
    + unfold triggerUB. ired. mstep. ss.

  - assert (H1:=ITRT). 
    rewrite  -ITRT SBRed.bind SBRed.get. des_ifs.
    + mstep. eapply K; try refl; eauto.
      { eapply sandbox_well_scoped; et. refl. }
      erewrite alist_find_exists_l; eauto.
      repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
    + rewrite SBRed.bind SBRed.get Heq !bind_trigger in H1.
      exfalso. unfold triggerUB in H1. rewrite bind_bind bind_vis in H1. ss.

  - mstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. i. hexploit K; et; i; des. esplits; et. i.
    eapply H2; try refl; eauto using inv_sandbox_ag.
  - guclo @msimC_spec. econs; esplits; et.
    eapply msim_assume_precise_both; et.
    i. eapply K; try refl; eauto using inv_sandbox_ag.
  - mstep. eapply K; try refl; eauto.
    + eapply inv_sandbox_spawn in ITRT. eauto.
    + eapply inv_sandbox_spawn in ITRS. eauto.
  - mstep.
    { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
      iModIntro. iFrame. iExists st_ctx, st_ctx.
      iSplit; eauto.
    }
    i. guclo msim_wfC_spec. econs. i.
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
    eapply K; try refl; eauto; try nia; cycle 3.
    { rewrite SBRed.bind SBRed.yield !bind_trigger in ITRT.
      depdes ITRT. eapply equal_f in x. eauto. }
    { rewrite SBRed.bind SBRed.yield !bind_trigger in ITRS.
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

Lemma isim_ctx `{Σ: GRA} contextual RR
  fs ft ms mt ctx Ist
  (WFS : Mod.wf (Mod.add ms ctx))
  (WFT : Mod.wf (Mod.add mt ctx))
  (SCOPES : sub_perm (Mod.scopes ms) (Mod.scopes mt))
  (NODUPFT : List.NoDup (List.map fst (Mod.fnsems mt ++ Mod.fnsems ctx)))
  (NODUPFS : List.NoDup (List.map fst (Mod.fnsems ms ++ Mod.fnsems ctx)))
  (IMON : ∀ nths0 nths', nths0 <= nths' → ∀ st_src st_tgt,
          Ist nths0 st_src st_tgt ⊢ Ist nths' st_src st_tgt)
  (MON: Ist_monotone Ist)
  :
  ∀ (arg : Any.t) (nths : nat) (st_src st_tgt st_ctx : list (key * Any.t))
    (SCOPEFS: incl fs.1.2 (Mod.scopes mt))
    (SCOPEFT: incl ft.1.2 (Mod.scopes mt))
    (SCOPES: incl (map (fst∘fst) st_src) (Mod.scopes mt))
    (SCOPET: incl (map (fst∘fst) st_tgt) (Mod.scopes mt))
    (SCOPEC: incl (map (fst∘fst) st_ctx) (Mod.scopes ctx)),
    isim open
           (map (map_snd SB.sandbox_body) (Mod.fnsems ms))
           (map (map_snd SB.sandbox_body) (Mod.fnsems mt)) Ist ibot ibot
           (ist_with_eq RR) false false nths
           (st_src, SB.sandbox_body fs arg)
           (st_tgt, SB.sandbox_body ft arg)
      ⊢ @isim _ contextual
          (map (map_snd SB.sandbox_body) (Mod.fnsems ms ++ Mod.fnsems ctx))
         (map (map_snd SB.sandbox_body) (Mod.fnsems mt ++ Mod.fnsems ctx))
         (IstProd (IstSB (Mod.scopes mt) Ist) (IstSB (Mod.scopes ctx) IstEq))
         ibot ibot Any.t Any.t
         (ist_with_eq
           (IstProd (IstSB (Mod.scopes mt) RR) (IstSB (Mod.scopes ctx) IstEq)))
         false false nths
         (st_src ++ st_ctx, SB.sandbox_body fs arg) (st_tgt ++ st_ctx, SB.sandbox_body ft arg).
Proof.
  ii. rewrite /SB.sandbox_body.
  eapply entails_pointwise. intros fmr SIM.
  eapply isim_init in SIM; cycle 1; et.
  eapply gpaco9_mon in SIM; try apply iunlift_ibot.
  eapply gpaco9_init in SIM; eauto with paco.
  eapply isim_final, gpaco9_final; eauto with paco. right.
  eapply paco9_mon_bot; et.
  destruct fs as [[[img msk] scp] bd].
  destruct ft as [[[img0 msk0] scp0] bd0]. ss.
  rewrite !map_app. eapply msim_ctx; try apply SIM; try nia; cycle 8; i.
  - instantiate (1:= wmask_all). instantiate (1:= true).    
    rewrite sandbox_well_scoped; i; bsimpl; et.
  - rewrite sandbox_well_scoped; i; bsimpl; et.
  - refl.
  - refl.
  - bsimpl. esplits; et.
    etrans; [|eapply sub_perm_incl; et].
    etrans; [|eapply Mod.well_scoped_fns].
    unfold fnsems_scopes. erewrite IN. refl.
  - bsimpl. esplits; et.
    etrans; [|eapply Mod.well_scoped_fns].
    unfold fnsems_scopes. erewrite IN. refl.
  - destruct WFT. et.
  - et.
  - etrans; [apply SCOPES0|]. refl.
  - et.
Qed.

Section ADEQUACY.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma ISim_ctx contextual (ms mt ctx : Mod.t) IC Ist
  (SIM : ISim.t open ms mt IC Ist)
  :
  ISim.t contextual (ms ★ ctx) (mt ★ ctx) IC 
    (IstProd (IstSB mt.(Mod.scopes) Ist) (IstSB ctx.(Mod.scopes) IstEq)).
Proof using.
  inv SIM.
  econs; intro WFTC; dup WFTC; eapply wf_inv_l in WFTC0; rename WFTC0 into WFT;
    assert (WFS: Mod.wf ms) by (eapply ISim_wf; et; econs; et).
  {
    ii. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)".
    des; subst. rewrite (sim_mon WFT _ _ LE).
    repeat iExists _. iFrame. iPureIntro. esplits; eauto.
  }
  { eapply sub_perm_cancel_tail. et. }
  { rewrite ?map_app. eapply sub_perm_cancel_tail. eauto. }
  {
    assert (WFSC: Mod.wf (ms ★ ctx)).
    { econs.
      * eapply sub_perm_nodup; [|eapply Mod.wf_fns, WFTC].
        s. rewrite !map_app. eapply sub_perm_cancel_tail. et.
      * eapply sub_perm_nodup; [|eapply Mod.wf_scopes, WFTC].
        s. eapply sub_perm_cancel_tail. et.
    }

    specialize (sim_initial WFT).
    r. r in sim_initial. i. rewrite map_app alist_find_app_o in H.
    rewrite !alist_find_map_snd in H, sim_initial |- *.
    destruct (alist_find _ (Mod.fnsems mt)) eqn: E; ss.
    edestruct sim_initial; et.
    destruct (alist_find _ (Mod.fnsems ms)) eqn: E0; ss.
    rewrite alist_find_app_o. rewrite E0.
    destruct (alist_find _ (Mod.fnsems ctx)) eqn: E1; ss. esplits; et.
    rewrite H1. iIntros "H". do 4 iExists _. iSplit; et. iSplit; et.
    - iSplit; et. iPureIntro. split; try apply (Mod.well_scoped_init mt).
      etrans; try apply (Mod.well_scoped_init ms).
      eapply sub_perm_incl; et.
    - iPureIntro. esplits; et; eapply (Mod.well_scoped_init ctx).
  }

  i. hexploit (sim_fnsems WFT fn); et. intros SIM.
  destruct fn; cycle 1.
  { ii. ss. rewrite !alist_find_app_o in FIND |- *.
    destruct (alist_find _ (Mod.fnsems ms)) eqn: E0; inv FIND.
    - exploit SIM; et.
      { rewrite map_app in NODUPFS. eapply NoDup_app_remove_r; et. }
      { rewrite map_app in NODUPFT. eapply NoDup_app_remove_r; et. }
      i; des. rewrite x0. esplits; et.
      ii. destruct fs as [[[img msk] scp] bd].
      destruct ft as [[[img0 msk0] scp0] bd0].
      iIntros "[% H] I". des; subst.
      iApply isim_mono; cycle 1.
      { iApply isim_ctx; et; try apply Mod.well_scoped_init.
        - eapply sim_mon; et.
        - s. etrans; cycle 1.
          { eapply sub_perm_incl. et. }
          etrans; [|eapply Mod.well_scoped_fns].
          rewrite /fnsems_scopes. erewrite E0. refl.
        - s. etrans; [|eapply Mod.well_scoped_fns].
          rewrite /fnsems_scopes. erewrite x0. refl.
        - etrans; [eapply Mod.well_scoped_init|].
          eapply sub_perm_incl; et.
        - exploit x1; et. i. 
          iApply (x2 with "[H]"); et. iSplit; et.
      }
      i. iIntros "%". des; subst. iPureIntro. et.

    - destruct (alist_find None (Mod.fnsems mt)) eqn: E.
      { exfalso. rewrite map_app in NODUPFT.
        eapply NoDup_app_disjoint; eauto.
        - eapply alist_find_some, (in_map fst) in E. et.
        - eapply alist_find_some, (in_map fst) in H0. et.
      }
      rewrite H0. esplits; et. ii.
      destruct fs as [[[img msk] scp] bd].
      iIntros "[% H] I". des; subst.
      iApply isim_mono; cycle 1.
      { iApply (isim_reflR with "[H]"); et.
        - eapply WFT0.
        - s. etrans; [|eapply Mod.well_scoped_fns].
          rewrite /fnsems_scopes. erewrite H0. refl.
        - i. iIntros "%". des; subst. et.
        - i. iIntros "%". des; subst. iPureIntro.
          rewrite state_scopes_update. et.
        - exploit sim_initial; et; try rewrite !alist_find_map_snd.
          { rewrite E. et. }
          i. des. rewrite x1. do 4 iExists _. iSplit; et.
          rewrite /IstSB. iSplit.
          + iFrame. iPureIntro. split; try apply Mod.well_scoped_init.
            etrans; try apply Mod.well_scoped_init.
            eapply sub_perm_incl. et.
          + iSplit; et. iPureIntro. split; apply Mod.well_scoped_init.
      }
      i. iIntros "[% H]". subst. iPureIntro. et.
  }

  ii. ss. rewrite alist_find_app_o in FIND. des_ifs.
  {
    (* find in src/tgt module *)
    exploit sim_fnsems; et; try eapply WFS; try eapply WFT. i; des.
    esplits.
    { rewrite alist_find_app_o. des_ifs. }
    ii. iIntros "[% [% [% [% [% [[% H] %]]]]]] I". des; subst.
    iApply (isim_ctx with "[H I]"); et; i.
    - eapply sim_mon; et.
    - etrans; [|eapply sub_perm_incl; et].
      etrans; [|eapply Mod.well_scoped_fns].
      unfold fnsems_scopes. erewrite Heq. destruct fs, p. refl.
    - etrans; [|eapply Mod.well_scoped_fns].
      unfold fnsems_scopes. erewrite x0. destruct ft, p. refl.
    - exploit x1; cycle 3; i.
      + iApply (x2 with "[H]"); et.
      + et.
      + rewrite map_app in NODS. eapply NoDup_app_remove_r; et.
      + rewrite map_app in NODD. eapply NoDup_app_remove_r; et.
  }
  {
    exists fs. esplits; ss.
    { rewrite alist_find_app_o. des_ifs. exfalso.
      eapply alist_find_some in FIND, Heq0.
      eapply in_map with (f:=fst) in FIND, Heq0.
      rewrite map_app in NODUPFT.
      eapply NoDup_app_disjoint; eauto.
    }
    destruct fs as [[[img msk] sc] bd].
    inv WFTC. eapply isim_reflR; ss; i; eauto.
    - etrans; [|eapply Mod.well_scoped_fns].
      rewrite /fnsems_scopes. erewrite FIND. refl.
    - iIntros "%". des; subst; eauto.
    - iIntros "%". des; subst; eauto. iPureIntro.  esplits; eauto.
      + rewrite state_scopes_update. eauto.
      + rewrite state_scopes_update. eauto.
  }
Unshelve. all: et.
- rewrite map_app in NODS. eapply NoDup_app_remove_r. et.
- rewrite map_app in NODD. eapply NoDup_app_remove_r. et.
Qed.

Theorem main_adequacy (ms mt : Mod.t) IC Ist
    (SIM : ISim.t open ms mt IC Ist) :
  ctx_refines (ms, IC) (mt, emp%I).
Proof using.
  ii. s.
  destruct ctx as [ctx cond].
  assert (SIMC := SIM).
  ii. ss. eapply ISim_ctx with (ctx := ctx) in SIMC.
  split.
  { eapply ISim_wf; eauto. }
  ii. ss. eapply Own_split in SRC; eauto. des.
  eapply Own_split in SRC1; et; des; cycle 1.
  { eapply Own_wand_valid, WFR. rewrite SRC Own_op. iIntros "[_ ?]". iFrame; et. }
  rewrite winv_split_empty in SRC0.
  eapply Own_split in SRC0; et; des; cycle 1.
  { eapply Own_wand_valid, WFR. rewrite SRC Own_op. iIntros "[? _]". iFrame; et. }
  exists (a4 ⋅ a3); splits.
  { eapply Own_wand_valid, WFR. rewrite SRC SRC1 SRC0 !Own_op.
    iIntros "[[? ?] [? ?]]". iFrame. et. }
  { rewrite Own_op SRC4 SRC3. iIntros "[? ?]"; iFrame; et. }
  assert (WFT: Mod.wf mt) by (eapply wf_inv_l; et).
  ii. eapply lsim_adequacy, PR.
  - eapply ISim_adequacy; et.
    + instantiate (1:= a0⋅a5). rewrite SRC SRC0 SRC1 !Own_op.
      iIntros "[[? ?] [? ?]]". iFrame.
    + rewrite Own_op SRC2 SRC5. et.
    + eapply ISim_wf; eauto.
  - inv WFM. econs. ss. unfold map_snd.
    eapply eq_ind; [|].
    { inv SIM. eapply sub_perm_nodup. eapply sub_perm_cancel_tail.
      eapply sim_match; et. 
      rewrite map_app in wf_fns. eapply wf_fns. }
    rewrite -map_app map_map. f_equal.
    extensionalities. destruct H. ss.
Qed.

End ADEQUACY.

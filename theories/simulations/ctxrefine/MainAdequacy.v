Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod HMod SMod Sp.
Require Import ModSim ModSimFacts HModSim HModSimFacts.
Require Import ISim ISimInit ISimFacts Tactics TacticsInit.
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

Lemma sandbox_well_scoped `{Σ: GRA} {A} (img0 img1: bool) (msk0 msk1: _->bool) scp0 scp1 (itr : itree hmodE A)
    (IMPL: img0 → img1)
    (MASK : ∀ fn, msk0 fn → msk1 fn)
    (SCP : incl scp0 scp1) :
  SB.sandbox msk1 scp1 img1 (SB.sandbox msk0 scp0 img0 itr) = SB.sandbox msk0 scp0 img0 itr.
Proof.
  apply bisim_is_eq.
  revert_until Σ. ginit. gcofix CIH. i.
  ides itr.
  { rewrite! SBRed.ret. gstep. econs. eauto. }
  { rewrite! SBRed.tau. gstep. econs. gbase. eauto. }
  rewrite <- bind_trigger. rewrite! SBRed.bind.
  destruct e.
  {
    assert ((@ITree.trigger (@hmodE Σ) X (inl1 a)) = trigger a) by grind.
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

Lemma inv_sandbox_tau `{Σ: GRA} {X} img msk sc (itr : itree hmodE X)
    (SB : SB.sandbox img msk sc (tau;; itr) = tau;; itr) :
  SB.sandbox img msk sc itr = itr.
Proof.
  rewrite SBRed.tau in SB. inv SB.
  rewrite sandbox_well_scoped; ss.
Qed.

Lemma inv_sandbox_core `{Σ: GRA} {X Y} x img msk sc (ktr : X -> itree hmodE Y) (e: coreE X)
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

Lemma inv_sandbox_call `{Σ: GRA} {Y} x img msk sc (ktr : _ -> itree hmodE Y) f a
    (SB : SB.sandbox img msk sc (trigger (Call f a) >>= ktr) = trigger (Call f a) >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.call in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
  - rewrite bind_bind bind_vis in x. depdes x.
Qed.

Lemma inv_sandbox_spawn `{Σ: GRA} {Y} x img msk sc (ktr : _ -> itree hmodE Y) f a
    (SB : SB.sandbox img msk sc (trigger (Spawn f a) >>= ktr) = trigger (Spawn f a) >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.spawn in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
  - rewrite bind_bind bind_vis in x. depdes x.
Qed.

Lemma inv_sandbox_pg `{Σ: GRA} {X Y} x img msk sc (ktr : X -> itree hmodE Y) (pg : pgE X)
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

Lemma inv_sandbox_ag `{Σ: GRA} {X R} x img msk sc (ktr : X -> itree hmodE R) (e: agE X)
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
    (WF : HMod.wf (HMod.add ms0 ms1)) :
  HMod.wf ms0.
Proof.
  inv WF; ss. rewrite map_app in wf_fns. 
  econs; eauto using nodup_app_l.
Qed.

Ltac hstep := guclo hsimC_spec; econs; econs; eauto; econs; eauto.

Lemma hsim_ctx `{Σ: GRA} contextual fnsems_src fnsems_tgt fl_src fl_tgt fl_ctx Ist (img:bool) (msk: _->bool) scp scpC RR
    (FLS : fl_src = (List.map (map_snd SB.sandbox_body) fnsems_src))
    (FLT : fl_tgt = (List.map (map_snd SB.sandbox_body) fnsems_tgt))
    (WS : ∀ (fn : string) p (IN : alist_find fn fnsems_src = Some p), (p.2.1 → img) ∧ (∀ fn, p.1.1 fn → msk fn) ∧ incl p.1.2 scp)
    (WT : ∀ (fn : string) p (IN : alist_find fn fnsems_tgt = Some p), (p.2.1 → img) ∧ (∀ fn, p.1.1 fn → msk fn) ∧ incl p.1.2 scp)
    (DISJ : List.NoDup (scp ++ scpC))

    ps pt nths st_src st_tgt st_ctx itr_src itr_tgt fmr
    (SCPT : incl (state_scopes st_tgt) scp)
    (SCPS : incl (state_scopes st_src) scp)
    (SCPC : incl (state_scopes st_ctx) scpC)
    (ITRT : SB.sandbox msk scp img itr_tgt = itr_tgt)
    (ITRS : SB.sandbox msk scp img itr_src = itr_src)
    (SIM : hsim open fl_src fl_tgt Ist (ist_with_eq RR) ps pt nths
             (st_src, itr_src) (st_tgt, itr_tgt) fmr)
  :
  @hsim _ contextual (fl_src ++ fl_ctx) (fl_tgt ++ fl_ctx)
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
    eapply _hsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo hsim_wfC_spec. econs. i.
    guclo hsim_nodupC_spec. econs. i.
    exploit IN; i; des; eauto.
    { rewrite map_app in NODFS. eapply NoDup_app_remove_r. eauto. }
    { rewrite map_app in NODFT. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODS. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODD. eapply NoDup_app_remove_r. eauto. }
    clear IN. destruct x0; i; des; inv Heqp; try inv Heqp0.
    - hstep. iIntros "H". rewrite RET. iMod "H" as "[% H]". subst.
      iModIntro. iSplit; eauto. iExists st_src, st_tgt, st_ctx, st_ctx.
      repeat (iSplit; et).
    - hstep.
      { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iExists st_ctx, st_ctx.
        iSplit; eauto.
      }
      i. guclo hsim_wfC_spec. econs. i.
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
      unfold o_map in FUN. des_ifs. unfold SB.sandbox_body.
      rewrite sandbox_well_scoped; eauto; cycle 1.
      f_equal. extensionalities.
      rewrite ?SBRed.bind !SBRed.tau SBRed.ret.
      do 4 f_equal. extensionalities. eapply inv_sandbox_call; eauto. 
    - hstep. { rewrite alist_find_app_o. rewrite FUN. eauto. }
      eapply K; try refl; eauto. grind.
      rewrite! SBRed.bind.
      move FLT at bottom. move FUN at bottom.
      rewrite FLT in FUN.
      rewrite alist_find_map_snd in FUN.
      unfold o_map in FUN. des_ifs. unfold SB.sandbox_body.
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
        { eapply sandbox_well_scoped; et; refl. }
        { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
      + unfold triggerUB. ired. hstep. ss.

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
      { eapply sandbox_well_scoped; et. refl. }
      { f_equal. symmetry. eapply inv_sandbox_pg. eauto. }
    + rewrite SBRed.bind SBRed.put Heq !bind_trigger in H1.
      exfalso. unfold triggerUB in H1. rewrite bind_bind bind_vis in H1. ss.

  - assert (H1:=ITRS). 
    rewrite  -ITRS SBRed.bind SBRed.get. des_ifs.
    + hstep. eapply K; try refl; eauto.
      { eapply sandbox_well_scoped; et. refl. }
      erewrite alist_find_exists_l; eauto.
      repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
    + unfold triggerUB. ired. hstep. ss.

  - assert (H1:=ITRT). 
    rewrite  -ITRT SBRed.bind SBRed.get. des_ifs.
    + hstep. eapply K; try refl; eauto.
      { eapply sandbox_well_scoped; et. refl. }
      erewrite alist_find_exists_l; eauto.
      repeat f_equal. symmetry. eapply inv_sandbox_pg; eauto. 
    + rewrite SBRed.bind SBRed.get Heq !bind_trigger in H1.
      exfalso. unfold triggerUB in H1. rewrite bind_bind bind_vis in H1. ss.

  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. i. hexploit K; et; i; des. esplits; et. i.
    eapply H2; try refl; eauto using inv_sandbox_ag.
  - guclo @hsimC_spec. econs; esplits; et.
    eapply hsim_assume_precise_both; et.
    i. eapply K; try refl; eauto using inv_sandbox_ag.
  - hstep. eapply K; try refl; eauto.
    + eapply inv_sandbox_spawn in ITRT. eauto.
    + eapply inv_sandbox_spawn in ITRS. eauto.
  - hstep.
    { instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
      iModIntro. iFrame. iExists st_ctx, st_ctx.
      iSplit; eauto.
    }
    i. guclo hsim_wfC_spec. econs. i.
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
  (WFS : HMod.wf (HMod.add ms ctx))
  (WFT : HMod.wf (HMod.add mt ctx))
  (SCOPES : sub_perm (HMod.scopes ms) (HMod.scopes mt))
  (NODUPFT : List.NoDup (List.map fst (HMod.fnsems mt ++ HMod.fnsems ctx)))
  (NODUPFS : List.NoDup (List.map fst (HMod.fnsems ms ++ HMod.fnsems ctx)))
  (IMON : ∀ nths0 nths', nths0 <= nths' → ∀ st_src st_tgt,
          Ist nths0 st_src st_tgt ⊢ Ist nths' st_src st_tgt)
  (MON: Ist_monotone Ist)
  :
  ∀ (arg : Any.t) (nths : nat) (st_src st_tgt st_ctx : list (key * Any.t))
    (SCOPEFS: incl fs.1.2 (HMod.scopes mt))
    (SCOPEFT: incl ft.1.2 (HMod.scopes mt))
    (SCOPES: incl (map (fst∘fst) st_src) (HMod.scopes mt))
    (SCOPET: incl (map (fst∘fst) st_tgt) (HMod.scopes mt))
    (SCOPEC: incl (map (fst∘fst) st_ctx) (HMod.scopes ctx)),
      isim open (map (map_snd SB.sandbox_body) (HMod.fnsems ms))
           (map (map_snd SB.sandbox_body) (HMod.fnsems mt)) Ist ibot ibot
           (ist_with_eq RR) false false nths
           (st_src, SB.sandbox_body fs arg)
           (st_tgt, SB.sandbox_body ft arg)
      ⊢ @isim _ contextual
          (map (map_snd SB.sandbox_body) (HMod.fnsems ms ++ HMod.fnsems ctx))
         (map (map_snd SB.sandbox_body) (HMod.fnsems mt ++ HMod.fnsems ctx))
         (IstProd (IstSB (HMod.scopes mt) Ist) (IstSB (HMod.scopes ctx) IstEq))
         ibot ibot Any.t Any.t
         (ist_with_eq
           (IstProd (IstSB (HMod.scopes mt) RR) (IstSB (HMod.scopes ctx) IstEq)))
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
  rewrite !map_app. eapply hsim_ctx; try apply SIM; cycle 8; i.
  - instantiate (1:= true).
    instantiate (1:= wmask_all).
    rewrite sandbox_well_scoped; i; bsimpl; et.
  - rewrite sandbox_well_scoped; i; bsimpl; et.
  - refl.
  - refl.
  - bsimpl. esplits; et.
    etrans; [|eapply sub_perm_incl; et].
    etrans; [|eapply HMod.well_scoped_fns].
    unfold fnsems_scopes. erewrite IN. destruct fs, p. refl.
  - bsimpl. esplits; et.
    etrans; [|eapply HMod.well_scoped_fns].
    unfold fnsems_scopes. erewrite IN. destruct ft, p. refl.
  - destruct WFT. et.
  - et.
  - etrans; [apply SCOPES0|]. refl. 
  - et.
Qed.

Lemma hmod_sim_ctx `{Σ: GRA} contextual (ms mt ctx : HMod.t) IC Ist
  (SIM : HSim.t open ms mt IC Ist)
  :
  HSim.t contextual (ms ★ ctx) (mt ★ ctx) IC 
    (IstProd (IstSB mt.(HMod.scopes) Ist)
             (IstSB ctx.(HMod.scopes) IstEq)).
Proof.
  inv SIM.
  econs; intro WFTC; dup WFTC; eapply wf_inv_l in WFTC0; rename WFTC0 into WFT;
    assert (WFS: HMod.wf ms) by (eapply Hsim_wf; et; econs; et).
  {
    assert (WFSC: HMod.wf (ms ★ ctx)).
    { econs.
      * eapply sub_perm_nodup; [|eapply HMod.wf_fns, WFTC].
        s. rewrite !map_app. eapply sub_perm_cancel_tail. et.
      * eapply sub_perm_nodup; [|eapply HMod.wf_scopes, WFTC].
        s. eapply sub_perm_cancel_tail. et.
    }

    specialize (sim_initial WFT).
    r. r in sim_initial. revert sim_initial.
    destruct (HMod.initial_code _) eqn: E0; [destruct o|]; cycle 1.
    - destruct (HMod.initial_code mt) eqn: E1; ss. destruct o; ss; i.
      rewrite E0 E1; ss. destruct (HMod.initial_code ctx) eqn: E2; ss.
    - destruct (HMod.initial_code mt) eqn: E1; ss. i.
      rewrite E0 E1; ss. destruct (HMod.initial_code ctx) eqn: E2; ss.
      { destruct o; ss. i.
        iIntros "H". iApply isim_mono; cycle 1.
        { iApply isim_reflR; cycle 7; et.
          - rewrite /IstProd. iExists _,_,_,_. iSplit; et.
            rewrite /IstSB. iSplit; cycle 1.
            + iPureIntro. esplits; et; eapply (HMod.well_scoped_init ctx).
            + iSplit.
              * iPureIntro. esplits; cycle 1.
                { eapply (HMod.well_scoped_init mt). }
                etrans; [eapply (HMod.well_scoped_init ms)|].
                eapply sub_perm_incl; et.
              * rewrite sim_initial. et.
          - eapply WFTC.
          - etrans; [|eapply (HMod.well_scoped_initcode ctx)].
            rewrite E2. s. refl.
          - i. iIntros "%". des. subst. et.
          - i. iIntros "%". des. subst. iPureIntro. esplits; et.
            + rewrite state_scopes_update. et.
            + rewrite state_scopes_update. et.
        }
        i. iIntros "[% H]". subst. iSplit; et.
      }
      rewrite sim_initial. iIntros "H".
      unfold IstProd. iExists _, _, _, _. iFrame. iPureIntro.
      esplits; eauto; try eapply HMod.well_scoped_init.
      etrans; [eapply HMod.well_scoped_init|].
      eapply sub_perm_incl, sim_scopes; et.
    - destruct (HMod.initial_code mt) eqn: E1; ss.
      destruct o; ss. i. rewrite E0 E1. s.
      destruct (HMod.initial_code ctx) eqn: E2; ss.
      i. iIntros "H".
      exploit sim_initial; et; i.
      { rewrite map_app in NODS. eapply NoDup_app_remove_r; et. }
      { rewrite map_app in NODD. eapply NoDup_app_remove_r; et. }
      i. rewrite x0.
      rewrite isim_ctx.
      + rewrite !map_app. iApply isim_mono; cycle 1.
        * iApply "H".
        * i. iIntros "%". des; subst. iPureIntro. et.
      + et.
      + et.
      + et.
      + eapply WFTC.
      + eapply WFSC.
      + eapply sim_mon; et.
      + eapply sim_mon; et.
      + etrans; [|eapply sub_perm_incl; et].
        etrans; [|eapply HMod.well_scoped_initcode].
        rewrite E0. s. refl.
      + etrans; [|eapply HMod.well_scoped_initcode].
        rewrite E1. s. refl.
      + etrans; [|eapply sub_perm_incl; et].
        eapply HMod.well_scoped_init.
      + eapply HMod.well_scoped_init.
      + eapply HMod.well_scoped_init.
  }
  {
    ii. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & (% & H) & %)".
    des; subst. rewrite (sim_mon WFT _ _ LE).
    repeat iExists _. iFrame. iPureIntro. esplits; eauto.
  }
  { eapply sub_perm_cancel_tail. et. }
  { rewrite ?map_app. eapply sub_perm_cancel_tail. eauto. }

  r. i. ss. rewrite alist_find_app_o in FIND. des_ifs.
  {
    (* find in src/tgt module *)
    exploit sim_fnsems; et; try eapply WFS; try eapply WFT. i; des.
    esplits.
    { rewrite alist_find_app_o. des_ifs. }
    ii. iIntros "[% [% [% [% [% [[% H] %]]]]]]". des; subst.
    iApply (isim_ctx with "[H]"); [..|rewrite x1]; et; i.
    - eapply sim_mon; et.
    - etrans; [|eapply sub_perm_incl; et].
      etrans; [|eapply HMod.well_scoped_fns].
      unfold fnsems_scopes. erewrite Heq. destruct fs, p. refl.
    - etrans; [|eapply HMod.well_scoped_fns].
      unfold fnsems_scopes. erewrite x0. destruct ft, p. refl.
    - rewrite map_app in NODS. eapply NoDup_app_remove_r; et.
    - rewrite map_app in NODD. eapply NoDup_app_remove_r; et.
  }    
  {
    exists fs. esplits; ss.
    { rewrite alist_find_app_o. des_ifs. exfalso.
      eapply alist_find_some in FIND, Heq0.
      eapply in_map with (f:=fst) in FIND, Heq0.
      rewrite map_app in NODUPFT.
      eapply NoDup_app_disjoint; eauto.
    }
    destruct fs as [[msk sc] [img itr]].
    inv WFTC. eapply isim_reflR; ss; i; eauto.
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
  { eapply Hsim_wf; eauto. }
  ii. hexploit Own_split; eauto; intros [a1 [a2 [Ha [H1 H2]]]].
  exists a2; splits; eauto.
  { eapply cmra_valid_op_r; erewrite <- Ha; ss. }
  { iIntros "H"; iSplitR "H"; ss; iApply H2; done. }
  assert (WFT: HMod.wf mt) by (eapply wf_inv_l; et).
  
  ii. subst. eapply adequacy_modsem, PR.
  - eapply (Hsim_adequacy _ _ rs a1 a2); eauto.
    { rewrite Ha; iIntros "[H1 H2]"; iFrame. }
    { eapply Hsim_wf; eauto. }
  - inv WFM. econs. ss. unfold map_snd.
    eapply eq_ind; [|].
    { inv SIM. eapply sub_perm_nodup. eapply sub_perm_cancel_tail.
      eapply sim_match; et. 
      rewrite map_app in wf_fns. eapply wf_fns. }
    rewrite -map_app map_map. f_equal.
    extensionalities. destruct H. ss.
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

Lemma hmod_add_comm `{Σ: GRA} contextual ms0 ms1:
  HSim.t contextual (ms0 ★ ms1) (ms1 ★ ms0) (emp%I)
    (IstSB (HMod.scopes (ms0 ★ ms1)) perm_Ist).
Proof.
  econs; ss; i.
  {
    r; s. destruct (HMod.initial_code ms0); s.
    { destruct (HMod.initial_code ms1); ss. destruct o; ss.
      i. iIntros. iApply isim_mono; cycle 1.
      - iApply isim_nodup. iIntros (? ? ? ?).
        iApply isim_refl.
        + ii. iIntros "%". iPureIntro. des. esplits; et.
        + ii. iIntros "%". iPureIntro. des. eapply alist_permutation_find; et.
        + ii. iIntros "%". iPureIntro. des. esplits; et.
          * rewrite state_scopes_update. et.
          * rewrite state_scopes_update. et.
          * eapply alist_upd_perm; et.
        + iPureIntro. esplits; et.
          * rewrite /state_scopes map_app.
            eapply incl_app; [apply incl_appl|apply incl_appr];
              eapply HMod.well_scoped_init.
          * rewrite /state_scopes map_app.
            eapply incl_app; [apply incl_appr|apply incl_appl];
              eapply HMod.well_scoped_init.
          * eapply Permutation_app_comm.
      - i. iIntros "%". iPureIntro. des; et.
    }
    { destruct (HMod.initial_code ms1); ss.
      { destruct o; ss. i.
        i. iIntros. iApply isim_mono; cycle 1.
        - iApply isim_nodup. iIntros (? ? ? ?).
          iApply isim_refl.
          + ii. iIntros "%". iPureIntro. des. esplits; et.
          + ii. iIntros "%". iPureIntro. des. eapply alist_permutation_find; et.
          + ii. iIntros "%". iPureIntro. des. esplits; et.
            * rewrite state_scopes_update. et.
            * rewrite state_scopes_update. et.
            * eapply alist_upd_perm; et.
          + iPureIntro. esplits; et.
            * rewrite /state_scopes map_app.
              eapply incl_app; [apply incl_appl|apply incl_appr];
                eapply HMod.well_scoped_init.
            * rewrite /state_scopes map_app.
              eapply incl_app; [apply incl_appr|apply incl_appl];
                eapply HMod.well_scoped_init.
            * eapply Permutation_app_comm.
        - i. iIntros "%". iPureIntro. des; et.
      }
      iIntros. iPureIntro. esplits; et.
      - rewrite /state_scopes map_app.
        eapply incl_app; [apply incl_appl|apply incl_appr];
          eapply HMod.well_scoped_init.
      - rewrite /state_scopes map_app.
        eapply incl_app; [apply incl_appr|apply incl_appl];
          eapply HMod.well_scoped_init.
      - eapply Permutation_app_comm.
    }
  }
  { apply sub_perm_comm. }
  { rewrite ?map_app; i. apply sub_perm_comm. }
  ii. eapply alist_find_comm in FIND; cycle 1. 
  { inv WFT; ss. }
  esplits; eauto.

  (* simulation *)
  ii. destruct fs as [[msk scp] [img i]]. unfold SB.sandbox_body. s.
  generalize (i arg) as it. clear FIND i arg.
  combine_quant NODD.
  combine_quant NODS.
  combine_quant st_tgt.
  combine_quant st_src.
  combine_quant nths.
  eapply isim_coind. i.
  destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
  iIntros "(%IST & #CIH)". des.
  assert (CASE := case_itrH it); des; subst.
  - step. eauto.
  - steps_l. steps_r. by_coind "CIH". eauto.
  - destruct img.
    + steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
    + rewrite SBRed.bind SBRed.Assume. s. steps_l. ss.
  - steps_l. steps_r. step. by_coind "CIH". eauto.
  - steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
  - destruct c.
    + norm_l. norm_r. rewrite! SBRed.call. des_ifs; ss.
      * iApply isim_call. iSplit; eauto. iIntros (? ? ? ? ? ?) "IST0".
        steps_l. steps_r. by_coind "CIH". eauto.
      * steps_l. ss.
    + norm_l. norm_r. rewrite! SBRed.spawn. des_ifs; ss.
      * iApply isim_spawn.
        steps_l. steps_r. by_coind "CIH". eauto.
      * steps_l. ss.
    + yield ""; eauto. by_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sput_src. iApply isim_sput_tgt.
      by_coind "CIH". unfold perm_Ist. 
      iPureIntro. rewrite !state_scopes_update. esplits; eauto. 
      eapply alist_upd_perm; eauto.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { steps_l. ss. }
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝)%I as "%".
      { iPureIntro. eapply alist_permutation_find; eauto. }
      rewrite H1. by_coind "CIH". eauto.
  - destruct e.
    + steps_r. force_l. instantiate (1:= q). steps_l. by_coind "CIH". eauto. 
    + rewrite SBRed.bind SBRed.take. des_ifs.
      * steps_l. force_r. instantiate (1:= q). steps_r. by_coind "CIH". eauto.
      * steps_l. ss.
    + step. by_coind "CIH". eauto. 
  Unshelve. all : eauto. 
  { eapply alist_upd_nodup. eauto. }
  { eapply alist_upd_nodup. eauto. }
Qed.

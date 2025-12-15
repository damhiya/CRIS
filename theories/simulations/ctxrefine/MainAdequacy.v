Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimFacts MSim MSimFacts MSimCommon.
Require Import ISim ISimFacts ClosedAdequacy TacticsInit.
Require Import CtxRefine.

Lemma inv_sandbox_event `{Σ : GRA} {X Y} x msk (ktr : _ → itree crisE Y) (e : crisE X) :
  SB.sandbox msk (trigger e >>= ktr) = trigger e >>= ktr →
  SB.sandbox msk (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_tau `{Σ : GRA} {X} msk (ktr : itree crisE X) :
  (SB.sandbox msk (tau;; ktr) = tau;; ktr) →
  SB.sandbox msk ktr = ktr.
Proof. rewrite SBRed.tau; grind. Qed.

Lemma sandbox_well_scoped `{Σ : GRA} {A} (msk0 msk1 : emask) (itr : itree crisE A) :
  (∀ X e, msk0 X e → msk1 X e) →
  SB.sandbox msk1 (SB.sandbox msk0 itr) = SB.sandbox msk0 itr.
Proof.
  intros Hmsk; apply bisim_is_eq; revert itr; ginit; gcofix CIH; intros itr.
  ides itr.
  { rewrite !SBRed.ret; gstep; econs; eauto. }
  { rewrite !SBRed.tau; gstep; econs; eauto.
    gbase; eauto.
  }
  { rewrite !SBRed.vis; des_ifs.
    { rewrite SBRed.vis; des_ifs.
      { gstep; econs; intros v; eauto.
        gbase; eauto.
      }
      { apply Hmsk in Heq; bsimpl; clarify. }
    }
    { rewrite SBRed.vis; des_ifs; gstep; econs; ii; ss. }
  }
Qed.
(* Set Implicit Arguments. *)

(* AUX *)

(* Lemma alist_upd_fst_in {V} a (k : key) (v : V) l
    (IN : In a (List.map (fst ∘ fst) l)) :
  In a (List.map (fst ∘ fst) (alist_upd k v l)).
Proof.
  unfold alist_upd in *.
  induction l; ss; i; rewrite eq_rel_dec_correct; des_ifs; ss; des; eauto.
Qed. *)

(* Lemma sandbox_well_scoped
    `{Σ : GRA} {A} (img0 img1 : bool) (msk0 msk1 : _->bool) scp0 scp1 (itr : itree crisE A)
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
    - rewrite !SBRed.AssumeRes !bind_trigger.
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
  {
    rewrite! SBRed.gettid. rewrite! bind_trigger.
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
0Qed.

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


Lemma inv_sandbox_spawn `{Σ: GRA} {Y} x img msk sc (ktr : _ -> itree crisE Y) f a
    (SB : SB.sandbox img msk sc (trigger (Spawn f a) >>= ktr) = trigger (Spawn f a) >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.spawn in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
  - rewrite bind_bind bind_vis in x. depdes x.
Qed.

Lemma inv_sandbox_gettid `{Σ : GRA} {Y} x img msk sc (ktr : _ -> itree crisE Y)
    (SB : SB.sandbox img msk sc (trigger GetTid >>= ktr) = trigger GetTid >>= ktr) :
  SB.sandbox img msk sc (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.gettid in SB.
  des_ifs; rewrite! bind_trigger in SB; depdes SB.
  - eapply equal_f in x. eauto.
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
  - rewrite SBRed.bind SBRed.AssumeRes in SB.
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

Lemma msim_ctx
    `{Σ: GRA} contextual fnsems_src fnsems_tgt (fl_src fl_tgt fl_ctx: alist (option string) _)
    Ist (img : bool) (msk : _ -> bool) scp scpC RR
    (FLS : fl_src = (List.map (map_snd SB.sandbox_body) fnsems_src))
    (FLT : fl_tgt = (List.map (map_snd SB.sandbox_body) fnsems_tgt))
    (WS : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_src = Some (img0,msk0,scp0,bd0)), (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (WT : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_tgt = Some (img0,msk0,scp0,bd0)), (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (DISJ : List.NoDup (scp ++ scpC))

    ps pt st_src st_tgt st_ctx itr_src itr_tgt fmr
    (SCPT : incl (state_scopes st_tgt) scp)
    (SCPS : incl (state_scopes st_src) scp)
    (SCPC : incl (state_scopes st_ctx) scpC)
    (ITRT : SB.sandbox img msk scp itr_tgt = itr_tgt)
    (ITRS : SB.sandbox img msk scp itr_src = itr_src)
    (SIM : msim open fl_src fl_tgt Ist (ist_with_eq RR) ps pt
             (st_src, itr_src) (st_tgt, itr_tgt) fmr)
  :
  @msim _ contextual (fl_src ++ fl_ctx) (fl_tgt ++ fl_ctx)
    (IstProd (IstSB scp Ist) (IstSB scpC IstEq)) Any.t Any.t
    (ist_with_eq (IstProd (IstSB scp RR) (IstSB scpC IstEq))) ps pt
    (st_src ++ st_ctx, itr_src) (st_tgt ++ st_ctx, itr_tgt) fmr.
  Proof.
    guardH FLS. guardH FLT. hdes.
    move WS0 at top. move WS2 at top. move WS3 at top.
    move WT0 at top. move WT2 at top. move WT3 at top.
    ginit. s. revert_until DISJ. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before CIH. revert_until SIM. punfold SIM.
    pattern ps, pt, p, p0, fmr.
    eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo msim_wfC_spec. econs. i.
    guclo msim_nodupC_spec. econs. i.
    exploit IN; i; des; eauto.
    { rewrite map_app in NODFS. eapply NoDup_app_remove_r. eauto. }
    { rewrite map_app in NODFT. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODS. eapply NoDup_app_remove_r. eauto. }
    { subst. rewrite map_app in NODT. eapply NoDup_app_remove_r. eauto. }
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
      eapply K; try refl; eauto using inv_sandbox_event; try nia; cycle 3.
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
      do 4 f_equal. extensionalities. eapply inv_sandbox_event; eauto.
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
      do 4 f_equal. extensionalities. eapply inv_sandbox_event; eauto.
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
  - mstep. i. eapply (K fmr1); et; i; des.
    try refl; eauto using inv_sandbox_ag.
  (* - guclo @msimC_spec. econs; esplits; et.
    eapply msim_assume_res_both; et.
    i. eapply K; try refl; eauto using inv_sandbox_ag. *)
  - mstep. intros tid; eapply (K tid); try refl; eauto.
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

  - mstep. intros tid; eapply (K tid); try refl; eauto.
    + eapply inv_sandbox_gettid in ITRT. eauto.
    + eapply inv_sandbox_gettid in ITRS. eauto.

  - gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; try refl; eauto.
Qed.

 *)
Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto.

Local Lemma Own_Ist `{Σ : GRA} FR fmr scp Ist st_src st_tgt :
  ✓ fmr →
  (Own fmr ⊢ |==> IstProd (IstSB scp Ist) IstEq st_src st_tgt ∗ FR) →
  ∃ st_srcL st_tgtL st_ctx,
    st_src = union_with (const (const (Some None))) st_srcL st_ctx ∧
    st_tgt = union_with (const (const (Some None))) st_tgtL st_ctx ∧
    (elements (dom st_srcL)).*1 ⊆ scp ∧
    (elements (dom st_tgtL)).*1 ⊆ scp ∧
    (Own fmr ⊢ |==> Ist st_srcL st_tgtL ∗ FR).
Proof.
  intros Hfmr2val Hfmr2.
  eapply Own_bupd_split in Hfmr2 as [fmr21 [fmr22 [Hfmr2 [Hfmr21 Hfmr22]]]]; eauto.
  eapply Own_general_soundness in Hfmr21; eauto; cycle 1.
  { eapply Own_wand_valid; [iIntros "F"; iMod (Hfmr2 with "F") as "[$ _]"|]; done. }
  rewrite /IstProd /IstSB /IstEq in Hfmr21; uPred.unseal_in Hfmr21.
  destruct Hfmr21 as [st_srcL [st_tgtL [st_srcR [st_tgtR Hfmr21]]]].    
  destruct Hfmr21 as [? [fmr212 [Hfmr21 [[-> ->] Hfmr212]]]].
  destruct Hfmr212 as [fmr2121 [? [Hfmr212 [[? [? [Hfmr2121 [[? ?] Hfmr21211]]]] ->]]]].
  eapply Own_general_completeness in Hfmr21211.
  esplits; eauto.
  rewrite Hfmr2 Hfmr21 Hfmr212 Hfmr2121 ?Own_op Hfmr21211 Hfmr22.
  iIntros "> [[? [[? ?] ?]] ?]"; by iFrame.
Qed.

Lemma msim_ctx
    `{Σ : GRA} contextual ms mt ctx
    Ist RR scp msk
    (* (img : bool) (msk : _ -> bool) scp scpC  *)
    ps pt st_src st_tgt st_ctx itr_src itr_tgt fmr
    (* (WS : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_src = Some (img0,msk0,scp0,bd0)),
      (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (WT : ∀ fn img0 msk0 scp0 bd0 (IN : alist_find (Some fn) fnsems_tgt = Some (img0,msk0,scp0,bd0)),
      (img0 → img) ∧ (∀ fn, msk0 fn → msk fn) ∧ incl scp0 scp)
    (DISJ : List.NoDup (scp ++ scpC)) *)

    
    (* (SCPT : incl (state_scopes st_tgt) scp)
    (SCPS : incl (state_scopes st_src) scp)
    (SCPC : incl (state_scopes st_ctx) scpC)
    (ITRT : SB.sandbox img msk scp itr_tgt = itr_tgt)
    (ITRS : SB.sandbox img msk scp itr_src = itr_src) *)
  :
  (elements (dom st_src)).*1 ⊆ scp →
  (elements (dom st_tgt)).*1 ⊆ scp →
  SB.sandbox msk itr_src = itr_src →
  SB.sandbox msk itr_tgt = itr_tgt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  msim open
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt))
    Ist (ist_with_eq RR) ps pt (st_src, itr_src) (st_tgt, itr_tgt) fmr →
  @msim _ contextual
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (ms ★ ctx)))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (mt ★ ctx)))
    (IstProd (IstSB scp Ist) IstEq) Any.t Any.t
    (ist_with_eq (IstProd (IstSB scp RR) IstEq)) ps pt
    (union_with (const (const (Some None))) st_src st_ctx, itr_src) 
    (union_with (const (const (Some None))) st_tgt st_ctx, itr_tgt) fmr.
Proof.
  (* guardH FLS. guardH FLT. hdes. *)
  (* move WS0 at top. move WS2 at top. move WS3 at top. *)
  (* move WT0 at top. move WT2 at top. move WT3 at top. *)
  ginit. intros ???? Hwfs Hwft; move Hwfs at top; move Hwft at top.
  revert_until msk. gcofix CIH.
  intros ps pt st_src st_tgt st_ctx itr_src itr_tgt fmr ? ? Hsbs Hsbt Hsim.
  remember (st_src, itr_src) as ss. remember (st_tgt, itr_tgt) as st.
  move Hsim before CIH. revert_until Hsim. punfold Hsim.
  pattern ps, pt, ss, st, fmr.
  eapply _msim_tarski, Hsim; clear Hsim fmr; intros ???? fmr Hin ????? ???? -> ->.
  guclo msim_wfC_spec. econs. intros Hval.
  guclo msim_nodupC_spec; econs; intros Hfs Hft Hss Hst; hexploit Hin; ss.
  { move: Hfs; rewrite ?map_Forall_lookup => Hfs i x; move: Hfs => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ ms !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }
  { move: Hft; rewrite ?map_Forall_lookup => Hft i x; move: Hft => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ mt !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }
  { move: Hss; rewrite ?map_Forall_lookup => Hss i x; move: Hss => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (st_src !! i) as [[|]|]; destruct (st_ctx !! i); ss; i; clarify.
  }
  { move: Hst; rewrite ?map_Forall_lookup => Hst i x; move: Hst => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (st_tgt !! i) as [[|]|]; destruct (st_ctx !! i); ss; i; clarify.
  }

  clear Hin; intros Hin.
  destruct Hin as [fmr1 [Hin Hfmr]]; eauto.
  inv Hin; try by (mstep; eauto using inv_sandbox_event, inv_sandbox_tau).
  { mstep; rewrite RET; iIntros "> [-> $] !>"; iSplit; [done|iExists _, _; iSplit; eauto]. }
  { mstep.
    { instantiate (1:=FR). rewrite INV; iIntros "> [$ $] !>"; iExists _, _; iSplit; eauto. }
    intros ? st_src2 st_tgt2 fmr2 Hfmr2.
    guclo msim_wfC_spec; econs; intros Hfmr2val.
    hexploit Own_Ist; eauto; intros [? [? [? [-> [-> [? [? Hfmr22]]]]]]].
    eapply K; eauto using inv_sandbox_event.
  }
  { mstep; cycle 1.
    { eapply K; eauto using inv_sandbox_event.
      ired. rewrite SBRed.bind; ired.
      assert (SB.sandbox msk (f varg) = f varg).
      { admit. }
      rewrite H2; grind.
      rewrite SBRed.tau; ired; grind; eauto using inv_sandbox_event.
    }
    admit.
  }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { mstep.
    { instantiate (1:=FR). rewrite INV; iIntros "> [$ $] !>"; iExists _, _; iSplit; eauto. }
    intros st_src2 st_tgt2 fmr2 Hfmr2.
    guclo msim_wfC_spec; econs; intros Hfmr2val.
    hexploit Own_Ist; eauto; intros [? [? [? [-> [-> [? [? Hfmr22]]]]]]].
    eapply K; eauto using inv_sandbox_event.
  }
  { gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; try refl; eauto.
  }

    (* destruct x0; i; des; inv Heqp; try inv Heqp0.
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
      eapply K; try refl; eauto using inv_sandbox_event; try nia; cycle 3.
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
      do 4 f_equal. extensionalities. eapply inv_sandbox_event; eauto.
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
      do 4 f_equal. extensionalities. eapply inv_sandbox_event; eauto.
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
  - mstep. i. eapply (K fmr1); et; i; des.
    try refl; eauto using inv_sandbox_ag.
  (* - guclo @msimC_spec. econs; esplits; et.
    eapply msim_assume_res_both; et.
    i. eapply K; try refl; eauto using inv_sandbox_ag. *)
  - mstep. intros tid; eapply (K tid); try refl; eauto.
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

  - mstep. intros tid; eapply (K tid); try refl; eauto.
    + eapply inv_sandbox_gettid in ITRT. eauto.
    + eapply inv_sandbox_gettid in ITRS. eauto.

  - gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; try refl; eauto. *)
Admitted.

Lemma isim_ctx `{Σ : GRA} contextual RR fs ft ms mt ctx Ist :
  (* (WFS : Mod.wf (ms ★ ctx))
  (WFT : Mod.wf (mt ★ ctx))
  (SCOPES : sub_perm (Mod.scopes ms) (Mod.scopes mt))
  (NODUPFT : List.NoDup (List.map fst (Mod.fnsems mt ++ Mod.fnsems ctx)))
  (NODUPFS : List.NoDup (List.map fst (Mod.fnsems ms ++ Mod.fnsems ctx))) *)
  ∀ (arg : Any.t) st_src st_tgt st_ctx,
    (elements (dom st_src)).*1 ⊆ Mod.scopes mt →
    (elements (dom st_tgt)).*1 ⊆ Mod.scopes mt →
    Mod.scopes ms ⊆+ Mod.scopes mt →
    Mod.wf (ms ★ ctx) →
    Mod.wf (mt ★ ctx) →
    (* (SCOPEFS: incl fs.1.2 (Mod.scopes mt))
    (SCOPEFT: incl ft.1.2 (Mod.scopes mt))
    (SCOPES: incl (map (fst∘fst) st_src) (Mod.scopes mt))
    (SCOPET: incl (map (fst∘fst) st_tgt) (Mod.scopes mt))
    (SCOPEC: incl (map (fst∘fst) st_ctx) (Mod.scopes ctx)),
     *)
    isim open
      ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms))
      ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt))
      Ist ibot ibot (ist_with_eq RR) false false
      (st_src, SB.sandbox_body fs arg)
      (st_tgt, SB.sandbox_body ft arg) ⊢
    @isim _ contextual
      ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (ms ★ ctx)))
      ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (mt ★ ctx)))
      (IstProd (IstSB (Mod.scopes mt) Ist) IstEq)
      ibot ibot Any.t Any.t
      (ist_with_eq (IstProd (IstSB (Mod.scopes mt) RR) IstEq))
      false false
      (union_with (const (const (Some None))) st_src st_ctx, SB.sandbox_body fs arg)
      (union_with (const (const (Some None))) st_tgt st_ctx, SB.sandbox_body ft arg).
Proof.
  intros arg st_src st_tgt st_ctx Hsrc Htgt Hscp Hwfs Hwft; apply entails_pointwise => r Hsim.
  eapply isim_init in Hsim; eauto.
  eapply gpaco8_mon in Hsim; try apply iunlift_ibot.
  eapply gpaco8_init in Hsim; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco; right.
  eapply paco8_mon_bot; eauto.
  destruct fs as [msks bds]; destruct ft as [mskt bdt].
  eapply msim_ctx; eauto.
  { rewrite /SB.sandbox_body /=. admit.
  }
  { admit. }
Admitted.
  (* etrans; eauto.
  apply submseteq_Permutation in Hscp as [? ->]; set_solver.  *)
(* Qed. *)
  (* ii. rewrite /SB.sandbox_body.
  eapply entails_pointwise. intros fmr SIM.
  eapply isim_init in SIM; cycle 1; et.
  eapply gpaco8_mon in SIM; try apply iunlift_ibot.
  eapply gpaco8_init in SIM; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco. right.
  eapply paco8_mon_bot; et.
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
Qed. *)

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_ctx contextual (ms mt ctx : Mod.t) IC Ist : 
    ISim.t open ms mt IC Ist →
    ISim.t contextual (ms ★ ctx) (mt ★ ctx) IC (IstProd (IstSB mt.(Mod.scopes) Ist) IstEq).
  Proof using.
    intros Hsim; apply ISim.t_strong; intros Hwftctx.
    hexploit Mod.add_wf; eauto; intros [Hwft Hwfctx].
    hexploit ISim_wf; eauto; intros Hwfs.
    pose Hsim as Hsim'; destruct Hsim' as [Hscp Hic Hsimfun].
    eapply ISim_reflR; eauto.
    { intros fn Hfns; hexploit ISim_match; eauto; intros [fbot Hfnt]%elem_of_dom.
      apply elem_of_dom in Hfns as [fbos Hfns].
      assert (Hfnctx : Mod.fnsems ctx !! fn = None).
      { destruct (_ ctx !! fn) eqn : Hctx; ss.
        exfalso; hexploit Mod.wf_fns; [apply Hwftctx|].
        rewrite map_Forall_lookup /= => /(_ fn None); rewrite lookup_union_with Hfnt Hctx //=.
        intros []; ss.
      }
      rewrite /ISim.sim_fun /= ?lookup_fmap ?lookup_union_with Hfnctx Hfns Hfnt /=.
      destruct fbos as [fbs|]; ss; cycle 1.
      { hexploit (Hsimfun Hwft fn); rewrite /ISim.sim_fun lookup_fmap Hfns /= Hfnt //. }
      destruct fbot as [fbt|]; ss; cycle 1.
      { hexploit (Hsimfun Hwft fn); rewrite /ISim.sim_fun ?lookup_fmap Hfns Hfnt /=.
        intros Hf; hexploit Hf; eauto; i; des; clarify.
      }
      intros _ _; eexists; split; first refl.
      intros arg st_src st_tgt.
      iIntros "[% [% [% [%st_ctx [[-> ->] [[[% %] IST] ->]]]]]] WINV".
      iApply isim_ctx; eauto. { admit. }
      hexploit (Hsimfun Hwft fn); rewrite /ISim.sim_fun ?lookup_fmap Hfns Hfnt /= => /(_ Hwfs Hwft).
      intros [? [? Hisim]]; clarify; move : Hisim => /(_ arg st_srcL st_tgtL); intros Hisim.
      iApply (Hisim with "IST WINV").
    }
    { intros ? ?; eapply ISim_match; eauto. }
    { rewrite Hic //; iIntros "$"; iExists _, _; iSplit; eauto.
      iSplit; eauto.
      iPureIntro; split; [|destruct mt; ss].
      etrans; first apply (Mod.well_scoped_init).
      hexploit Hscp; eauto; clear Hscp; intros Hscp.
      apply submseteq_Permutation in Hscp as [? ->]; set_solver.
    }
Admitted.
Search Mod.t ISim.t Mod.wf.
    (* econs; intros [Hwft Hwfctx]%Mod.add_wf.
    { apply submseteq_app; eauto. }
    { rewrite Hic //; iIntros "$"; iExists _, _; iSplit; eauto.
      iSplit; eauto.
      { iPureIntro; split; [|destruct mt; ss].
        etrans; first apply (Mod.well_scoped_init).
        hexploit Hscp; eauto; clear Hscp; intros Hscp.
        apply submseteq_Permutation in Hscp as [? ->]; set_solver.
      }
      iSplit; [iPureIntro; split; destruct ctx; ss|ss].
    }
    hexploit ISim_wf; eauto; intros Hwfs.
    intros fn; rewrite /ISim.sim_fun ?lookup_fmap /= ?lookup_union_with.
    destruct (_ ms !! fn) as [[[mskms itrms]|]|] eqn : Hms; cycle 1.
    { inv Hwfs; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns _ _ Hms).
      intros []; clarify.
    }
    { destruct (_ ctx !! fn) as [[[mskctx itrctx]|]|] eqn : Hctx; ss.
      { intros _ Hwf; destruct (_ mt !! fn) eqn : Hmt; ss.
        { exfalso; hexploit (Mod.wf_fns _ Hwf); rewrite map_Forall_lookup.
          intros Hf; hexploit (Hf fn None); [|intros []; clarify].
          rewrite /= lookup_union_with Hctx Hmt //=.
        }
        eexists; split; first done.
        eapply 
      }
      2:{ }
    }
    destruct (_ ctx !! fn) eqn : Hctx; ss.
    { hexploit (Hsimfun Hwft fn); rewrite /ISim.sim_fun ?lookup_fmap Hms /=.

      des_ifs; ss 2:{ }
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
      - etrans; [|eapply sub_perm_incl; et].
        etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. erewrite Heq. destruct fs, p. refl.
      - etrans; [|eapply Mod.well_scoped_fns].
        unfold fnsems_scopes. erewrite x0. destruct ft, p. refl.
      - exploit x1; cycle 2; i.
        + iApply (x2 with "[H]"); et.
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
  Qed. *)

  Theorem main_adequacy (ms mt : Mod.t) IC Ist :
    ISim.t open ms mt IC Ist →
    ctx_refines (ms, IC) (mt, emp%I).
  Proof using.
    intros Hsim [ctx ctxcond]; ss.
    eapply ISim_ctx with (ctx := ctx) in Hsim.
    eapply closed_adequacy with (P := ctxcond) in Hsim.
    intros Hwfm%Hsim; ss; split; [des; ss|]. intros ???%Hwfm; eauto.
    des; esplits; eauto; rewrite -bi.emp_sep_1 //.
  Qed.
End ADEQUACY.

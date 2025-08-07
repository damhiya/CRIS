Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod LMod FSpec.
Require Import MSim TacticsCommon.
Require Export MSimCommon.

Set Implicit Arguments.

Section SIM.
  Context `{Σ : GRA}.
  Variable contextual: contextuality.
  Variable fl_src fl_tgt : alist (option string) (Any.t → itree crisE Any.t).
  Variable Ist : ist_type Σ.

  Let _msim := _msim contextual fl_src fl_tgt Ist.
  Let rel := ∀ Rs Rt, (retr_type Σ Rs Rt) → bool → bool → nat → alist key Any.t * itree crisE Rs → alist key Any.t * itree crisE Rt → iProp Σ.

  Variant iunlift (r : rel) Rs Rt RR ps pt nths sti_src sti_tgt res : Prop :=
  | unlift_intro (WF : ✓ res) (REL : Own res ⊢ |==> r Rs Rt RR ps pt nths sti_src sti_tgt).

  Definition ibot : rel := λ _ _ _ _ _ _ _ _, False%I.

  Global Program Definition isim
      r g {Rs Rt} (RR : retr_type Σ Rs Rt) ps pt
      nths sti_src sti_tgt : iProp Σ :=
    UPred Σ (gpaco9 (_msim) (cpn9 _msim) (iunlift r) (iunlift g) _ _ RR ps pt nths sti_src sti_tgt) _.
  Next Obligation. guclo msim_extendC_spec. econs; et. Defined.

  (***** isim lemmas *****)
  Lemma iunlift_ibot : iunlift ibot <9= bot9.
  Proof using.
    rewrite /ibot; i; inv PR.
    assert (CON : Own x8 ⊢ False).
    { iIntros "H". iPoseProof (REL with "H") as "F". iMod "F". done. }
    eapply Own_pure_soundness in CON; eauto.
  Qed.

  Lemma isim_init r g r' g' ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt iP fmr
    (ENTAIL : iP ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)))
    (CUR : Own fmr ⊢ iP)
    (LER: iunlift r <9= r')
    (LEG: iunlift g <9= g')
    :
    gpaco9 _msim (cpn9 _msim) r' g' Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof using.
    guclo msim_wfC_spec; econs; ii; esplits; eauto.
    assert (SIM : Own fmr ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)).
    { etrans; eauto. }
    eapply gpaco9_mon; et.
    hexploit (Own_general_soundness fmr); eauto.
  Qed.

  Lemma isim_final r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt fmr
    (SIM : gpaco9 _msim (cpn9 _msim) (iunlift r) (iunlift g) Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    Own fmr ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)).
  Proof using.
    rr. econs. i. rr in H0. rewrite /isim. rr.
    rewrite seal_eq /own.Own_def /uPred_ownM seal_eq in H0. ss.
    guclo msim_extendC_spec. econs; et.
  Qed.

  Lemma iunlift_mon r0 r1
      (MON : ∀ Rs Rt RR ps pt nths sti_src sti_tgt,
        @r0 Rs Rt RR ps pt nths sti_src sti_tgt ⊢ |==> @r1 Rs Rt RR ps pt nths sti_src sti_tgt) :
    iunlift r0 <9= iunlift r1.
  Proof using.
    i. destruct PR. econs; eauto.
    iIntros "H". iPoseProof (REL with "H") as "H".
    iMod "H". iPoseProof (MON with "H") as "H". eauto.
  Qed.

  Lemma isim_mono_knowledge r0 g0 r1 g1 {Rs Rt} RR ps pt nths sti_src sti_tgt
      (MON0 : ∀ Rs Rt RR ps pt nths sti_src sti_tgt,
        @r0 Rs Rt RR ps pt nths sti_src sti_tgt ⊢ |==> @r1 Rs Rt RR ps pt nths sti_src sti_tgt)
      (MON1 : ∀ Rs Rt RR ps pt nths sti_src sti_tgt,
        @g0 Rs Rt RR ps pt nths sti_src sti_tgt ⊢ |==> @g1 Rs Rt RR ps pt nths sti_src sti_tgt) :
    @isim r0 g0 Rs Rt RR ps pt nths sti_src sti_tgt ⊢ @isim r1 g1 Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof using.
    split; intros x wfx SIM.
    eapply gpaco9_mon; first eapply SIM; eauto using iunlift_mon.
  Qed.

  Lemma isim_mono r g ps pt {Rs Rt} RR0 RR1 nths sti_src sti_tgt
      (MONO : ∀ nths st_src st_tgt ret_src ret_tgt,
        RR0 nths (st_src, ret_src) (st_tgt, ret_tgt) ⊢ RR1 nths (st_src, ret_src) (st_tgt, ret_tgt)) :
    @isim r g Rs Rt RR0 ps pt nths sti_src sti_tgt ⊢ @isim r g Rs Rt RR1 ps pt nths sti_src sti_tgt.
  Proof using.
    split; intros x wfx H0; destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i); rewrite <-(bind_ret_r i0).
    guclo msim_bindC_spec; econs; first apply H0.
    ii; gstep; econs; ii; esplits; eauto; econs; eauto.
    iIntros "H"; iMod (RET with "H") as "H"; iModIntro; iApply MONO; done.
  Qed.

  Lemma isim_nodup r g ps pt {Rs Rt} RR nths sti_src sti_tgt :
    (∀ (NODFS : List.NoDup (List.map fst fl_src))
       (NODFT : List.NoDup (List.map fst fl_tgt))
       (NODS : List.NoDup (List.map fst sti_src.1))
       (NODT : List.NoDup (List.map fst sti_tgt.1)),
     @isim r g Rs Rt RR ps pt nths sti_src sti_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof using.
    uPred.unseal. split. intros x wfx SIM. rr. rr in SIM.
    guclo msim_nodupC_spec. econs. eauto.
  Qed.
  
  Lemma isim_upd r g ps pt {Rs Rt} RR nths sti_src sti_tgt :
    ( |==> @isim r g Rs Rt RR ps pt nths sti_src sti_tgt) ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof using.
    uPred.unseal; split; intros x wfx SIM; destruct SIM as [x' SIM].
    guclo msim_updateC_spec; econs; intros ?; exists x'; split.
    { by apply (SIM ε); rewrite right_id; done. }
    { by apply Own_Upd; rewrite cmra_discrete_total_update => z; apply (SIM z). }
  Qed.

  Global Instance isim_elim_upd r g {Rs Rt} RR ps pt nths sti_src sti_tgt P p :
    ElimModal True p false ( |==> P)%I P
      (@isim r g Rs Rt RR ps pt nths sti_src sti_tgt) 
      (isim r g RR ps pt nths sti_src sti_tgt).
  Proof using.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_wand r g ps pt {Rs Rt} RR RR' nths sti_src sti_tgt :
    (∀ nths st_src ret_src st_tgt ret_tgt,
        ((RR' nths (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR nths (st_src, ret_src) (st_tgt, ret_tgt))))
    ∗ (@isim r g Rs Rt RR' ps pt nths sti_src sti_tgt)
    ⊢ isim r g RR ps pt nths sti_src sti_tgt.
  Proof using.
    uPred.unseal; split; intros x wfx H; destruct H as [x1 [x2 [-> [HRR SIM]]]].
    destruct sti_src as [st_src i_src]; destruct sti_tgt as [st_tgt i_tgt].
    rewrite <-(bind_ret_r i_src); rewrite <-(bind_ret_r i_tgt).
    guclo msim_frameC_spec; econs; cycle 1.
    { iIntros "H"; iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H2"; iFrame; last by iApply "H1". }
    guclo msim_bindC_spec; econs; eauto; first by exact SIM.
    intros; gstep; econs; ii; esplits; eauto.
    econs; eauto.
    { iIntros "H1"; iPoseProof (RET with "H1") as "> HRR"; iModIntro; iIntros "H1".
      iRevert "HRR"; iStopProof; uPred.unseal; split; intros x' wfx'.
      rewrite ?own.Own_eq /own.Own_def; uPred.unseal; intros [x'' ->].
      eapply uPred_mono; last by eapply cmra_included_l.
      eapply HRR.
    }
  Qed.

  Lemma isim_frame r g {Rs Rt} RR ps pt nths sti_src sti_tgt P :
    P ∗ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt
    ⊢ isim r g (fun nths str_src str_tgt => P ∗ RR nths str_src str_tgt) ps pt nths sti_src sti_tgt.
  Proof using. iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto. Qed.

  Lemma isim_bind r g ps pt {Rs Rt Qs Qt} RR QQ nths st_src st_tgt i_src i_tgt k_src k_tgt :
    @isim r g Qs Qt QQ ps pt nths (st_src, i_src) (st_tgt, i_tgt)
    ∗ (∀ nths0 st_src0 ret_src st_tgt0 ret_tgt (NTHS: nths <= nths0),
        QQ nths0 (st_src0, ret_src) (st_tgt0, ret_tgt)
        -∗ isim r g RR false false nths0 (st_src0, k_src ret_src) (st_tgt0, k_tgt ret_tgt))%I
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof using.
    rewrite {3}/isim; split; intros x wfx BINDSIM; r.
    uPred.unseal_once_in BINDSIM; destruct BINDSIM as [x1 [x2 [Heq [RET BINDSIM]]]].
    eapply Own_general_completeness in RET, BINDSIM.
    guclo msim_bindC_spec; econs; eauto; ii.
    { instantiate (1:=(λ n ss st, Own x2 ∗ QQ n ss st)%I).
      eapply isim_init; et.
      rewrite Heq; iIntros "[H1 H2]"; iApply isim_wand; iSplitL "H2".
      - iIntros (?????) "QQ"; iSplitL "H2"; iFrame. done.
      - iApply RET; done.
    }
    eapply isim_init; et.
    iIntros "FMR"; iMod (RET0 with "FMR") as "[H2 QQ]".
    iApply (BINDSIM with "H2"); iFrame. et.
  Qed.

  Lemma isim_eqit_src r g ps pt {Rs Rt} RR nths st_src st_tgt i_src0 i_src1 i_tgt
    (EQIT: eqit eq false true i_src0 i_src1)
    :
    @isim r g Rs Rt RR ps pt nths (st_src, i_src0) (st_tgt, i_tgt)
    ⊢ isim r g RR ps pt nths (st_src, i_src1) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx RRx.
    guclo msim_eqitC_src_spec; econs; esplits; i; eauto; econs; eauto.
  Qed.

  Lemma isim_eqit_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt0 i_tgt1
    (EQIT: eqit eq false true i_tgt0 i_tgt1)
    :
    @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt0)
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, i_tgt1).
  Proof using.
    split; intros x wfx RRx.
    guclo msim_eqitC_tgt_spec; econs; esplits; i; eauto; econs; eauto.
  Qed.

  (* Simulation rules *)
  Lemma isim_ret r g ps pt {Rs Rt} RR nths st_src st_tgt v_src v_tgt :
    RR nths (st_src, v_src) (st_tgt, v_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, Ret v_src) (st_tgt, Ret v_tgt).
  Proof using.
    split; intros x wfx RRx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    split; intros x' wfx'; rewrite own.Own_eq /own.Own_def; uPred.unseal; intros xx'.
    exists x'; intros yf x'wf; split; eauto. eapply uPred_mono; eauto.
  Qed.

  Lemma isim_tau_src r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim r g Rs Rt RR true pt nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, tau;; i_src) (st_tgt, i_tgt).
  Proof using.
    by split; intros x wfx sim; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tau_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, tau;; i_tgt).
  Proof using. 
    by split; intros x wfx sim; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_io r g ps pt {Rs Rt} RR nths st_src st_tgt I O k_src k_tgt fn (varg : I) :
    (∀ (vret : O), @isim r g Rs Rt RR true true nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM.
    guclo msimC_spec. econs; esplits; eauto. econs; eauto. intros vret.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H"); eauto.
  Qed.

  Lemma isim_take_src X r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∀ x, @isim r g Rs Rt RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_take_tgt X r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∃ x, @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.
  
  Lemma isim_choose_src X r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∃ x, @isim r g Rs Rt RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.

  Lemma isim_choose_tgt X r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∀ x, @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt).
  Proof using. 
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_asm_src (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∀ (_ : P), @isim r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, assume P >>= k_src) (st_tgt, i_tgt).
  Proof using.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_src. rewrite bind_ret_l. eauto.
  Qed.
  
  Lemma isim_asm_tgt (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    P →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt ())
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, assume P >>= k_tgt).
  Proof using.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_tgt. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.
  
  Lemma isim_guar_src (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    ⌜P⌝ ∗ @isim r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, guarantee P >>= k_src) (st_tgt, i_tgt).
  Proof using.
    iIntros "[% H]". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_src. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_tgt (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∀ (_:P), @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt ()))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, guarantee P >>= k_tgt).
  Proof using. 
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_tgt. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_sput_src r g ps pt {Rs Rt} RR k v nths st_src st_tgt k_src i_tgt :
    @isim r g Rs Rt RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_src_sandbox r g ps pt {Rs Rt} RR k v nths st_src st_tgt k_src i_tgt img msk scp :
    In k.1 scp →
    @isim r g Rs Rt RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (SPut k v)) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.put.
    des_ifs; ss.
    - iApply isim_sput_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sput_tgt r g ps pt {Rs Rt} RR k v nths st_src st_tgt i_src k_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_tgt_sandbox r g ps pt {Rs Rt} RR k v nths st_src st_tgt i_src k_tgt img msk scp :
    In k.1 scp →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, SB.sandbox img msk scp (trigger (SPut k v)) >>= k_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.put.
    des_ifs; ss.
    - iApply isim_sput_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_src r g ps pt {Rs Rt} RR k nths st_src st_tgt k_src i_tgt :
    @isim r g Rs Rt RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_src_sandbox r g ps pt {Rs Rt} RR k nths st_src st_tgt k_src i_tgt img msk scp :
    In k.1 scp →
    @isim r g Rs Rt RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (SGet k)) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.get.
    des_ifs; ss.
    - iApply isim_sget_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_tgt r g ps pt {Rs Rt} RR k nths st_src st_tgt i_src k_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_tgt_sandbox r g ps pt {Rs Rt} RR k nths st_src st_tgt i_src k_tgt img msk scp :
    In k.1 scp →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, SB.sandbox img msk scp (trigger (SGet k)) >>= k_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.get.
    des_ifs; ss.
    - iApply isim_sget_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_assume_src r g ps pt {Rs Rt} RR iP nths st_src st_tgt k_src i_tgt :
    (iP -∗ (@isim r g Rs Rt RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init; et.
    iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done.
  Qed.

  Lemma isim_assume_res_src r g ps pt {Rs Rt} RR a nths st_src st_tgt k_src i_tgt :
    (Own a -∗ @isim r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (AssumeRes a) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx Hx. eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto.
    econs; eauto.
    intros x' Hx'.
    eapply isim_init; et.
    iIntros "X". iMod (Hx' with "X") as "[P X]". iPoseProof (Hx with "X P") as "SIM".
    iApply "SIM"; eauto.
  Qed.
  
  Lemma isim_assume_tgt r g ps pt {Rs Rt} RR iP nths st_src st_tgt i_src k_tgt :
    (iP ∗ (@isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto.
      iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_assume_res_tgt r g ps pt {Rs Rt} RR a nths st_src st_tgt i_src k_tgt :
    ((Own a ∗ @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt ()))%I) ⊢
    @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (AssumeRes a) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto. econs; eauto.
    { iIntros "A"; iPoseProof (Hx with "A") as "$"; ss. }
    intros ???. eapply isim_init; eauto. rewrite NEW. iIntros ">H". et.
  Qed.

  (* Lemma isim_assume_res_both r g ps pt {Rs Rt} RR iP nths st_src st_tgt k_src k_tgt :
    @isim r g Rs Rt RR true true nths (st_src, k_src ()) (st_tgt, k_tgt ())
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (AssumeRes iP) >>= k_src) (st_tgt, trigger (AssumeRes iP) >>= k_tgt).
  Proof using.
    split; intros a wfa Ha.
    eapply Own_general_completeness in Ha.
    guclo msimC_spec. econs; esplits; et.
    eapply msim_assume_res_both; et.
    eapply isim_init; et.
  Qed. *)

  Lemma isim_guarantee_src r g ps pt {Rs Rt} RR iP nths st_src st_tgt k_src i_tgt :
    (iP ∗ (@isim r g Rs Rt RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto.
      iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_guarantee_tgt r g ps pt {Rs Rt} RR iP nths st_src st_tgt i_src k_tgt :
    (iP -∗ (@isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init; et.
    iIntros "X"; iMod (Hx' with "X") as "[P X]".
    iPoseProof (Hx with "X P") as "I". et.
  Qed.

  Lemma isim_triggerUB_src r g {Rs Rt} RR ps pt X nths st_src st_tgt (k_src : X -> _) i_tgt :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, triggerUB >>= k_src) (st_tgt, i_tgt).
  Proof using. 
    unfold triggerUB. ired. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger r g {Rs Rt} RR ps pt nths st_src st_tgt i_tgt :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, triggerUB) (st_tgt, i_tgt).
  Proof using.
    rewrite (@idK_spec _ _ (triggerUB)). iApply isim_triggerUB_src.
  Qed.

  Lemma isim_triggerNB_tgt r g {Rs Rt} RR ps pt X nths st_src st_tgt i_src (k_tgt : X -> _) :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, triggerNB >>= k_tgt).
  Proof using.
    unfold triggerNB. ired. iApply isim_choose_tgt. iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger r g {Rs Rt} RR ps pt nths st_src st_tgt i_src :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, triggerNB).
  Proof using.
    rewrite (@idK_spec _ _ (triggerNB)). iApply isim_triggerNB_tgt.
  Qed.

  Lemma isim_unwrapU_src r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    iIntros "H". unfold unwrapU. destruct x.
    { norm_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. }
  Qed.

  Lemma isim_unwrapN_src r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g Rs Rt RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ isim r g RR ps pt nths (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt).
  Proof using.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. norm_l. iApply "H". Qed.

  Lemma isim_unwrapU_tgt r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt).
  Proof using.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. norm_r. iApply "H".
  Qed.

  Lemma isim_unwrapN_tgt r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt).
  Proof using.
    iIntros "H". unfold unwrapN. destruct x.
    { norm_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. }
  Qed.

  Lemma isim_call r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn varg :
    Ist nths st_src st_tgt
    ∗ (∀ nths0 st_src0 st_tgt0 vret
          (NODS : List.NoDup (List.map fst st_src0))
          (NODT : List.NoDup (List.map fst st_tgt0))
          (NTHS: nths <= nths0),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g Rs Rt RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo msimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo msim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! nths0 st_src0 st_tgt0 vret NODS NODT).
    iApply "B"; eauto.
  Qed.

  Lemma isim_call_sandbox r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn varg (msk_src msk_tgt:_→bool) scp_src scp_tgt img_src img_tgt:
    (msk_src fn → msk_tgt fn) →
    Ist nths st_src st_tgt
    ∗ (∀ nths0 st_src0 st_tgt0 vret
          (NODS : List.NoDup (List.map fst st_src0))
          (NODT : List.NoDup (List.map fst st_tgt0))
          (NTHS: nths <= nths0),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g Rs Rt RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, SB.sandbox img_src msk_src scp_src (trigger (Call fn varg)) >>= k_src) (st_tgt, SB.sandbox img_tgt msk_tgt scp_tgt (trigger (Call fn varg)) >>= k_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite !SBRed.call.
    des_if; cycle 1.
    { iApply isim_triggerUB_src. }
    des_ifs; ss; cycle 1.
    { specialize (H eq_refl). inv H. }
    iApply isim_call. iFrame.
  Qed.

  Lemma isim_inline_src r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt f fn varg
      (FIND : alist_find (Some fn) fl_src = Some f) :
    @isim r g Rs Rt RR true pt nths (st_src, f varg >>= (λ ret, tau;; Ret ret) >>= k_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_inline_src_sandbox r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt f fn varg (msk:_→bool) scp img
    (FIND : alist_find (Some fn) fl_src = Some f) :
    @isim r g Rs Rt RR true pt nths (st_src, f varg >>= (λ ret, tau;; Ret ret) >>= k_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (Call fn varg)) >>= k_src) (st_tgt, i_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.call.
    des_ifs.
    - iApply isim_inline_src; eauto.
    - iApply isim_triggerUB_src.
  Qed.

  Lemma isim_inline_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt f fn varg
      (FIND : alist_find (Some fn) fl_tgt = Some f) :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, f varg >>= (λ ret, tau;; Ret ret) >>= k_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof using. 
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_inline_tgt_sandbox r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt f fn varg (msk:_→bool) scp img
    (FIND : alist_find (Some fn) fl_tgt = Some f) :
    (msk fn) →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, f varg >>= (λ ret, tau;; Ret ret) >>= k_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, SB.sandbox img msk scp (trigger (Call fn varg)) >>= k_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite SBRed.call.
    des_ifs; ss.
    iApply isim_inline_tgt; eauto.
  Qed.
  
  Lemma isim_spawn r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn arg :
    @isim r g Rs Rt RR true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths)
    ⊢ isim r g RR ps pt nths (st_src, trigger (Spawn fn arg) >>= k_src) (st_tgt, trigger (Spawn fn arg) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_spawn_sandbox r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn arg (msk_src msk_tgt:_→bool) scp_src scp_tgt img_src img_tgt:
    (msk_src fn → msk_tgt fn) →
    @isim r g Rs Rt RR true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths)
    ⊢ isim r g RR ps pt nths (st_src, SB.sandbox img_src msk_src scp_src (trigger (Spawn fn arg)) >>= k_src) (st_tgt, SB.sandbox img_tgt msk_tgt scp_tgt (trigger (Spawn fn arg)) >>= k_tgt).
  Proof using.
    i. iIntros "ISIM".
    rewrite !SBRed.spawn.
    des_if; cycle 1.
    { iApply isim_triggerUB_src. }
    des_ifs; ss; cycle 1.
    { specialize (H eq_refl). inv H. }
    iApply isim_spawn. iFrame.
  Qed.
  
  Lemma isim_yield r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt tid :
    Ist nths st_src st_tgt
    ∗ (∀ nths0 st_src0 st_tgt0
          (NODS : List.NoDup (List.map fst st_src0))
          (NODT : List.NoDup (List.map fst st_tgt0))
          (NTHS: nths <= nths0),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g Rs Rt RR true true nths0 (st_src0, k_src ()) (st_tgt0, k_tgt ()))
    ⊢ (isim r g RR ps pt nths (st_src, trigger (Yield tid) >>= k_src) (st_tgt, trigger (Yield tid) >>= k_tgt)).
  Proof using.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo msimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo msim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! nths0 st_src0 st_tgt0 NODS NODT).
    iApply "B"; eauto.
  Qed.

  Lemma isim_call_none
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg
    (CLOSED: contextual = closed)
    (FIND: alist_find (Some fn) fl_src = None)
  :
  ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec. econs; esplits; eauto.
    eapply msim_call_none; et.
  Qed.

  Lemma isim_call_none_sandbox
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg img msk scp
    (CLOSED: contextual = closed)
    (FIND: alist_find (Some fn) fl_src = None)
    :
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (Call fn varg)) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    i. rewrite SBRed.call.
    des_ifs; ss.
    - iApply isim_call_none; eauto.
    - unfold triggerUB. grind. iApply isim_take_src. iIntros (?). ss.
  Qed.
  
  Lemma isim_spawn_none
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg
    (CLOSED: contextual = closed)
    (FIND: alist_find (Some fn) fl_src = None)
  :
  ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, trigger (Spawn fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec. econs; esplits; eauto.
    eapply msim_spawn_none; et.
  Qed.

  Lemma isim_spawn_none_sandbox
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg img msk scp
    (CLOSED: contextual = closed)
    (FIND: alist_find (Some fn) fl_src = None)
    :
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (Spawn fn varg)) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    i. rewrite SBRed.spawn.
    des_ifs; ss.
    - iApply isim_spawn_none; eauto.
    - unfold triggerUB. grind. iApply isim_take_src. iIntros (?). ss.
  Qed.
  
  Lemma isim_call_mask_sandbox
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg img msk scp
    (FIND: msk fn = false)
  :
  ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (Call fn varg)) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    rewrite SBRed.call FIND. iApply isim_triggerUB_src.
  Qed.

  Lemma isim_spawn_mask_sandbox
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg img msk scp
    (FIND: msk fn = false)
    :
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, SB.sandbox img msk scp (trigger (Spawn fn varg)) >>= k_src) (st_tgt, i_tgt)).
  Proof using.
    rewrite SBRed.spawn FIND. iApply isim_triggerUB_src.
  Qed.
  
  Lemma isim_progress r g {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim g g Rs Rt RR false false nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR true true nths (st_src, i_src) (st_tgt, i_tgt).
  Proof using.
    split; intros x wfx SIM; eapply msim_progress_flag; eauto.
  Qed.

  Lemma isim_base r g Rs Rt RR ps pt nths sti_src sti_tgt :
    r Rs Rt RR ps pt nths sti_src sti_tgt
    ⊢ isim r g RR ps pt nths sti_src sti_tgt.
  Proof using.
    split; intros x wfx Hr.
    gfinal; left; econs; eauto.
    eapply Own_general_completeness in Hr; iIntros "X"; iModIntro; iApply Hr; done.
  Qed.

  Lemma isim_flag_mon r g {Rs Rt} RR nths st_src st_tgt i_src i_tgt (ps pt ps' pt' : bool)
      (PSLE : ps' → ps) (PTLE : pt' → pt) :
    @isim r g Rs Rt RR ps' pt' nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt).
  Proof using. split; intros x wfx SIM. guclo msim_flagC_spec. econs; eauto. eapply SIM. Qed.

  Lemma isim_reset r g {Rs Rt} RR ps pt nths sti_src sti_tgt :
    @isim r g Rs Rt RR false false nths sti_src sti_tgt
    ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof using.
    split; intros x wfx SIM. eapply msim_flag_down. eauto. 
  Qed.
  
  Lemma isim_coind (r g : rel) A P RsA RtA RRA psA ptA nthsA srcA tgtA
      (COIND : ∀ (g0 : rel) (a : A),
        (∀ Rs Rt RR ps pt nths0 src tgt, g Rs Rt RR ps pt nths0 src tgt -∗ g0 Rs Rt RR ps pt nths0 src tgt)
        → (P a ∗ (□ ∀ a, P a -∗ g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))
          ⊢ @isim r g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))) :
    ∀ (a : A), P a ⊢ @isim r g (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
  Proof using.
    i. iIntros "H". iPoseProof (bupd_intro with "H") as "H". iStopProof.
    split; intros x wfx Px.
    revert_until COIND. gcofix CIH. i. rename r0 into g0.
    pose (g' :=
      (λ Rs Rt RR ps pt nths src tgt,
        g Rs Rt RR ps pt nths src tgt
        ∨ ∃ a, P a
          ∗ ⌜@existT (Type*Type)%type (fun '(_,_) => _) (Rs, Rt) (RR,ps,pt,nths,src,tgt)
            = existT (RsA a, RtA a) (RRA a,psA a,ptA a,nthsA a,srcA a,tgtA a)⌝)%I).
    specialize (COIND g' a).
    uPred.unseal_once_in Px; destruct Px as [x' Px].
    guclo msim_updateC_spec; econs; ii; exists x'; split; cycle 1.
    { apply Own_Upd; rewrite cmra_discrete_total_update; intros yf; eapply Px; eauto. }
    eapply gpaco9_mon.
    { eapply COIND; eauto.
      { iIntros (????????) "X". rewrite /g'; iLeft; eauto. }
      { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
      { eapply Own_general_soundness.
        { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
        iIntros "X"; iSplitL "X".
        { specialize (Px ε); rewrite ?right_id in Px; hexploit (Px); eauto; i; des;
            iPoseProof (Own_general_completeness with "X") as "X"; eauto.
        }
        iModIntro. iIntros (?) "P"; rewrite /g'; iRight; iExists a0; iSplitL "P"; iFrame.
        iPureIntro; eauto.
      }
    }
    { ii; eauto. }
    { rewrite /g'; ii; inv PR.
      uPred.unseal_once_in REL; destruct REL as [REL]; hexploit REL; eauto.
      { rewrite own.Own_eq /own.Own_def; uPred.unseal; rr; exists ε; rewrite right_id; ss. }
      intros UPD; uPred.unseal_in UPD; destruct UPD as [x7']; dup H0.
      specialize (H0 ε); rewrite ?right_id in H0; hexploit H0; eauto; i; des.
      destruct H3.
      { apply CIH0; econs; eauto.
        iIntros "X"; iMod (Own_Upd with "X") as "X"; cycle 1.
        { eapply Own_general_completeness in H3; iModIntro; iApply H3; done. }
        { rewrite cmra_discrete_total_update; intros frame wf7; eapply (H1 frame); eauto. }
      }
      { destruct H3 as [a' [x7'' [x7''' H3]]]; des.
        rr in H5. depdes H5.
        eapply CIH; eauto.
        uPred.unseal; exists x7'; split.
        { eapply (H1 yf); eauto. }
        { eapply Own_general_soundness; eauto.
          rewrite H3; iIntros "[X _]"; eapply Own_general_completeness in H4; eauto.
          iApply H4; eauto.
        }
      }
    }
  Qed.

End SIM.

Global Opaque isim.

Section Proph.

  Context `{Σ: GRA}.

  Context (contextual: contextuality).
  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : ist_type Σ).

  Local Notation isim := (isim contextual fl_s fl_t Ist).

  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : alist key Any.t).

  (* Precise Pre & Post conditions *)
  Lemma isim_assume_proph_src_advanced {X} pre r g k_s i_t :
    (∃ (I P : iProp Σ) (Q : X → iProp Σ),
      I ∗ precise P ∗
      (∀ x, ∃ T, (I ∗ pre x -∗ □ T) ∗ (□ T -∗ pre x ==∗ P ∗ Q x)) ∗
      (P ∗ I ==∗
        isim r g RR true pt nths (st_s, k_s Q) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, (AssumeProph pre) >>= k_s) (st_t, i_t).
  Proof.
    rewrite /AssumeProph; unseal CRIS_PROPH.
    iIntros "[%I [%P [%Q [I [#[%pr [PRP PPR]] [G H]]]]]]".
    iRevert "G H PRP PPR".
    iStopProof; eapply entails_pointwise; iIntros (res Hres) "R I K #PRP #PPR".
    norm_l; iApply isim_choose_src; iExists (pr ⋅ res).
    norm_l; iApply isim_choose_src; iExists Q.
    norm_l; iApply isim_guarantee_src; iSplitL "R I".
    { iIntros (x) "Hpre". iPoseProof ("I" $! x) as "[%T [Ht1 Ht2]]".
      iPoseProof ("Ht1" with "[R Hpre]") as "#T"; [rewrite Hres; iFrame|].
      iMod ("Ht2" with "T Hpre") as "[P $]"; rewrite Own_op; iFrame "R".
      iApply "PPR"; done.
    }
    norm_l; iApply isim_assume_res_src; iIntros "[P I]"; rewrite Hres.
    iMod ("PRP" with "P") as "P".
    iMod ("K" with "[P I]") as "K"; first iFrame.
    norm_l; iApply "K".
  Qed.

  Lemma isim_assume_proph_src {X} pre r g k_s i_t :
    (∃ (P : iProp Σ) (Q : X → iProp Σ),
      precise P ∗
      (∀ x, pre x ==∗ P ∗ Q x) ∗
      (P ==∗ isim r g RR true pt nths (st_s, (k_s Q)) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, (AssumeProph pre) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%P [%Q [#Pre [Hsplit Hpost]]]]".
    iApply isim_assume_proph_src_advanced.
    iExists emp%I, P, Q; iSplit; first by done.
    iSplit; first by eauto.
    iSplitL "Hsplit".
    { iIntros (x); iExists emp%I; iSplitR; [iIntros "_"; done|].
      iIntros "_ Hpre"; iApply "Hsplit"; done.
    }
    by iIntros "[P _]"; iApply "Hpost".
  Qed.

  Lemma isim_assume_proph_src_simple {X} pre r g k_s i_t :
    (∃ (x : X), precise (pre x) ∗
      ∀ x', pre x' -∗ ⌜x' = x⌝ ∗ isim r g RR true pt nths (st_s, k_s (λ x', ⌜x' = x⌝)) (st_t, i_t)) ⊢
    isim r g RR ps pt nths (st_s, AssumeProph pre >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%x [#Hprecise K]]".
    iApply isim_assume_proph_src_advanced.
    set (K := (∀ x : X, _ -∗ _ ∗ _)%I).
    iExists K, (pre x).
    iFrame "K".
    iExists (λ x', ⌜x' = x⌝%I).
    iSplitL; [by eauto|].
    iSplitL.
    { iIntros (x'); iExists ⌜x' = x⌝%I; iSplitL.
      { subst K; iIntros "[H P]"; iPoseProof ("H" with "P") as "[$ _]". }
      { iIntros "->"; iIntros "$"; done. }
    }
    iIntros "[P K]"; iPoseProof ("K" with "P") as "[_ ?]". done.
  Qed.

  Lemma isim_assume_proph_both
      {X_s X_t} (pre_s : X_s → iProp Σ) (pre_t : X_t → iProp Σ) r g k_s k_t :
    (∀ pr_t Q_t, (∀ x, pre_t x ==∗ Own pr_t ∗ Q_t x) -∗
      ∃ (P : iProp Σ) (Q : X_s → iProp Σ),
        precise P ∗
        (∀ x, pre_s x ==∗ P ∗ Q x) ∗
        (P ==∗ (Own pr_t ∗ (isim r g RR true true nths (st_s, k_s Q) (st_t, k_t Q_t))))) ⊢
    isim r g RR ps pt nths (st_s, AssumeProph pre_s >>= k_s) (st_t, AssumeProph pre_t >>= k_t).
  Proof.
    iIntros "P".
    rewrite /AssumeProph; unseal CRIS_PROPH.
    norm_r; iApply isim_choose_tgt; iIntros (pr_t).
    norm_r; iApply isim_choose_tgt; iIntros (Q_t).
    norm_r; iApply isim_guarantee_tgt; iIntros "Q".
    iPoseProof ("P" with "Q") as "[%P [%Q_s [#[%pr_s [Hpre Hpre2]] [Hsplit HP]]]]".
    norm_l; iApply isim_choose_src; iExists pr_s.
    norm_l; iApply isim_choose_src; iExists Q_s.
    norm_l; iApply isim_guarantee_src; iSplitL "Hsplit".
    { iIntros (x) "PRE"; iMod ("Hsplit" with "PRE") as "[P $]"; iApply "Hpre2"; done. }
    norm_l; iApply isim_assume_res_src; iIntros "P"; iMod ("Hpre" with "P") as "P".
    iMod ("HP" with "P") as "[P K]". norm_r; iApply isim_assume_res_tgt; iFrame "P".
    norm_l; norm_r; done.
  Qed.

  Lemma isim_assume_proph_tgt {X} (pre : X → iProp Σ) r g k_t i_s :
    (∃ x, pre x ∗ (∀ Q, Q x ==∗ isim r g RR ps true nths (st_s, i_s) (st_t, k_t Q))) ⊢
    isim r g RR ps pt nths (st_s, i_s) (st_t, AssumeProph pre >>= k_t).
  Proof using.
    iIntros "[%x [Hpre Hpost]]".
    rewrite /AssumeProph; unseal CRIS_PROPH.
    norm_r; iApply isim_choose_tgt; iIntros (pr).
    norm_r; iApply isim_choose_tgt; iIntros (Q).
    norm_r; iApply isim_guarantee_tgt; iIntros "Hpost'".
    iPoseProof ("Hpost'" with "Hpre") as "> [P Q]".
    norm_r; iApply isim_assume_res_tgt; iFrame "P".
    norm_r. iPoseProof ("Hpost" with "Q") as "> SIM"; done.
  Qed.

  Lemma isim_guarantee_proph_src {X R} (post : X → R → iProp Σ) (Q : X → iProp Σ) r g k_s i_t :
    (∃ (ret : R), (∀ x, Q x ==∗ post x ret) ∗
      isim r g RR true pt nths (st_s, k_s ret) (st_t, i_t)) ⊢
    isim r g RR ps pt nths (st_s, (GuaranteeProph post Q) >>= k_s) (st_t, i_t).
  Proof using.
    rewrite /GuaranteeProph; unseal CRIS_PROPH.
    iIntros "[%ret [HQ H]]".
    norm_l. iApply isim_choose_src. iExists ret.
    norm_l. iApply isim_guarantee_src; iFrame "HQ".
    norm_l. done.
  Qed.

  Lemma isim_guarantee_proph_tgt {X R} (post : X → R → iProp Σ) (Q : X → iProp Σ) r g i_s k_t :
    (∀ (ret : R), (∀ x, Q x ==∗ post x ret) ==∗
      isim r g RR ps true nths (st_s, i_s) (st_t, k_t ret)) ⊢
    isim r g RR ps pt nths (st_s, i_s) (st_t, GuaranteeProph post Q >>= k_t).
  Proof using.
    rewrite /GuaranteeProph; unseal CRIS_PROPH.
    iIntros "H".
    norm_r. iApply isim_choose_tgt. iIntros (x).
    norm_r. iApply isim_guarantee_tgt; iIntros "P".
    norm_r. iPoseProof ("H" with "P") as "> H". done.
  Qed.

  Lemma isim_update_proph_src_advanced {X A R} pre (post : X → R → iProp Σ) (arg : A) r g k_s i_t :
    (∃ (I P Q : iProp Σ) (ret : R),
      I ∗ precise P ∗
      (∀ x, ∃ T, (I ∗ pre x arg -∗ □ T) ∗ (□ T -∗ pre x arg ==∗ P ∗ (Q ==∗ post x ret))) ∗
      (P ∗ I ==∗ Q ∗ isim r g RR true pt nths (st_s, k_s ret) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, UpdateProph pre post arg >>= k_s) (st_t, i_t).
  Proof.
    iIntros "[%I [%P [%Q [%ret [I [#[%pr Pre] [Hsplit Hsim]]]]]]]".
    iRevert "Hsplit Hsim Pre"; iStopProof.
    eapply entails_pointwise; iIntros (res Hres) "I Hsplit Hsim #[Hpre1 Hpre2]".
    rewrite /UpdateProph; unseal CRIS_PROPH.
    norm_l; iApply isim_choose_src; iExists (pr ⋅ res).
    norm_l; iApply isim_choose_src; iExists (Q).
    norm_l; iApply isim_choose_src; iExists ret.
    norm_l; iApply isim_guarantee_src; iSplitL "I Hsplit".
    { iIntros (x) "Pre"; iPoseProof ("Hsplit" $! x) as "[%T [HT Hsplit]]".
      iPoseProof ("HT" with "[I Pre]") as "#T".
      { rewrite Hres; iFrame. }
      iMod ("Hsplit" with "T Pre") as "[P $]".
      rewrite Own_op; iFrame "I". iApply "Hpre2"; done.
    }
    norm_l; iApply isim_assume_res_src; iIntros "[P R]"; rewrite Hres.
    iMod ("Hpre1" with "P") as "P"; iMod ("Hsim" with "[P R]") as "[Q SIM]"; iFrame.
    norm_l; iApply isim_guarantee_src; iFrame "Q"; norm_l; iApply "SIM".
  Qed.

  Lemma isim_update_proph_src {X A R} pre (post : X → R → iProp Σ) (arg : A) r g k_s i_t :
    (∃ (P Q : iProp Σ) (ret : R),
      precise P ∗
      (∀ x, pre x arg ==∗ P ∗ (Q ==∗ post x ret)) ∗
      (P ==∗ Q ∗ isim r g RR true pt nths (st_s, k_s ret) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, UpdateProph pre post arg >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%P [%Q [%ret [Hprecise [Hsplit Hsim]]]]]".
    iApply isim_update_proph_src_advanced.
    iExists True%I, P, Q, ret.
    iSplit; [done|iSplit; [done|]].
    iSplitL "Hsplit".
    { iIntros (?); iExists emp%I; iSplitR; [iIntros "_"; done|].
      by iIntros "_ Pre"; iApply "Hsplit".
    }
    by iIntros "[P _]"; iApply "Hsim".
  Qed.

  Lemma isim_update_proph_src_simple {X A R} pre (post : X → R → iProp Σ) (arg : A) r g k_s i_t :
    (∃ (x : X) (ret : R),
      precise (pre x arg) ∗
      ∀ x', pre x' arg ==∗
        ⌜x' = x⌝ ∗ post x ret ∗
        isim r g RR true pt nths (st_s, k_s ret) (st_t, i_t)) ⊢
    isim r g RR ps pt nths (st_s, UpdateProph pre post arg >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%x [%ret [Hprecise Hsim]]]".
    iApply isim_update_proph_src_advanced.
    iExists _, (pre x arg), (post x ret), ret.
    iSplitR "Hprecise"; [iExact "Hsim"|iSplit; [done|]].
    iSplitL.
    { iIntros (x'); iExists ⌜x = x'⌝%I; iSplitL.
      { iIntros "[Hsplit Hpre]"; iMod ("Hsplit" with "Hpre") as "[-> Post]"; done. }
      { iIntros "-> $ !> $ //". }
    }
    iIntros "[Hpre Hpost]"; iMod ("Hpost" with "Hpre") as "[% $]"; done.
  Qed.

  Lemma isim_update_proph_tgt {X A R} pre (post : X → R → iProp Σ) (arg : A) r g k_t i_s :
    (∃ x, pre x arg ∗
      ∀ ret, post x ret -∗ isim r g RR ps true nths (st_s, i_s) (st_t, k_t ret)) ⊢
    isim r g RR ps pt nths (st_s, i_s) (st_t, UpdateProph pre post arg >>= k_t).
  Proof using.
    iIntros "[%x [Hpre Hsim]]".
    rewrite /UpdateProph; unseal CRIS_PROPH.
    norm_r; iApply isim_choose_tgt; iIntros (pr).
    norm_r; iApply isim_choose_tgt; iIntros (Q).
    norm_r; iApply isim_choose_tgt; iIntros (ret).
    norm_r; iApply isim_guarantee_tgt; iIntros "P".
    iMod ("P" with "Hpre") as "[Hpr Hpost]".
    norm_r; iApply isim_assume_res_tgt; iFrame "Hpr".
    norm_r; iApply isim_guarantee_tgt; iIntros "Q"; iMod ("Hpost" with "Q").
    norm_r; iApply "Hsim"; done.
  Qed.

  Lemma isim_update_proph_both
      {X_s A_s R2_s X_t A_t R2_t}
      (pre_s : X_s → A_s → iProp Σ) (post_s : X_s → R2_s → iProp Σ) (arg_s : A_s)
      (pre_t : X_t → A_t → iProp Σ) (post_t : X_t → R2_t → iProp Σ) (arg_t : A_t)
      r g k_s k_t :
    (∀ ret_t P_t Q_t, precise P_t -∗
      (∀ x, pre_t x arg_t ==∗ P_t ∗ (Q_t ==∗ post_t x ret_t)) -∗
      ∃ (P_s Q_s : iProp Σ) ret_s,
        precise P_s ∗
        (∀ x, pre_s x arg_s ==∗ P_s ∗ (Q_s ==∗ post_s x ret_s)) ∗
        (P_s ==∗ P_t ∗
          (Q_t ==∗ Q_s ∗ isim r g RR true true nths (st_s, k_s ret_s) (st_t, k_t ret_t)))) ⊢
    isim r g RR ps pt nths
      (st_s, UpdateProph pre_s post_s arg_s >>= k_s)
      (st_t, UpdateProph pre_t post_t arg_t >>= k_t).
  Proof.
    iIntros "H".
    rewrite /UpdateProph; unseal CRIS_PROPH.
    norm_r; iApply isim_choose_tgt; iIntros (pr).
    norm_r; iApply isim_choose_tgt; iIntros (Q).
    norm_r; iApply isim_choose_tgt; iIntros (ret).
    norm_r; iApply isim_guarantee_tgt; iIntros "P".
    iPoseProof ("H" $! ret (Own pr) Q with "[] P") as "[% [% [% [[% #Hprecise] [Hsplit Hrest]]]]]".
    { iApply precise_Own. }
    do 3 (norm_l; iApply isim_choose_src; iExists _).
    norm_l; iApply isim_guarantee_src; iSplitL "Hsplit".
    { iIntros "% P"; iMod ("Hsplit" with "P") as "[P $]".
      iDestruct "Hprecise" as "[? H]"; iApply "H"; done.
    }
    norm_l; iApply isim_assume_res_src; iIntros "P".
    iDestruct "Hprecise" as "[H ?]"; iMod ("H" with "P") as "P".
    iMod ("Hrest" with "P") as "[P SIM]".
    norm_r; iApply isim_assume_res_tgt; iFrame "P".
    norm_r; iApply isim_guarantee_tgt; iIntros "Qt".
    iMod ("SIM" with "Qt") as "[Q SIM]".
    norm_l; iApply isim_guarantee_src; iFrame "Q".
    norm_l; norm_r; done.
  Qed.

(* 
  Lemma isim_guarantee_proph_src_advanced {X} Pre r g k_s i_t :
    (∃ (I P : iProp Σ) (Q : X → iProp Σ),
      I ∗ precise P ∗
      (∀ (x : X), ∃ (T : iProp Σ), (I ∗ Pre x -∗ □ T) ∗ (□ T -∗ Pre x ==∗ P ∗ Q x)) ∗
      (∀ a, □ (Own a ==∗ P ∗ I) -∗
        isim r g RR true pt nths (st_s, k_s (a, Q)) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, (GuaranteeProph Pre) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%I [%P [%Q [I [#[%pr [PRP PPR]] [G H]]]]]]".
    iRevert "G H PRP PPR". iStopProof.
    eapply entails_pointwise; iIntros (res Hres) "R I K #PRP #PPR".
    iApply isim_guarantee_proph_src.
    iExists (P ∗ Own res)%I, Q.
    iSplitR;
      [iApply precise_sep; iSplit; [iExists pr; iModIntro; iSplitL; done|iApply precise_Own]|].
    iSplitR "K".
    { iIntros (x) "P"; iDestruct ("I" $! x) as "[%T [HT HPQ]]".
      iPoseProof ("HT" with "[R P]") as "#T".
      { iSplitR "P"; [rewrite Hres|]; done. }
      iFrame "R"; iMod ("HPQ" with "T P") as "[$ $]"; done.
    }
    iIntros (?) "#[PRP2 PPR2]"; iApply "K"; iModIntro.
    iIntros "A"; iMod ("PPR2" with "A") as "[$ H]"; iApply Hres; done.
  Qed.

  Lemma isim_update_proph_src_advanced {X R} pre post (choice : R → bool) arg r g k_s i_t :
    (∃ (I P : iProp Σ) (Q : X → iProp Σ),
      I ∗ precise P ∗
      (∀ x, ∃ T, (I ∗ pre x arg -∗ □ T) ∗ (□ T -∗ pre x arg ==∗ P ∗ Q x)) ∗
      (P ∗ I ==∗ ∃ ret,
        (∀ x, Q x ==∗ if choice ret then post x ret↑ else pre x arg) ∗
        isim r g RR true pt nths
          (st_s, (if choice ret then Ret (inr ret↑) else Ret (inl ())) >>= k_s) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, (UpdateProph pre post choice arg) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%I [%P [%Q [I [#[%pr [Pre1 Pre2]] [Hsplit Hpost]]]]]]".
    rewrite /UpdateProph /GuaranteeProph; unseal CRIS_PROPH.
    iRevert "Pre1 Pre2 Hsplit Hpost"; iStopProof; eapply entails_pointwise; intros res Hres.
    iIntros "I #Pre1 #Pre2 Hsplit Hpost".
    norm_l; iApply isim_choose_src; iExists (res ⋅ pr).
    norm_l; iApply isim_choose_src; iExists Q.
    norm_l; iApply isim_guarantee_src; iSplitL "Hsplit I".
    { iIntros (x) "Hpre". iPoseProof ("Hsplit" $! x) as "[%T [Ht1 Ht2]]".
      iPoseProof ("Ht1" with "[I Hpre]") as "#T"; [rewrite Hres; iFrame|].
      iMod ("Ht2" with "T Hpre") as "[P $]"; rewrite Own_op; iFrame "I".
      iApply "Pre2"; done.
    }
    norm_l; iApply isim_assume_res_src; iIntros "[Hres Hp]".
    rewrite Hres. iMod ("Pre1" with "Hp") as "Hp".
    iMod ("Hpost" with "[Hp Hres]") as "[%ret [Hpost Hsim]]"; first iFrame.
    norm_l; iApply isim_choose_src; iExists ret.
    norm_l; iApply isim_guarantee_src; iFrame "Hpost".
    norm_l; done.
  Qed.

  Lemma isim_update_proph_src {X R} pre post (choice : R → bool) arg r g k_s i_t :
    (∃ (P : iProp Σ) (Q : X → iProp Σ),
      precise P ∗
      (∀ x, pre x arg ==∗ P ∗ Q x) ∗
      (P ==∗ ∃ ret,
        (∀ x, Q x ==∗ if choice ret then post x ret↑ else pre x arg) ∗
        isim r g RR true pt nths
          (st_s, (if choice ret then Ret (inr ret↑) else Ret (inl ())) >>= k_s) (st_t, i_t))) ⊢
    isim r g RR ps pt nths (st_s, (UpdateProph pre post choice arg) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%P [%Q [#Pre [Hsplit Hpost]]]]".
    iApply isim_update_proph_src_advanced.
    iExists emp%I, P, Q; iSplit; first by done.
    iSplit; first by eauto.
    iSplitL "Hsplit".
    { iIntros (x); iExists emp%I; iSplitR; [iIntros "_"; done|].
      iIntros "_ Hpre"; iApply "Hsplit"; done.
    }
    by iIntros "[P _]"; iApply "Hpost".
  Qed.

  Lemma isim_update_proph_src_simple {X R} pre post (choice : R → bool) arg r g k_s i_t :
    (∃ (x : X), precise (pre x arg) ∗
      ∀ x', pre x' arg -∗
        ⌜x' = x⌝ ∗
        ∃ ret, (if choice ret then post x ret↑ else pre x arg) ∗
          isim r g RR true pt nths
            (st_s, (if choice ret then Ret (inr ret↑) else Ret (inl ())) >>= k_s) (st_t, i_t)) ⊢
    isim r g RR ps pt nths (st_s, (UpdateProph pre post choice arg) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[%x [#Hprecise K]]".
    iApply isim_update_proph_src_advanced.
    set (K := (∀ x : X, _ -∗ _ ∗ _)%I).
    iExists K, (pre x arg), (λ x', ⌜x' = x⌝%I).
    iFrame "K".
    iSplitL; [by eauto|].
    iSplitL.
    { iIntros (x'); iExists ⌜x' = x⌝%I; iSplitL.
      { subst K; iIntros "[H P]"; iPoseProof ("H" with "P") as "[$ _]". }
      { iIntros "->"; iIntros "$"; done. }
    }
    iIntros "[P K]"; iPoseProof ("K" with "P") as "[_ [%ret [K Hsim]]]".
    iExists ret; iSplitL "K".
    { iIntros "!> % -> !> //". }
    done.
  Qed. *)

  (* Lemma isim_update_proph_tgt {X R} pre post (choice : R → bool) arg r g k_t i_s :
    (∃ (x : X), pre x arg ∗
      ∀ ret, (if choice ret then post x ret↑ else pre x arg) -∗
        isim r g RR ps true nths
          (st_s, i_s) (st_t, (if choice ret then Ret (inr ret↑) else Ret (inl ())) >>= k_t)) ⊢
    isim r g RR ps pt nths (st_s, i_s) (st_t, UpdateProph pre post choice arg >>= k_t).
  Proof using.
    iIntros "[%x [P Post]]".
    rewrite /UpdateProph; unseal CRIS_PROPH.
    rewrite bind_bind /GuaranteeProph; unseal CRIS_PROPH.
    norm_r; iApply isim_choose_tgt; iIntros (pr).
    norm_r; iApply isim_choose_tgt; iIntros (Q).
    norm_r; iApply isim_guarantee_tgt; iIntros "Q".
    iMod ("Q" with "P") as "[P Q]".
    norm_r; iApply isim_assume_res_tgt; iFrame "P".
    norm_r; iApply isim_choose_tgt; iIntros (ret).
    norm_r; iApply isim_guarantee_tgt; iIntros "Post'".
    iMod ("Post'" with "Q") as "Q"; norm_r; iApply "Post"; done.
  Qed. *)


  (* TODO : make isim_update_proph_src_advanced & isim_update_proph_src_simple *)
  (*  Lemma isim_guarantee_proph_src_advanced {X R} (Pre: X→_) Post r g k_s i_t
    :
    (∃ I P Q,
      I ∗ (precise P) ∗
      (∀ x, ∃ T, (I ∗ Pre x -∗ □ T) ∗ ((□ T) ∗ Pre x ==∗ P ∗
                 (∀ ret: R, Q ret ==∗ Post x ret))) ∗
      (I ∗ P -∗ isim r g RR true pt nths (st_s, k_s Q) (st_t, i_t)))
    ⊢
    isim r g RR ps pt nths (st_s, (AssumeProph Pre Post) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[% [% [% [I [PR [G H]]]]]]".
    iApply isim_guarantee_proph_src.
    iRevert "PR G H". iStopProof. eapply entails_pointwise. i.
    iIntros "I #PR G H".
    iExists (Own res ∗ P)%I, Q.
    iSplit. { iApply precise_sep. iSplit; [iApply precise_Own|]; et. }
    iSplitL "I G"; cycle 1.
    { iIntros "P". rewrite H. iApply "H"; et. }
    iIntros (?) "P".
    iSpecialize ("G" $! x). iDestruct "G" as "[% [G1 G2]]".
    iAssert (Own res ∗ Pre x -∗ □ T)%I with "[G1]" as "G1".
    { iIntros "[I P]". rewrite H. iApply ("G1" with "[I P]"). iFrame. }
    iCombine "I P" as "P". iPoseProof ("G1" with "P") as "#T".
    iDestruct "P" as "[I P]". iFrame.
    iApply ("G2" with "[T P]"). iFrame. et.
  Qed.

  Lemma isim_guarantee_proph_src_simple {X R} Pre (Post: _→R→_) r g k_s i_t
    :
    (∃ x: X, precise (Pre x) ∗
      ∀ x', Pre x' -∗
        ⌜x' = x⌝ ∗ isim r g RR true pt nths (st_s, k_s (Post x)) (st_t, i_t))
    ⊢
    isim r g RR ps pt nths (st_s, (AssumeProph Pre Post) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "[% [#PR H]]".
    iApply isim_guarantee_proph_src_advanced.
    iExists _, (Pre x), (Post x). iSplitL "H"; [iApply "H"|]. iSplit; et.
    iSplitL "".
    - iIntros (?). iExists (⌜x0 = x⌝)%I.
      iSplitL "".
      + iIntros "[H P]". iPoseProof ("H" with "P") as "[% _]". subst. et.
      + iIntros "[% P]". subst. iFrame. et.
    - iIntros "[H P]".  iSpecialize ("H" with "P"). iDestruct "H" as "[_ H]". et.
  Qed.

  Lemma isim_guarantee_proph_tgt {X R} Pre (Post: _→R→_) r g i_s k_t
    :
    (∃ x: X, Pre x
       ∗
       ∀ Q, (∀ ret, Q ret ==∗ Post x ret) -∗
       isim r g RR ps true nths (st_s, i_s) (st_t, k_t Q))
    ⊢
    isim r g RR ps pt nths (st_s, i_s) (st_t, (AssumeProph Pre Post) >>= k_t).
  Proof using.
    rewrite /AssumeProph. unseal CRIS_PROPH.
    iIntros "[% [P H]]".
    norm_r. iApply isim_choose_tgt. iIntros (?).
    norm_r. iApply isim_choose_tgt. iIntros (?).
    norm_r. iApply isim_guarantee_tgt. iIntros "GRT".
    iSpecialize ("H" $! x1). iMod ("GRT" with "P") as "[I Q]".
    norm_r. iApply isim_assume_res_tgt. iIntros "#PR". iFrame.
    ired. iApply "H". et.
  Qed. *)

End Proph.

Section FSEM.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

  Definition isim_fsem fl_src fl_tgt Ist contextual IstS IstE : relation (Any.t -> itree crisE Any.t) :=
  fun itr_src itr_tgt =>
  ∀ arg nths st_src st_tgt
    (IMON : Ist_monotone Ist)
    (NODS : List.NoDup (List.map fst st_src))
    (NODT : List.NoDup (List.map fst st_tgt)),
  IstS nths st_src st_tgt ⊢
    (winv (∅,∅) -∗ @isim Σ contextual fl_src fl_tgt Ist ibot ibot Any.t Any.t (ist_with_eq IstE)
      false false nths (st_src, itr_src arg) (st_tgt, itr_tgt arg)).

End FSEM.

Module ISim. Section ISim.
  Import Mod.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.  

  Variable contextual: contextuality.
  Variable (ms_src ms_tgt : Mod.t).
  Variable init_cond : iProp Σ.
  Variable Ist : ist_type Σ.

  Let scopes_src := ms_src.(scopes).
  Let scopes_tgt := ms_tgt.(scopes).
  Let fnsems_src := ms_src.(fnsems).
  Let fnsems_tgt := ms_tgt.(fnsems).
  Let init_src := ms_src.(initial_st).
  Let init_tgt := ms_tgt.(initial_st).
  Let fl_src := (List.map (map_snd SB.sandbox_body) fnsems_src).
  Let fl_tgt := (List.map (map_snd SB.sandbox_body) fnsems_tgt).

  Definition IstS (is_fun: bool) :=
    if is_fun
    then Ist
    else λ nths st_src st_tgt,
        (⌜nths = 1 ∧ st_src = init_src ∧ st_tgt = init_tgt⌝ ∗ init_cond)%I.

  Definition IstE (is_fun: bool) :=
    if is_fun
    then Ist
    else IstTrue.

  Definition sim_fun fno : Prop :=
    ∀ (WFS : Mod.wf ms_src)
      (WFT : Mod.wf ms_tgt)
      (NODUPFS : List.NoDup (List.map fst fnsems_src))
      (NODUPFT : List.NoDup (List.map fst fnsems_tgt))
      fs (FIND : alist_find fno fnsems_src = Some fs),
    ∃ ft, alist_find fno fnsems_tgt = Some ft /\
      isim_fsem fl_src fl_tgt Ist contextual (IstS (is_some fno)) (IstE (is_some fno))
        (SB.sandbox_body fs) (SB.sandbox_body ft).

  Definition initial_valid : Prop :=
    alist_find None fl_tgt = None
    →
    ((alist_find None fl_src = None) ∧
     (init_cond ⊢ Ist 1 init_src init_tgt)).

  Inductive t : Prop := mk {
    sim_mon : Mod.wf ms_tgt →
      Ist_monotone Ist;
    sim_scopes : Mod.wf ms_tgt →
      sub_perm scopes_src scopes_tgt;
    sim_match : Mod.wf ms_tgt →
      sub_perm (List.map fst fnsems_src) (List.map fst fnsems_tgt);
    sim_initial : Mod.wf ms_tgt →
      initial_valid;
    sim_fnsems : Mod.wf ms_tgt →
      ∀ fn, sim_fun fn;
  }.

  Lemma sim_fun_strong fno:
    (In fno (List.map fst fnsems_src) → sim_fun fno) → sim_fun fno.
  Proof using.
    ii. dup FIND. eapply alist_find_some, (in_map fst) in FIND0. eapply H; et.
  Qed.

End ISim. End ISim.

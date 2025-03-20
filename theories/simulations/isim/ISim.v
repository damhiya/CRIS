Require Import Common.
Require Import HMod.
Require Import HPSim.

Set Implicit Arguments.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).

Section SIM.
  Context `{Σ : GRA}.
  Variable contextual: contextuality.
  Variable fl_src fl_tgt : alist string (Any.t → itree hmodE Any.t).
  Variable Ist : nat → alist key Any.t → alist key Any.t → iProp Σ.

  Let _hpsim := _hpsim contextual fl_src fl_tgt Ist.
  Let rel := ∀ Rs Rt, (nat → alist key Any.t * Rs → alist key Any.t * Rt → iProp Σ) → bool → bool → nat → alist key Any.t * itree hmodE Rs → alist key Any.t * itree hmodE Rt → iProp Σ.

  Variant iunlift (r : rel) Rs Rt RR ps pt nths sti_src sti_tgt res : Prop :=
  | unlift_intro (WF : ✓ res) (REL : Own res ⊢ |==> r Rs Rt RR ps pt nths sti_src sti_tgt).

  Definition ibot : rel := λ _ _ _ _ _ _ _ _, False%I.

  Global Program Definition isim
      r g {Rs Rt} (RR : nat → alist key Any.t * Rs → alist key Any.t * Rt → iProp Σ) ps pt
      nths sti_src sti_tgt : iProp Σ :=
    UPred Σ (gpaco9 (_hpsim) (cpn9 _hpsim) (iunlift r) (iunlift g) _ _ RR ps pt nths sti_src sti_tgt) _.
  Next Obligation. guclo hpsim_extendC_spec. econs; et. Defined.

  (***** isim lemmas *****)
  Lemma iunlift_ibot : iunlift ibot <9= bot9.
  Proof.
    rewrite /ibot; i; inv PR.
    assert (CON : Own x8 ⊢ False).
    { iIntros "H". iPoseProof (REL with "H") as "F". iMod "F". done. }
    eapply Own_pure_soundness in CON; eauto.
  Qed.

  Lemma isim_init r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt iP fmr
      (ENTAIL : iP ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)))
      (CUR : Own fmr ⊢ iP) :
    gpaco9 _hpsim (cpn9 _hpsim) (iunlift r) (iunlift g) Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    guclo hpsim_wfC_spec; econs; ii; esplits; eauto.
    assert (SIM : Own fmr ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)).
    { etrans; eauto. }
    hexploit (Own_general_soundness fmr); eauto.
  Qed.

  Lemma iunlift_mon r0 r1
      (MON : ∀ Rs Rt RR ps pt nths sti_src sti_tgt,
        @r0 Rs Rt RR ps pt nths sti_src sti_tgt ⊢ |==> @r1 Rs Rt RR ps pt nths sti_src sti_tgt) :
    iunlift r0 <9= iunlift r1.
  Proof.
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
  Proof.
    split; intros x wfx SIM.
    eapply gpaco9_mon; first eapply SIM; eauto using iunlift_mon.
  Qed.

  Lemma isim_nodup r g ps pt {Rs Rt} RR nths sti_src sti_tgt :
    (∀ (NODFS : List.NoDup (List.map fst fl_src))
       (NODFT : List.NoDup (List.map fst fl_tgt))
       (NODS : List.NoDup (List.map fst sti_src.1))
       (NODD : List.NoDup (List.map fst sti_tgt.1)),
     @isim r g Rs Rt RR ps pt nths sti_src sti_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof.
    uPred.unseal. split. intros x wfx SIM. rr. rr in SIM.
    guclo hpsim_nodupC_spec. econs. eauto.
  Qed.
  
  Lemma isim_upd r g ps pt {Rs Rt} RR nths sti_src sti_tgt :
    ( |==> @isim r g Rs Rt RR ps pt nths sti_src sti_tgt) ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof.
    uPred.unseal; split; intros x wfx SIM; destruct SIM as [x' SIM].
    guclo hpsim_updateC_spec; econs; intros ?; exists x'; split.
    { by apply (SIM ε); rewrite right_id; done. }
    { by apply Own_Upd; rewrite cmra_discrete_total_update => z; apply (SIM z). }
  Qed.

  Global Instance isim_elim_upd r g {Rs Rt} RR ps pt nths sti_src sti_tgt P p :
    ElimModal True p false ( |==> P)%I P
      (@isim r g Rs Rt RR ps pt nths sti_src sti_tgt) 
      (isim r g RR ps pt nths sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_mono r g ps pt {Rs Rt} RR0 RR1 nths sti_src sti_tgt
      (MONO : ∀ nths st_src st_tgt ret_src ret_tgt,
        RR0 nths (st_src, ret_src) (st_tgt, ret_tgt) ⊢ RR1 nths (st_src, ret_src) (st_tgt, ret_tgt)) :
    @isim r g Rs Rt RR0 ps pt nths sti_src sti_tgt ⊢ @isim r g Rs Rt RR1 ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx H0; destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i); rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec; econs; first apply H0.
    ii; gstep; econs; ii; esplits; eauto; econs; eauto.
    iIntros "H"; iMod (RET with "H") as "H"; iModIntro; iApply MONO; done.
  Qed.

  Lemma isim_wand r g ps pt {Rs Rt} RR RR' nths sti_src sti_tgt :
    (∀ nths0 st_src ret_src st_tgt ret_tgt,
        ((RR' nths0 (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR nths0 (st_src, ret_src) (st_tgt, ret_tgt))))
    ∗ (@isim r g Rs Rt RR' ps pt nths sti_src sti_tgt)
    ⊢ isim r g RR ps pt nths sti_src sti_tgt.
  Proof.
    uPred.unseal; split; intros x wfx H; destruct H as [x1 [x2 [-> [HRR SIM]]]].
    destruct sti_src as [st_src i_src]; destruct sti_tgt as [st_tgt i_tgt].
    rewrite <-(bind_ret_r i_src); rewrite <-(bind_ret_r i_tgt).
    guclo hpsim_frameC_spec; econs; cycle 1.
    { iIntros "H"; iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H2"; iFrame; last by iApply "H1". }
    guclo hpsim_bindC_spec; econs; eauto; first by exact SIM.
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
    ⊢ isim r g (fun nths0 str_src str_tgt => P ∗ RR nths0 str_src str_tgt) ps pt nths sti_src sti_tgt.
  Proof. iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto. Qed.

  Lemma isim_bind r g ps pt {Rs Rt Qs Qt} RR QQ nths st_src st_tgt i_src i_tgt k_src k_tgt :
    @isim r g Qs Qt QQ ps pt nths (st_src, i_src) (st_tgt, i_tgt)
    ∗ (∀ nths0 st_src0 ret_src st_tgt0 ret_tgt,
        QQ nths0 (st_src0, ret_src) (st_tgt0, ret_tgt)
        -∗ isim r g RR false false nths0 (st_src0, k_src ret_src) (st_tgt0, k_tgt ret_tgt))%I
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    rewrite {3}/isim; split; intros x wfx BINDSIM; r.
    uPred.unseal_once_in BINDSIM; destruct BINDSIM as [x1 [x2 [Heq [RET BINDSIM]]]].
    eapply Own_general_completeness in RET, BINDSIM.
    guclo hpsim_bindC_spec; econs; eauto; ii.
    { instantiate (1:=(λ n ss st, Own x2 ∗ QQ n ss st)%I).
      eapply isim_init; last by iIntros "H"; iExact "H".
      { rewrite Heq; iIntros "[H1 H2]"; iApply isim_wand; iSplitL "H2".
        { iIntros (?????) "QQ"; iSplitL "H2"; iFrame. done. }
        { iApply RET; done. }
      }
    }
    eapply isim_init; last by iIntros "H"; iExact "H".
    iIntros "FMR"; iMod (RET0 with "FMR") as "[H2 QQ]".
    iApply (BINDSIM with "H2"); iFrame.
  Qed.

  Lemma isim_eqit_src r g ps pt {Rs Rt} RR nths st_src st_tgt i_src0 i_src1 i_tgt
    (EQIT: eqit eq false true i_src0 i_src1)
    :
    @isim r g Rs Rt RR ps pt nths (st_src, i_src0) (st_tgt, i_tgt)
    ⊢ isim r g RR ps pt nths (st_src, i_src1) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx RRx.
    guclo hpsim_eqitC_src_spec; econs; esplits; i; eauto; econs; eauto.
  Qed.

  Lemma isim_eqit_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt0 i_tgt1
    (EQIT: eqit eq false true i_tgt0 i_tgt1)
    :
    @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt0)
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, i_tgt1).
  Proof.
    split; intros x wfx RRx.
    guclo hpsim_eqitC_tgt_spec; econs; esplits; i; eauto; econs; eauto.
  Qed.


  (* Simulation rules *)
  Lemma isim_ret r g ps pt {Rs Rt} RR nths st_src st_tgt v_src v_tgt :
    RR nths (st_src, v_src) (st_tgt, v_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, Ret v_src) (st_tgt, Ret v_tgt).
  Proof.
    split; intros x wfx RRx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    split; intros x' wfx'; rewrite own.Own_eq /own.Own_def; uPred.unseal; intros xx'.
    exists x'; intros yf x'wf; split; eauto. eapply uPred_mono; eauto.
  Qed.

  Lemma isim_tau_src r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim r g Rs Rt RR true pt nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, tau;; i_src) (st_tgt, i_tgt).
  Proof.
    by split; intros x wfx sim; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tau_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, tau;; i_tgt).
  Proof. 
    by split; intros x wfx sim; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_call r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn varg :
    Ist nths st_src st_tgt
    ∗ (∀ nths0 st_src0 st_tgt0 vret
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0)),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g Rs Rt RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! nths0 st_src0 st_tgt0 vret NODS NODD).
    iApply "B". eauto.
  Qed.

  Lemma isim_io r g ps pt {Rs Rt} RR nths st_src st_tgt I O k_src k_tgt fn (varg : I) :
    (∀ (vret : O), @isim r g Rs Rt RR true true nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt).
  Proof.
    split; intros x wfx SIM.
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. intros vret.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H"); eauto.
  Qed.

  Lemma isim_inline_src r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt f fn varg
      (FIND : alist_find fn fl_src = Some f) :
    @isim r g Rs Rt RR true pt nths (st_src, f varg >>= (λ ret, tau;; tau;; Ret ret) >>= k_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_inline_src_simpl r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt f fn varg
      (FIND : alist_find fn fl_src = Some f) :
    @isim r g Rs Rt RR true pt nths (st_src, f varg >>= k_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt).
  Proof.
    iIntros. iApply isim_inline_src; eauto.
    iApply isim_eqit_src; [|eauto].
    ired. eapply eqit_bind; eauto using eqit_refl.
    ii. ired. eauto using eqit_Tau_r, eqit_refl.
  Qed.

  Lemma isim_inline_tgt r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt f fn varg
      (FIND : alist_find fn fl_tgt = Some f) :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, f varg >>= (λ ret, tau;; tau;; Ret ret) >>= k_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_inline_tgt_simpl r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt f fn varg
      (FIND : alist_find fn fl_tgt = Some f) :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, f varg >>= k_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof.
    iIntros. iApply isim_inline_tgt; eauto.
    iApply isim_eqit_tgt; [|eauto].
    ired. eapply eqit_bind; eauto using eqit_refl.
    ii. ired. eauto using eqit_Tau_r, eqit_refl.
  Qed.

  Lemma isim_take_src X r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∀ x, @isim r g Rs Rt RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_take_tgt X r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∃ x, @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt).
  Proof.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.
  
  Lemma isim_choose_src X r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∃ x, @isim r g Rs Rt RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.

  Lemma isim_choose_tgt X r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∀ x, @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_asm_src (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    (∀ (_ : P), @isim r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, assume P >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_src. rewrite bind_ret_l. eauto.
  Qed.
  
  Lemma isim_asm_tgt (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    P →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt ())
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, assume P >>= k_tgt).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_tgt. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.
  
  Lemma isim_guar_src (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt :
    P →
    @isim r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, guarantee P >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_src. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_tgt (P : Prop) r g ps pt {Rs Rt} RR nths st_src st_tgt i_src k_tgt :
    (∀ (_:P), @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt ()))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, guarantee P >>= k_tgt).
  Proof. 
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_tgt. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_sput_src r g ps pt {Rs Rt} RR k v nths st_src st_tgt k_src i_tgt :
    @isim r g Rs Rt RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_src_sandbox r g ps pt {Rs Rt} RR  k v nths st_src st_tgt k_src i_tgt scopes :
    In k.1 scopes →
    @isim r g Rs Rt RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, HMod.sandbox scopes (trigger (SPut k v)) >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite SBRed.put.
    des_ifs; ss.
    - iApply isim_sput_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sput_tgt r g ps pt {Rs Rt} RR k v nths st_src st_tgt i_src k_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_tgt_sandbox r g ps pt {Rs Rt} RR k v nths st_src st_tgt i_src k_tgt scopes :
    In k.1 scopes →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, HMod.sandbox scopes (trigger (SPut k v)) >>= k_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite SBRed.put.
    des_ifs; ss.
    - iApply isim_sput_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_src r g ps pt {Rs Rt} RR k nths st_src st_tgt k_src i_tgt :
    @isim r g Rs Rt RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_src_sandbox r g ps pt {Rs Rt} RR k nths st_src st_tgt k_src i_tgt scopes :
    In k.1 scopes →
    @isim r g Rs Rt RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, HMod.sandbox scopes (trigger (SGet k)) >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite SBRed.get.
    des_ifs; ss.
    - iApply isim_sget_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_tgt r g ps pt {Rs Rt} RR k nths st_src st_tgt i_src k_tgt :
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_tgt_sandbox r g ps pt {Rs Rt} RR k nths st_src st_tgt i_src k_tgt scopes :
    In k.1 scopes →
    @isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, HMod.sandbox scopes (trigger (SGet k)) >>= k_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite SBRed.get.
    des_ifs; ss.
    - iApply isim_sget_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_Assume_src r g ps pt {Rs Rt} RR iP nths st_src st_tgt k_src i_tgt :
    (iP -∗ (@isim r g Rs Rt RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init.
    { iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done. }
    { done. }
  Qed.

  Lemma isim_Assume_tgt r g ps pt {Rs Rt} RR iP nths st_src st_tgt i_src k_tgt :
    (iP ∗ (@isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt).
  Proof.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto. iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_Guarantee_src r g ps pt {Rs Rt} RR iP nths st_src st_tgt k_src i_tgt :
    (iP ∗ (@isim r g Rs Rt RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto. iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_Guarantee_tgt r g ps pt {Rs Rt} RR iP nths st_src st_tgt i_src k_tgt :
    (iP -∗ (@isim r g Rs Rt RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt).
  Proof.
    split; intros x wfx Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init.
    { iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done. }
    { done. }
  Qed.

  Lemma isim_spawn r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt fn arg :
    @isim r g Rs Rt RR true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths)
    ⊢ isim r g RR ps pt nths (st_src, trigger (Spawn fn arg) >>= k_src) (st_tgt, trigger (Spawn fn arg) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_yield r g ps pt {Rs Rt} RR nths st_src st_tgt k_src k_tgt tid :
    (Ist nths st_src st_tgt)
    ∗ (∀ nths0 st_src0 st_tgt0
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0)),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g Rs Rt RR true true nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    ⊢ (isim r g RR ps pt nths (st_src, trigger (Yield tid) >>= k_src) (st_tgt, trigger (Yield tid) >>= k_tgt)).
  Proof.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! nths0 st_src0 st_tgt0 NODS NODD).
    iApply "B". eauto.
  Qed.

  Lemma isim_call_none
    r g ps pt {Rs Rt} RR nths st_src st_tgt k_src i_tgt fn varg
    (CLOSED: contextual = closed)
    (FIND: alist_find fn fl_src = None)
  :
    (@isim r g Rs Rt RR true pt nths (st_src, x <- triggerUB;; tau;; tau;; k_src x) (st_tgt, i_tgt))
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec. econs; esplits; eauto. econs 22; eauto.
  Qed.

  Lemma isim_progress r g {Rs Rt} RR nths st_src st_tgt i_src i_tgt :
    @isim g g Rs Rt RR false false nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR true true nths (st_src, i_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; eapply hpsim_progress_flag; eauto.
  Qed.

  Lemma isim_triggerUB_src r g {Rs Rt} RR ps pt X nths st_src st_tgt (k_src : X -> _) i_tgt :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, triggerUB >>= k_src) (st_tgt, i_tgt).
  Proof. 
    unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger r g {Rs Rt} RR ps pt nths st_src st_tgt i_tgt :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, triggerUB) (st_tgt, i_tgt).
  Proof.
    rewrite (@idK_spec _ _ (triggerUB)). iApply isim_triggerUB_src.
  Qed.

  Lemma isim_triggerNB_tgt r g {Rs Rt} RR ps pt X nths st_src st_tgt i_src (k_tgt : X -> _) :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, triggerNB >>= k_tgt).
  Proof.
    unfold triggerNB. hred_r. iApply isim_choose_tgt. iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger r g {Rs Rt} RR ps pt nths st_src st_tgt i_src :
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, triggerNB).
  Proof.
    rewrite (@idK_spec _ _ (triggerNB)). iApply isim_triggerNB_tgt.
  Qed.

  Lemma isim_unwrapU_src r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ (@isim r g Rs Rt RR ps pt nths (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. }
  Qed.

  Lemma isim_unwrapN_src r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g Rs Rt RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ isim r g RR ps pt nths (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. hred_l. iApply "H". Qed.

  Lemma isim_unwrapU_tgt r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapN_tgt r g {Rs Rt} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. }
  Qed.

  Lemma isim_base r g Rs Rt RR ps pt nths sti_src sti_tgt :
    r Rs Rt RR ps pt nths sti_src sti_tgt
    ⊢ isim r g RR ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx Hr.
    gfinal; left; econs; eauto.
    eapply Own_general_completeness in Hr; iIntros "X"; iModIntro; iApply Hr; done.
  Qed.

  Lemma isim_flag_mon r g {Rs Rt} RR nths st_src st_tgt i_src i_tgt (ps pt ps' pt' : bool)
      (PSLE : ps' → ps) (PTLE : pt' → pt) :
    @isim r g Rs Rt RR ps' pt' nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g Rs Rt RR ps pt nths (st_src, i_src) (st_tgt, i_tgt).
  Proof. split; intros x wfx SIM. guclo hpsim_flagC_spec. econs; eauto. eapply SIM. Qed.

  Lemma isim_reset r g {Rs Rt} RR ps pt nths sti_src sti_tgt :
    @isim r g Rs Rt RR false false nths sti_src sti_tgt
    ⊢ @isim r g Rs Rt RR ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx SIM. eapply hpsim_flag_down. eauto. 
  Qed.
  
  Lemma isim_coind (r g : rel) A P RsA RtA RRA psA ptA nthsA srcA tgtA
      (COIND : ∀ (g0 : rel) (a : A),
        (∀ Rs Rt RR ps pt nths0 src tgt, g Rs Rt RR ps pt nths0 src tgt -∗ g0 Rs Rt RR ps pt nths0 src tgt)
        → (P a ∗ (□ ∀ a, P a -∗ g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))
          ⊢ @isim r g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))) :
    ∀ (a : A), P a ⊢ @isim r g (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
  Proof.
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
    guclo hpsim_updateC_spec; econs; ii; exists x'; split; cycle 1.
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

  Lemma combine_quant A B (P : ∀ (a: A) (b: B), Prop)
      (PR : ∀ (ab : A * B), P (fst ab) (snd ab)) :
    ∀ a b, P a b.
  Proof. i. eapply (PR (a,b)). Qed.

  Lemma combine_quant_dep A (B: A -> Type) (P: forall a (b: B a), Prop)
      (PR: ∀ (ab: sigT B), P (projT1 ab) (projT2 ab)):
    ∀ a b, P a b.
  Proof. i. eapply (PR (existT a b)). Qed.

End SIM.

Global Opaque isim.

Definition Ist_monotone `{Σ : GRA} (Ist: nat → alist key Any.t → alist key Any.t → iProp Σ) : Prop :=
  ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
  Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt.

Definition isim_fsem `{Σ : GRA} fl_src fl_tgt Ist contextual : relation (Any.t -> itree hmodE Any.t) :=
  (eq ==> (fun itr_src itr_tgt =>
  ∀ nths st_src st_tgt
    (IMON : Ist_monotone Ist)
    (NODS : List.NoDup (List.map fst st_src))
    (NODD : List.NoDup (List.map fst st_tgt)),
  Ist nths st_src st_tgt ⊢
    @isim Σ contextual fl_src fl_tgt Ist ibot ibot Any.t Any.t
      (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ Ist nths st_src st_tgt))%I
      false false nths (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

Module HSim. Section HSim.
    Import HMod.
    Context `{Σ : GRA}.

    Variable contextual: contextuality.
    Variable (ms_src ms_tgt : HMod.t).
    Variable init_cond : iProp Σ.
    Variable Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ.

    Let scopes_src := ms_src.(scopes).
    Let scopes_tgt := ms_tgt.(scopes).
    Let fnsems_src := ms_src.(fnsems).
    Let fnsems_tgt := ms_tgt.(fnsems).
    Let init_src := ms_src.(initial_st).
    Let init_tgt := ms_tgt.(initial_st).

    Definition sim_fun fn : Prop :=
      ∀ (WFS : HMod.wf ms_src)
        (WFT : HMod.wf ms_tgt)
        (NODUPFS : List.NoDup (List.map fst fnsems_src))
        (NODUPFT : List.NoDup (List.map fst fnsems_tgt))
        fs (FIND : alist_find fn fnsems_src = Some fs),
      ∃ ft, alist_find fn fnsems_tgt = Some ft /\
        isim_fsem
          (List.map (map_snd HMod.sandbox_body) fnsems_src)
          (List.map (map_snd HMod.sandbox_body) fnsems_tgt)
          Ist contextual
          (HMod.sandbox_body fs) (HMod.sandbox_body ft).

    Inductive t : Prop := mk {
      sim_initial :
        init_cond ⊢ Ist 1 init_src init_tgt;
      sim_mon :
        ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
          Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt;
      sim_scopes :
        sub_perm scopes_src scopes_tgt;
      sim_match :
        sub_perm (List.map fst fnsems_src) (List.map fst fnsems_tgt);
      sim_fnsems :
        ∀ fn (IN : In fn (List.map fst fnsems_src)),
          sim_fun fn;
    }.
End HSim. End HSim.

Require Import Coqlib sflib ITreelib.
Require Import Behavior.
Require Import Mod HMod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import Events STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import Red IRed.
Require Import SubPerm.

From stdpp Require Import coPset gmap.

Set Implicit Arguments.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).

Section SIM.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).
  Variable fl_src fl_tgt : alist gname (Any.t → itree hmodE Any.t).
  Variable Ist : nat → alist key Any.t → alist key Any.t → iProp.
  Variable my_tid : nat.

  Let _hpsim := _hpsim fl_src fl_tgt Ist my_tid.
  Let rel := ∀ R : Type, (nat → alist key Any.t * R → alist key Any.t * R → iProp) → bool → bool → nat → alist key Any.t * itree hmodE R → alist key Any.t * itree hmodE R → iProp.

  Variant iunlift (r : rel) R RR ps pt nths sti_src sti_tgt res : Prop :=
    | unlift_intro
        (WF : ✓ res)
        (REL : Own res ⊢ |==> r R RR ps pt nths sti_src sti_tgt).

  Definition ibot : rel := fun _ _ _ _ _ _ _ => False%I.

  Program Definition isim
          r g {R} (RR : nat → alist key Any.t * R → alist key Any.t * R → iProp) ps pt
          nths (sti_src sti_tgt : alist key Any.t * itree hmodE R) : iProp := 
    UPred Σ (gpaco8 (_hpsim) (cpn8 _hpsim) (iunlift r) (iunlift g) _ RR ps pt nths sti_src sti_tgt) _.
  Next Obligation. guclo hpsim_extendC_spec. econs; et. Defined.

  (***** isim lemmas *****)
  Lemma iunlift_ibot:
    iunlift ibot <8= bot8.
  Proof.
    rewrite /ibot; i; inv PR.
    assert (CON : Own x7 ⊢ False).
    { iIntros "H". iPoseProof (REL with "H") as "F". iMod "F". done. }
    eapply Own_pure_soundness in CON; eauto.
  Qed.

  Lemma isim_init
      r g ps pt {R} RR nths st_src st_tgt i_src i_tgt iP fmr
      (ENTAIL : iP ⊢ (@isim r g R RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)))
      (CUR : Own fmr ⊢ iP) :
    gpaco8 _hpsim (cpn8 _hpsim) (iunlift r) (iunlift g) R RR ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    guclo hpsim_wfC_spec; econs; ii; esplits; eauto.
    assert (SIM : Own fmr ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, i_tgt)).
    { etrans; eauto. }
    hexploit (Own_general_soundness fmr); eauto.
  Qed.

  Lemma iunlift_mon r0 r1
      (MON : ∀ R RR ps pt nths sti_src sti_tgt,
        @r0 R RR ps pt nths sti_src sti_tgt ⊢ |==> @r1 R RR ps pt nths sti_src sti_tgt) :
    iunlift r0 <8= iunlift r1.
  Proof.
    i. destruct PR. econs; eauto.
    iIntros "H". iPoseProof (REL with "H") as "H".
    iMod "H". iPoseProof (MON with "H") as "H". eauto.
  Qed.

  Lemma isim_mono_knowledge 
      r0 g0 r1 g1 {R} RR ps pt nths sti_src sti_tgt
      (MON0 : ∀ R RR ps pt nths sti_src sti_tgt,
        @r0 R RR ps pt nths sti_src sti_tgt ⊢ |==> @r1 R RR ps pt nths sti_src sti_tgt)
      (MON1 : ∀ R RR ps pt nths sti_src sti_tgt,
        @g0 R RR ps pt nths sti_src sti_tgt ⊢ |==> @g1 R RR ps pt nths sti_src sti_tgt) :
    @isim r0 g0 R RR ps pt nths sti_src sti_tgt ⊢ @isim r1 g1 R RR ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx SIM.
    eapply gpaco8_mon; first eapply SIM; eauto using iunlift_mon.
  Qed.

  Lemma isim_upd r g ps pt {R} RR nths sti_src sti_tgt :
    ( |==> @isim r g R RR ps pt nths sti_src sti_tgt) ⊢ @isim r g R RR ps pt nths sti_src sti_tgt.
  Proof.
    uPred.unseal; split; intros x wfx SIM; destruct SIM as [x' SIM].
    guclo hpsim_updateC_spec; econs; intros ?; exists x'; split.
    { by apply (SIM ε); rewrite right_id; done. }
    { by apply Own_Upd; rewrite cmra_discrete_total_update => z; apply (SIM z). }
  Qed.

  Global Instance isim_elim_upd r g {R} RR ps pt nths sti_src sti_tgt P p :
    ElimModal True p false ( |==> P)%I P
      (@isim r g R RR ps pt nths sti_src sti_tgt) 
      (isim r g RR ps pt nths sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  (* GIL : Deleted the following because it is subsumed by [isim_wand]. *)
  (* Restored to use in wsim_bind_top *)
  Lemma isim_mono r g ps pt {R} RR0 RR1 nths sti_src sti_tgt
      (MONO : ∀ nths st_src st_tgt ret_src ret_tgt,
        RR0 nths (st_src, ret_src) (st_tgt, ret_tgt) ⊢ RR1 nths (st_src, ret_src) (st_tgt, ret_tgt)) :
    @isim r g R RR0 ps pt nths sti_src sti_tgt ⊢ @isim r g R RR1 ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx H0; destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i); rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec; econs; first apply H0.
    ii; gstep; econs; ii; esplits; eauto; econs; eauto.
    iIntros "H"; iMod (RET with "H") as "H"; iModIntro; iApply MONO; done.
  Qed.

  (* Try RR` -∗|==> RR *)
  Lemma isim_wand r g ps pt {R} RR RR' nths sti_src sti_tgt :
    (∀ nths0 st_src ret_src st_tgt ret_tgt,
        ((RR' nths0 (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR nths0 (st_src, ret_src) (st_tgt, ret_tgt))))
    ∗ (@isim r g R RR' ps pt nths sti_src sti_tgt)
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
      rewrite ?Own_eq /IPM.Own_def; uPred.unseal; intros [x'' ->].
      eapply uPred_mono; last by eapply cmra_included_l.
      eapply HRR.
    }
  Qed.

  Lemma isim_frame r g {R} RR ps pt nths sti_src sti_tgt P :
    P ∗ @isim r g R RR ps pt nths sti_src sti_tgt
    ⊢ isim r g (fun nths0 str_src str_tgt => P ∗ RR nths0 str_src str_tgt) ps pt nths sti_src sti_tgt.
  Proof. iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto. Qed.

  Lemma isim_bind r g ps pt {R S} RR nths st_src st_tgt i_src i_tgt k_src k_tgt :
    @isim r g S
      (fun nths0 '(st_src, ret_src) '(st_tgt, ret_tgt) =>
          (@isim r g R RR false false nths0 (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt))%I)
      ps pt nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ (isim r g RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    rewrite /isim; split; intros x wfx BINDSIM; rr; rr in BINDSIM.
    guclo hpsim_bindC_spec; econs; eauto; ii.
    guclo hpsim_updateC_spec; econs; intros wf0.
    destruct RET as [RET]; specialize (RET fmr0 wf0); exploit RET.
    { rewrite Own_eq /IPM.Own_def; uPred.unseal; rr; exists ε; rewrite right_id; ss. }
    intros UPD. uPred.unseal_in UPD; rewrite /CRIS.base_logic.upred.uPred_bupd_def /uPred_holds in UPD.
    destruct UPD as [fmr1 UPD]; exists fmr1; split.
    { eapply (UPD ε); rewrite ?right_id; eauto. }
    { eapply Own_Upd; rewrite cmra_discrete_total_update; intros z wfz; eapply UPD; eauto. }
  Qed.

  (* Simulation rules *)
  Lemma isim_ret r g ps pt {R} RR nths st_src st_tgt v_src v_tgt :
    RR nths (st_src, v_src) (st_tgt, v_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, Ret v_src) (st_tgt, Ret v_tgt).
  Proof.
    split; intros x wfx RRx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    split; intros x' wfx'; rewrite IPM.Own_eq /IPM.Own_def; uPred.unseal; intros xx'.
    exists x'; intros yf x'wf; split; eauto. eapply uPred_mono; eauto.
  Qed.

  Lemma isim_tau_src r g ps pt {R} RR nths st_src st_tgt i_src i_tgt :
    @isim r g R RR true pt nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, tau;; i_src) (st_tgt, i_tgt).
  Proof.
    by split; intros x wfx sim; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tau_tgt r g ps pt {R} RR nths st_src st_tgt i_src i_tgt :
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, tau;; i_tgt).
  Proof. 
    by split; intros x wfx sim; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_call r g ps pt {R} RR nths st_src st_tgt k_src k_tgt fn varg :
    Ist nths st_src st_tgt
    ∗ (∀ nths0 st_src0 st_tgt0 vret
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0)),
        (Ist nths0 st_src0 st_tgt0) ==∗ @isim r g R RR true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite IPM.Own_eq /IPM.Own_def in H1.
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

  Lemma isim_io r g ps pt {R} RR nths st_src st_tgt I O k_src k_tgt fn (varg : I) :
    (∀ (vret : O), @isim r g R RR true true nths (st_src, k_src vret) (st_tgt, k_tgt vret))
    ⊢ isim r g RR ps pt nths (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt).
  Proof.
    split; intros x wfx SIM.
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. intros vret.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H"); eauto.
  Qed.

  Lemma isim_inline_src r g ps pt {R} RR nths st_src st_tgt k_src i_tgt f fn varg
      (FIND : alist_find fn fl_src = Some f) :
    @isim r g R RR true pt nths (st_src, x <- f varg;; tau;; tau;; k_src x) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_inline_tgt r g ps pt {R} RR nths st_src st_tgt i_src k_tgt f fn varg
      (FIND : alist_find fn fl_tgt = Some f) :
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, x <- f varg;; tau;; tau;; k_tgt x)
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.
  
  Lemma isim_take_src X r g ps pt {R} RR nths st_src st_tgt k_src i_tgt :
    (∀ x, @isim r g R RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_take_tgt X r g ps pt {R} RR nths st_src st_tgt i_src k_tgt :
    (∃ x, @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt).
  Proof.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.
  
  Lemma isim_choose_src X r g ps pt {R} RR nths st_src st_tgt k_src i_tgt :
    (∃ x, @isim r g R RR true pt nths (st_src, k_src x) (st_tgt, i_tgt))
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.

  Lemma isim_choose_tgt X r g ps pt {R} RR nths st_src st_tgt i_src k_tgt :
    (∀ x, @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt x))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_asm_src (P : Prop) r g ps pt {R} RR nths st_src st_tgt k_src i_tgt :
    (∀ (_ : P), @isim r g R RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt))
    ⊢ @isim r g R RR ps pt nths (st_src, assume P >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_src. rewrite bind_ret_l. eauto.
  Qed.
  
  Lemma isim_asm_tgt (P : Prop) r g ps pt {R} RR nths st_src st_tgt i_src k_tgt :
    P →
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt ())
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, assume P >>= k_tgt).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_tgt. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.
  
  Lemma isim_guar_src (P : Prop) r g ps pt {R} RR nths st_src st_tgt k_src i_tgt :
    P →
    @isim r g R RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, guarantee P >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_src. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_tgt (P : Prop) r g ps pt {R} RR nths st_src st_tgt i_src k_tgt :
    (∀ (_:P), @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt ()))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, guarantee P >>= k_tgt).
  Proof. 
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_tgt. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_sput_src r g ps pt {R} RR k v nths st_src st_tgt k_src i_tgt :
    @isim r g R RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_src_sandbox r g ps pt {R} RR  k v nths st_src st_tgt k_src i_tgt scopes :
    In k.1 scopes →
    @isim r g R RR true pt nths (alist_upd k v st_src, k_src tt) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, HModSem.sandbox scopes (trigger (SPut k v)) >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite HModSB.transl_put.
    des_ifs; ss.
    - iApply isim_sput_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sput_tgt r g ps pt {R} RR k v nths st_src st_tgt i_src k_tgt :
    @isim r g R RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sput_tgt_sandbox r g ps pt {R} RR k v nths st_src st_tgt i_src k_tgt scopes :
    In k.1 scopes →
    @isim r g R RR ps true nths (st_src, i_src) (alist_upd k v st_tgt, k_tgt tt)
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, HModSem.sandbox scopes (trigger (SPut k v)) >>= k_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite HModSB.transl_put.
    des_ifs; ss.
    - iApply isim_sput_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_src r g ps pt {R} RR k nths st_src st_tgt k_src i_tgt :
    @isim r g R RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_src_sandbox r g ps pt {R} RR k nths st_src st_tgt k_src i_tgt scopes :
    In k.1 scopes →
    @isim r g R RR true pt nths (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, HModSem.sandbox scopes (trigger (SGet k)) >>= k_src) (st_tgt, i_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite HModSB.transl_get.
    des_ifs; ss.
    - iApply isim_sget_src. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_sget_tgt r g ps pt {R} RR k nths st_src st_tgt i_src k_tgt :
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_sget_tgt_sandbox r g ps pt {R} RR k nths st_src st_tgt i_src k_tgt scopes :
    In k.1 scopes →
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, HModSem.sandbox scopes (trigger (SGet k)) >>= k_tgt).
  Proof.
    i. iIntros "ISIM".
    rewrite HModSB.transl_get.
    des_ifs; ss.
    - iApply isim_sget_tgt. iFrame.
    - exfalso. edestruct (existsb_exists (String.eqb k.1) scopes).
      hexploit H1.
      + esplits; try eassumption. apply String.eqb_refl.
      + i. rewrite Heq in H2. ss.
  Qed.
  
  Lemma isim_Assume_src r g ps pt {R} RR iP nths st_src st_tgt k_src i_tgt :
    (iP -∗ (@isim r g R RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init.
    { iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done. }
    { done. }
  Qed.

  Lemma isim_Assume_tgt r g ps pt {R} RR iP nths st_src st_tgt i_src k_tgt :
    (iP ∗ (@isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt).
  Proof.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto. iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_Guarantee_src r g ps pt {R} RR iP nths st_src st_tgt k_src i_tgt :
    (iP ∗ (@isim r g R RR true pt nths (st_src, k_src tt) (st_tgt, i_tgt)))
    ⊢ @isim r g R RR ps pt nths (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' Hx'; eapply isim_init; eauto. iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_Guarantee_tgt r g ps pt {R} RR iP nths st_src st_tgt i_src k_tgt :
    (iP -∗ (@isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt)))
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt).
  Proof.
    split; intros x wfx Hx.
    guclo hpsimC_spec; econs; esplits; i; eauto; econs; eauto; intros x' Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init.
    { iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done. }
    { done. }
  Qed.

  Lemma isim_spawn r g ps pt {R} RR nths st_src st_tgt k_src k_tgt fn arg :
    @isim r g R RR true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths)
    ⊢ isim r g RR ps pt nths (st_src, trigger (Spawn fn arg) >>= k_src) (st_tgt, trigger (Spawn fn arg) >>= k_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_yield r g ps pt {R} RR nths st_src st_tgt k_src k_tgt tid :
    (Ist nths st_src st_tgt)
    ∗ (∀ nths0 st_src0 st_tgt0
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0)),
        (Ist nths0 st_src0 st_tgt0) -∗ @isim r g R RR true true nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    ⊢ (isim r g RR ps pt nths (st_src, trigger (Yield tid) >>= k_src) (st_tgt, trigger (Yield tid) >>= k_tgt)).
  Proof.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite IPM.Own_eq /IPM.Own_def in H1.
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

  Lemma isim_tid_src r g ps pt {R} RR nths st_src st_tgt k_src i_tgt :
    @isim r g R RR true pt nths (st_src, k_src my_tid) (st_tgt, i_tgt)
    ⊢ @isim r g R RR ps pt nths (st_src, trigger Tid >>= k_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tid_tgt r g ps pt {R} RR nths st_src st_tgt i_src k_tgt :
    @isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt my_tid)
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger Tid >>= k_tgt).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tid_tgt
    r g ps pt {R} RR nths st_src st_tgt i_src k_tgt
  :
    bi_entails
      (@isim r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt my_tid))
      (@isim r g R RR ps pt nths (st_src, i_src) (st_tgt, trigger Tid >>= k_tgt)).
  Proof. 
    split; intros x wfx SIM; guclo hpsimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_progress r g {R} RR nths st_src st_tgt i_src i_tgt :
    @isim g g R RR false false nths (st_src, i_src) (st_tgt, i_tgt)
    ⊢ @isim r g R RR true true nths (st_src, i_src) (st_tgt, i_tgt).
  Proof.
    split; intros x wfx SIM; eapply hpsim_progress_flag; eauto.
  Qed.  

  Lemma isim_triggerUB_src r g {R} RR ps pt X nths st_src st_tgt (k_src : X -> _) i_tgt :
    ⊢ @isim r g R RR ps pt nths (st_src, triggerUB >>= k_src) (st_tgt, i_tgt).
  Proof. 
    unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger r g {R} RR ps pt nths st_src st_tgt i_tgt :
    ⊢ @isim r g R RR ps pt nths (st_src, triggerUB) (st_tgt, i_tgt).
  Proof.
    rewrite (@idK_spec _ _ (triggerUB)). iApply isim_triggerUB_src.
  Qed.

  Lemma isim_triggerNB_tgt r g {R} RR ps pt X nths st_src st_tgt i_src (k_tgt : X -> _) :
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, triggerNB >>= k_tgt).
  Proof.
    unfold triggerNB. hred_r. iApply isim_choose_tgt. iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger r g {R} RR ps pt nths st_src st_tgt i_src :
    ⊢ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, triggerNB).
  Proof.
    rewrite (@idK_spec _ _ (triggerNB)). iApply isim_triggerNB_tgt.
  Qed.

  Lemma isim_unwrapU_src r g {R} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ (@isim r g R RR ps pt nths (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. }
  Qed.

  Lemma isim_unwrapN_src r g {R} RR ps pt nths st_src st_tgt X (x : option X) k_src i_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g R RR ps pt nths (st_src, k_src x') (st_tgt, i_tgt))
    ⊢ isim r g RR ps pt nths (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. hred_l. iApply "H". Qed.

  Lemma isim_unwrapU_tgt r g {R} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapN_tgt r g {R} RR ps pt nths st_src st_tgt X (x : option X) i_src k_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ @isim r g R RR ps pt nths (st_src, i_src) (st_tgt, k_tgt x'))
    ⊢ isim r g RR ps pt nths (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. }
  Qed.

  Lemma isim_base r g R RR ps pt nths sti_src sti_tgt :
    r R RR ps pt nths sti_src sti_tgt
    ⊢ isim r g RR ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx Hr.
    gfinal; left; econs; eauto.
    eapply Own_general_completeness in Hr; iIntros "X"; iModIntro; iApply Hr; done.
  Qed.

  Lemma isim_reset r g {R} RR ps pt nths sti_src sti_tgt :
    @isim r g R RR false false nths sti_src sti_tgt
    ⊢ @isim r g R RR ps pt nths sti_src sti_tgt.
  Proof.
    split; intros x wfx SIM. eapply hpsim_flag_down. eauto. 
  Qed.
  
  Lemma isim_coind (r g : rel) A P RA RRA psA ptA nthsA srcA tgtA
      (COIND : ∀ (g0 : rel) (a : A),
        (∀ R RR ps pt nths0 src tgt, g R RR ps pt nths0 src tgt -∗ g0 R RR ps pt nths0 src tgt)
        → (P a ∗ (∀ a, P a -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))
          ⊢ @isim r g0 (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a))) :
    ∀ (a : A), P a ⊢ @isim r g (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
  Proof.
    i. iIntros "H". iPoseProof (bupd_intro with "H") as "H". iStopProof.
    split; intros x wfx Px.
    (* rr. autorewrite with iprop. *)
    revert_until COIND. gcofix CIH. i. rename r0 into g0.
    pose (g' :=
      (λ R RR ps pt nths src tgt,
        g R RR ps pt nths src tgt
        ∨ ∃ a, P a
          ∗ ⌜@existT Type (fun _ => _) R (RR,ps,pt,nths,src,tgt)
            = existT (RA a) (RRA a,psA a,ptA a,nthsA a,srcA a,tgtA a)⌝)%I).
    specialize (COIND g' a).
    uPred.unseal_once_in Px; destruct Px as [x' Px].
    guclo hpsim_updateC_spec; econs; ii; exists x'; split; cycle 1.
    { apply Own_Upd; rewrite cmra_discrete_total_update; intros yf; eapply Px; eauto. }
    eapply gpaco8_mon.
    { eapply COIND; eauto.
      { iIntros (???????) "X". rewrite /g'; iLeft; eauto. }
      { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
      { eapply Own_general_soundness.
        { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
        iIntros "X"; iSplitL "X".
        { specialize (Px ε); rewrite ?right_id in Px; hexploit (Px); eauto; i; des;
            iPoseProof (Own_general_completeness with "X") as "X"; eauto.
        }
        iIntros (?) "P"; rewrite /g'; iRight; iExists a0; iSplitL "P"; iFrame.
        iPureIntro; eauto.
      }
    }
    { ii; eauto. }
    { rewrite /g'; ii; inv PR.
      uPred.unseal_once_in REL; destruct REL as [REL]; hexploit REL; eauto.
      { rewrite IPM.Own_eq /IPM.Own_def; uPred.unseal; rr; exists ε; rewrite right_id; ss. }
      intros UPD; uPred.unseal_in UPD; destruct UPD as [x7']; dup H0.
      specialize (H0 ε); rewrite ?right_id in H0; hexploit H0; eauto; i; des.
      destruct H3.
      { apply CIH0; econs; eauto.
        iIntros "X"; iMod (Own_Upd with "X") as "X"; cycle 1.
        { eapply Own_general_completeness in H3; iModIntro; iApply H3; done. }
        { rewrite cmra_discrete_total_update; intros frame wf7; eapply (H1 frame); eauto. }
      }
      { destruct H3 as [a' [x7'' [x7''' H3]]]; des. inv H5.
        eapply inj_pair2 in H12, H13, H8; clarify; eapply CIH; eauto.
        uPred.unseal; exists x7'; split.
        { eapply (H1 yf); eauto. }
        { eapply Own_general_soundness; eauto.
          rewrite H3; iIntros "[X _]"; eapply Own_general_completeness in H4; eauto.
          iApply H4; eauto.
        }
      }
    }
  Qed.

  Lemma combine_quant A (B : A -> Type) (P : ∀ a (b : B a), Prop)
      (PR : ∀ (ab : sigT B), P (projT1 ab) (projT2 ab)) :
    ∀ a b, P a b.
  Proof. i. eapply (PR (existT a b)). Qed.

  Lemma combine_quant_dep A (B: A -> Type) (P: forall a (b: B a), Prop)
      (PR: forall (ab: sigT B), P (projT1 ab) (projT2 ab)):
    forall a b, P a b.
  Proof. i. eapply (PR (existT a b)). Qed.
End SIM.

Global Opaque isim.

Definition isim_fsem `{Σ : GRA.t} fl_src fl_tgt Ist : relation (Any.t -> itree hmodE Any.t) :=
  (eq ==> (fun itr_src itr_tgt =>
             forall my_tid nths st_src st_tgt
                    (IMON : forall nths nths' (LE : nths <= nths') st_src st_tgt,
                        Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt)
                    (NODS : List.NoDup (List.map fst st_src))
                    (NODD : List.NoDup (List.map fst st_tgt)),
               Ist nths st_src st_tgt ⊢
                 @isim Σ fl_src fl_tgt Ist my_tid is_closed ibot ibot Any.t
                 (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ Ist nths st_src st_tgt))%I
                 false false nths (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

Module HSSim.
  Section SIM.
    Import HModSem.
    Context `{Σ : GRA.t}.
    Notation iProp := (iProp Σ).
    Variable (ms_src ms_tgt : HModSem.t).
    Variable init_cond : iProp.
    Variable Ist : nat -> alist key Any.t -> alist key Any.t -> iProp.

    Let scopes_src := ms_src.(scopes).
    Let scopes_tgt := ms_tgt.(scopes).
    Let fnsems_src := ms_src.(fnsems).
    Let fnsems_tgt := ms_tgt.(fnsems).
    Let init_src := ms_src.(initial_st).
    Let init_tgt := ms_tgt.(initial_st).

    Definition sim_fun fn : Prop :=
      forall
        (WFS : HModSem.wf ms_src)
        (WFT : HModSem.wf ms_tgt)
        (NODUPFS : List.NoDup (List.map fst fnsems_src))
        (NODUPFT : List.NoDup (List.map fst fnsems_tgt))
        fs (FIND : alist_find fn fnsems_src = Some fs),
      exists ft, alist_find fn fnsems_tgt = Some ft /\
                   isim_fsem
                     (List.map (map_snd HModSem.sandbox_body) fnsems_src)
                     (List.map (map_snd HModSem.sandbox_body) fnsems_tgt)
                     Ist is_closed
                     (HModSem.sandbox_body fs) (HModSem.sandbox_body ft).

    Inductive t : Prop :=
      mk {
          sim_initial:
            init_cond ⊢ Ist 1 init_src init_tgt;
          sim_mon:
          forall nths nths' (LE : nths <= nths') st_src st_tgt,
            Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt;
          sim_scopes:
            sub_perm scopes_tgt scopes_src;
          sim_length:
            List.length fnsems_src = List.length fnsems_tgt;
          sim_match:
            forall fn (IN : In fn (List.map fst fnsems_src)),
              In fn (List.map fst fnsems_tgt);
          sim_fnsems:
          forall fn
                 (IN : In fn (List.map fst fnsems_src)),
              sim_fun fn;
        }.

  End SIM.
End HSSim.

Module HSim.
  Section SIM.
    Context `{Σ : GRA.t}.
    Notation iProp := (iProp Σ).
    Variable (md_src md_tgt : HMod.t).
    Variable init_cond : Sk.t -> iProp.
    Variable Ist : Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp.

    Inductive t : Prop :=
      mk {
          sim_modsem:
          forall sk (SKINCL : List.incl md_tgt.(HMod.sk) sk) (SKWF : Sk.wf sk),
            <<SIM : HSSim.t (md_src.(HMod.modsem) sk) (md_tgt.(HMod.modsem) sk) (init_cond sk) (Ist sk)>>;
          sim_sk : <<SIM : Sk.equiv md_src.(HMod.sk) md_tgt.(HMod.sk)>>;
        }.

    Definition sim_fun fn : Prop :=
      forall sk,
        HSSim.sim_fun is_closed (HMod.modsem md_src sk) (HMod.modsem md_tgt sk) (Ist sk) fn.

  End SIM.
End HSim.

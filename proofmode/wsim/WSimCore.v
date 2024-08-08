Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import Translate STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import Red IRed.

From stdpp Require Import coPset gmap.
Require Import ISimCore.


Set Implicit Arguments.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).


Section WSIM.
  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{CtxWD.t}.

  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Let isim := isim Ist fl_src fl_tgt.

  Variable u: world_id.
  Variable b: level.

  Definition wsim (E : coPset) 
    r g {R} (RR: Any.t * R -> Any.t * R -> iProp) ps pt src tgt
  :=
    (world u b E -∗ isim r g RR ps pt src tgt)%I.

  Definition wclosed u b (P: iProp) : iProp := P ∗ closed_world u b ⊤.

  (***** wsim lemmas ****)

  Lemma wsim_discard 
        E0 E1 r g {R} RR
        ps pt sti_src sti_tgt
        (TOP: E0 ⊆ E1)
    :
      (@wsim E0 r g R RR ps pt sti_src sti_tgt)
    -∗
      (wsim E1 r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. 
    Local Transparent world. 
    iIntros "H [W [E U]]". 
    iApply "H". iFrame. iPoseProof (OwnE_subset with "E") as "[E0 E1]"; [eapply TOP|]. iFrame.
  Qed.

  Lemma wsim_upd
    E r g {R} ps pt sti_src sti_tgt
    (RR: Any.t * R -> Any.t * R -> iProp)
  :
    (#=> (wsim E r g RR ps pt sti_src sti_tgt))
  -∗
    wsim E r g RR ps pt sti_src sti_tgt.
  Proof.
    unfold wsim. destruct sti_src, sti_tgt.
    iIntros "H WD". iApply isim_upd. iMod "H". iModIntro.
    iApply "H"; eauto.
  Qed.

  
  (* Comment: Update modality diff??: RR -∗#=> RR' in fairness *)
  Lemma wsim_wand 
    E r g {R} RR0 RR1 ps pt sti_src sti_tgt
  :
    (@wsim E r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (∀ st_src ret_src st_tgt ret_tgt,
          ((RR0 (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR1 (st_src, ret_src) (st_tgt, ret_tgt))))
      -∗
        (wsim E r g RR1 ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H R D".
    iApply isim_wand.
    iPoseProof ("H" with "D") as "H".
    iSplitR "H"; [|auto]. iIntros (? ? ? ?) "H".
    iPoseProof ("R" $! _ _ with "H") as "H". iFrame.
  Qed.

  Lemma wsim_mono 
    E r g {R} RR0 RR1 ps pt sti_src sti_tgt
    (MONO: forall st_src r_src st_tgt r_tgt,
              (RR0 (st_src, r_src) (st_tgt, r_tgt))
            -∗
              ((RR1 (st_src, r_src) (st_tgt, r_tgt))))
  :
    (@wsim E r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (wsim E r g RR1 ps pt sti_src sti_tgt).
  Proof.
    iIntros "H". iApply (wsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma wsim_frame 
    E r g {R} RR ps pt sti_src sti_tgt
    P
  :
    (@wsim E r g R RR ps pt sti_src sti_tgt)
  -∗
    (P -∗ (wsim E r g (fun str_src str_tgt => P ∗ RR str_src str_tgt) ps pt sti_src sti_tgt))
  .
  Proof.
    iIntros "H0 H1". iApply (wsim_wand with "H0").
    iIntros. iFrame.
  Qed.

  Lemma wsim_bind_top
    E r g {R S} RR ps pt st_src st_tgt i_src i_tgt k_src k_tgt
  :
    (@wsim E r g S (fun '(s_src, r_src) '(s_tgt, r_tgt) => isim r g RR false false (s_src, k_src r_src) (s_tgt, k_tgt r_tgt)) ps pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (@wsim E r g R RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    iIntros "H W". iPoseProof ("H" with "W") as "H".
    iApply isim_bind. iApply (isim_mono with "H"). eauto.
  Qed.

  (****** FUpd Rules ******)

  Lemma wsim_FUpd
    E0 E1 r g {R} RR ps pt sti_src sti_tgt 
  :
    (FUpd u b emp E0 E1 (wsim E1 r g RR ps pt sti_src sti_tgt))
  -∗
    (@wsim E0 r g R RR ps pt sti_src sti_tgt).
  Proof.
    Local Transparent FUpd.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "F WD".
    iAssert (emp ∗ world u b E0)%I with "[WD]" as "WD". { iFrame. }
    iApply isim_upd.
    iMod ("F" with "WD") as "(_ & W & SIM)".
    iApply "SIM"; iFrame. eauto.
  Qed.

  Lemma wsim_FUpd_weaken 
    r g {R} RR ps pt sti_src sti_tgt
    (E0 E1: coPset)
    (SUB: E0 ⊆ E1)
  :
    (FUpd u b emp E0 E0 (@wsim E1 r g R RR ps pt sti_src sti_tgt))
  -∗
    (wsim E1 r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    iIntros "H". iApply wsim_FUpd. iApply FUpd_mask_mono; eauto. 
  Qed.

  Global Instance wsim_elim_FUpd_gen
         r g {R} RR
         (E0 E1 E2: coPset)
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E0 ⊆ E2) p false 
    (FUpd u b emp E0 E1 P) 
    P 
    (@wsim E2 r g R RR ps pt sti_src sti_tgt) 
    (wsim (E1 ∪ (E2 ∖ E0)) r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd. iMod "H0". iModIntro. iApply "H1". iFrame.
  Qed.

  Global Instance wsim_elim_FUpd_eq
         (E1 E2: coPset) r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E1 ⊆ E2) p false 
    (FUpd u b emp E1 E1 P) 
    P
    (@wsim E2 r g R RR ps pt sti_src sti_tgt) 
    (wsim E2 r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wsim_elim_FUpd
         E0 E1 r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal True p false 
    (FUpd u b emp E0 E1 P)
    P
    (@wsim E0 r g R RR ps pt sti_src sti_tgt)
    (wsim E1 r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "(H0 & H1)".
    iApply wsim_FUpd. instantiate (1:= E1).
    iMod "H0". iApply FUpd_intro. iModIntro. (* iModIntro doesn't work. why? *)
    iApply "H1". eauto.
  Qed.
  
  Global Instance wsim_add_modal_FUpd
         E r g {R} RR
         ps pt sti_src sti_tgt
         P
    :
    AddModal (FUpd u b emp E E P) P (@wsim E r g R RR ps pt sti_src sti_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]".
    iApply ("H1" with "H0").
  Qed.

  (**** Simulation Rules ****)

  Lemma wsim_ret
    r g {R} ps pt st_src st_tgt v_src v_tgt
    (RR: Any.t * R -> Any.t * R -> iProp)
  :
    (RR (st_src, v_src) (st_tgt, v_tgt))
  -∗
    (@wsim ⊤ r g R RR ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt)).
  Proof.
    iIntros "H". unfold wsim. iIntros "[W [E U]]".
    iApply isim_upd. iApply isim_ret. iFrame. eauto.
  Qed.

  Lemma wsim_call 
    E r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg
  :
    ((Ist st_src st_tgt) ∗ (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -∗ @wsim E r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗  
    (wsim E r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "[IST H] WD". iApply isim_call. iFrame.
    iIntros (? ? ?) "IST". iPoseProof ("H" with "IST") as "H". iApply "H". eauto.
  Qed.  

  Lemma wsim_syscall
    E r g {R} RR ps pt st_src st_tgt k_src k_tgt fn varg rvs
  :
    (∀ vret, @wsim E r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
  -∗
    (wsim E r g RR ps pt (st_src, trigger (IO fn varg rvs) >>= k_src) (st_tgt, trigger (IO fn varg rvs) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_syscall. iIntros. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_inline_src
    E r g ps pt {R} RR st_src st_tgt k_src i_tgt f fn varg 
    (FIND: alist_find fn fl_src = Some f)
  :
  bi_entails
    (@wsim E r g R RR true pt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    (@wsim E r g R RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_inline_src; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.
  
  Lemma wsim_inline_tgt
    E r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    unfold wsim. iIntros "H D".
    iApply isim_inline_tgt; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_tau_src
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim E r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_src. iFrame.
  Qed.


  Lemma wsim_tau_tgt
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_tgt. iFrame.
  Qed.

  Lemma wsim_choose_src 
    E X x r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (@wsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim E r g RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_choose_src. iFrame.
  Qed.

  Lemma wsim_choose_tgt 
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (∀ x, @wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_choose_tgt. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_src 
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (∀ x, @wsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim E r g RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_take_src. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_tgt 
    E X x r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_take_tgt. iFrame.
  Qed.
  
  Lemma wsim_supdate_src
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim E r g R RR true pt ((run st_src).1, k_src (run st_src).2) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_src. iFrame.
  Qed.

  Lemma wsim_supdate_tgt
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim E r g R RR ps true (st_src, i_src) ((run st_tgt).1, k_tgt (run st_tgt).2))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_tgt. iFrame.
  Qed.

  Lemma wsim_assume_src
    P r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (P ∗ free_worlds u b -∗ (@wsim ⊤ r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
  -∗
    (isim r g RR ps pt (st_src, trigger (Assume (wclosed u b P)) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iApply isim_assume_src. iIntros "(P & (F & W))".
    iPoseProof ("H" with "[P F]") as "H". iFrame.
    iApply "H". eauto.
  Qed.

  Lemma wsim_guarantee_src
    P r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (P ∗ free_worlds u b ∗ @isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt))
  -∗
    (wsim ⊤ r g RR ps pt (st_src, trigger (Guarantee (wclosed u b P)) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "(P & F & H) WD". iApply isim_guarantee_src. iFrame.
  Qed.  
  
  Lemma wsim_assume_tgt
    P u0 b0 E r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (wclosed u0 b0 P ∗ (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Assume (wclosed u0 b0 P)) >>= k_tgt)).
  Proof.
    iIntros "(P & H) WD". iApply isim_assume_tgt. iFrame.
    iApply "H". eauto.
  Qed.

  Lemma wsim_guarantee_tgt
    P u0 b0 E r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (wclosed u0 b0 P -∗ @wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Guarantee (wclosed u0 b0 P)) >>= k_tgt)).
  Proof.
    iIntros "H WD". iApply isim_guarantee_tgt. iIntros "IP".
    iPoseProof ("H" with "IP") as "H". iApply "H". eauto.
  Qed.  

  Lemma wsim_progress
    E r g {R} RR sti_src sti_tgt
  :
    @wsim E g g R RR false false sti_src sti_tgt
  -∗
    @wsim E r g R RR true true sti_src sti_tgt.
  Proof.
    destruct sti_src, sti_tgt. iIntros "H WD".
    iApply isim_progress. iApply "H". eauto.
  Qed.

  Lemma wsim_base E r g R (RR: Any.t * R -> Any.t * R -> iProp)
    ps pt sti_src sti_tgt
    :
    bi_entails
      (world u b E -∗ r R RR ps pt sti_src sti_tgt)
      (wsim E r g RR ps pt sti_src sti_tgt).
  Proof.
    iIntros "H W". iApply isim_base. iApply "H". eauto.
  Qed.

  Lemma wsim_reset 
    E r g {R} RR ps pt sti_src sti_tgt
  :
    bi_entails
      (@wsim E r g R RR false false sti_src sti_tgt)
      (@wsim E r g R RR ps pt sti_src sti_tgt).
  Proof.
    iIntros "H W". iApply isim_reset. iApply "H". eauto.
  Qed.

  Lemma wsim_coind E r g A P RA RRA psA ptA srcA tgtA
    (COIND: forall g0 (a:A),
      bi_entails
        ((□ ((∀ R RR ps pt src tgt, g R RR ps pt src tgt -∗ g0 R RR ps pt src tgt) ∗
             (∀ a, P a ∗ world u b E -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))) ∗
         P a)
        (@wsim E r g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))
    :
    forall (a:A),
      bi_entails
        (P a)
        (@wsim E r g (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)).
  Proof.
    i. iIntros "P W". iApply (isim_coind _ (fun a => P a ∗ world u b E)%I); i.
    - iIntros "(H & P & W)". iRevert "W". iApply COIND. eauto.
    - iFrame.
  Qed.

  (********)

  Lemma wsim_triggerUB_src
    E r g {R} RR ps pt X st_src st_tgt (k_src: X -> _) i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    iIntros "H". unfold triggerUB. hred_l. iApply wsim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerUB_src_trigger
    E r g {R} RR ps pt st_src st_tgt i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply wsim_triggerUB_src. auto.
  Qed.

  Lemma wsim_triggerNB_tgt
    E r g {R} RR ps pt X st_src st_tgt i_src (k_tgt: X -> _)
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply wsim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerNB_trigger
    E r g {R} RR ps pt st_src st_tgt i_src
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply wsim_triggerNB_tgt. auto.
  Qed.

  Lemma wsim_unwrapU_src
      E r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -∗ wsim E r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
        (@wsim E r g R RR ps pt (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply wsim_triggerUB_src. auto. }
  Qed.

  Lemma wsim_unwrapN_src
    E r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∗ @wsim E r g R RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (wsim E r g RR ps pt (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma wsim_unwrapU_tgt
    E r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∗ @wsim E r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim E r g RR ps pt (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma wsim_unwrapN_tgt
    E r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -∗ @wsim E r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim E r g RR ps pt (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply wsim_triggerNB_tgt. auto. }
  Qed.

  (**** TODO ****)

  (* Definition wsim_fsem RR: relation (Any.t -> itree hmodE Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt,
             Ist st_src st_tgt ⊢ @isim ibot ibot Any.t RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature. *)

  (* Definition wsim_fnsem RR: relation (string * (Any.t -> itree hmodE Any.t)) := RelProd eq (wsim_fsem RR). *)

End WSIM.

Section WSIM_LEVEL_UP.

  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{CtxWD.t}.
  
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hmodE Any.t).

  Let wsim u b := wsim Ist fl_src fl_tgt u b.

  Lemma wsim_level_up u b b' E r g R RR ps pt src tgt
      (LE: b <= b'):
    (free_worlds u b' -∗ @wsim u b' E r g R RR ps pt src tgt)
    -∗
    (free_worlds u b -∗ @wsim u b E r g R RR ps pt src tgt).
  Proof.
    iIntros "H FA W".
    iPoseProof (closed_world_mon with "[FA W]") as "[FA' W']"; eauto.
    - iFrame.
    - iPoseProof ("H" with "FA'") as "H". iApply "H". eauto.
  Qed.

End WSIM_LEVEL_UP.

Global Opaque wsim.

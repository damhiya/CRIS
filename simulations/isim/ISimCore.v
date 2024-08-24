Require Import Coqlib sflib ITreelib.
Require Import STS.
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
Require Import World sWorld.
Require Import Red IRed.
Require Import SubPerm.

From stdpp Require Import coPset gmap.
(* Require Import FancyUpdate. *)


Set Implicit Arguments.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).


Section SIM.

  Context `{Σ: GRA.t}.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hmodE Any.t).
  Variable Ist: alist key Any.t -> alist key Any.t -> iProp.
  
  Let _hpsim := @_hpsim Σ fl_src fl_tgt Ist false.
  Let rel := ∀ R : Type, (alist key Any.t * R → alist key Any.t * R → iProp) → bool → bool → alist key Any.t * itree hmodE R → alist key Any.t * itree hmodE R → iProp.

  Variant iunlift (r: rel) R RR ps pt sti_src sti_tgt res: Prop :=
    | unlift_intro
        (WF: URA.wf res)
        (REL: Own res ⊢ |==> r R RR ps pt sti_src sti_tgt).

  Definition ibot : rel := fun _ _ _ _ _ _ => False%I.

  Program Definition isim
          r g {R} (RR: alist key Any.t * R-> alist key Any.t * R -> iProp) ps pt
          (sti_src sti_tgt : alist key Any.t * itree hmodE R): iProp := 
    iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) (iunlift r) (iunlift g) _ RR ps pt sti_src sti_tgt) _.
  Next Obligation.
    guclo hpsim_extendC_spec. econs; et.
  Qed.

(***** isim lemmas *****)

  Lemma iunlift_ibot:
    iunlift ibot <7= bot7.
  Proof.
    unfold ibot. i. destruct PR.
    eapply Own_iProp in REL; eauto.
    rr in REL. uiprop in REL. des.
    rr in REL. uiprop in REL. eauto.
  Qed.

  Lemma isim_init
      r g ps pt {R} RR st_src st_tgt i_src i_tgt iP fmr
      (ENTAIL: bi_entails
                iP
                (@isim r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt)))
      (CUR: Own fmr ⊢ iP)
    :
      gpaco7 _hpsim (cpn7 _hpsim) (iunlift r) (iunlift g) R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in ENTAIL. exploit ENTAIL; eauto using Own_iProp.
  Qed.

  Lemma iunlift_mon r0 r1
    (MON: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@r0 R RR ps pt sti_src sti_tgt)
              (#=> @r1 R RR ps pt sti_src sti_tgt))
  :
    iunlift r0 <7= iunlift r1.
  Proof.
    i. destruct PR. econs; eauto.
    iIntros "H". iPoseProof (REL with "H") as "H".
    iMod "H". iPoseProof (MON with "H") as "H". eauto.
  Qed.

  Lemma isim_mono_knowledge 
    r0 g0 r1 g1 {R} RR ps pt sti_src sti_tgt
    (MON0: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@r0 R RR ps pt sti_src sti_tgt)
              (#=> @r1 R RR ps pt sti_src sti_tgt))
    (MON1: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@g0 R RR ps pt sti_src sti_tgt)
              (#=> @g1 R RR ps pt sti_src sti_tgt))
    :
    bi_entails
      (@isim r0 g0 R RR ps pt sti_src sti_tgt)
      (@isim r1 g1 R RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. 
    eapply gpaco7_mon; eauto using iunlift_mon.
  Qed.

  Lemma isim_upd
      r g ps pt {R} RR sti_src sti_tgt
    :
      bi_entails
        (#=> (@isim r g R RR ps pt sti_src sti_tgt))
        (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. des. guclo hpsim_updateC_spec. econs. ii.
    esplits; eauto. eapply Own_Upd; eauto.
  Qed.

  Global Instance isim_elim_upd
    r g {R} RR ps pt sti_src sti_tgt
    P p
  :
    ElimModal True p false (#=> P) P 
    (@isim r g R RR ps pt sti_src sti_tgt) 
    (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  (* GIL: Deleted the following because it is subsumed by [isim_wand]. *)
  (* Restored to use in wsim_bind_top *)
  Lemma isim_mono
    r g ps pt {R} RR0 RR1 sti_src sti_tgt
    (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (RR0 (st_src, ret_src) (st_tgt, ret_tgt)) (RR1 (st_src, ret_src) (st_tgt, ret_tgt))))
    :
      bi_entails
        (@isim r g R RR0 ps pt sti_src sti_tgt)
        (@isim r g R RR1 ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i). rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec. econs; eauto.
    i. gstep. econs. ii. esplits; eauto. econs; eauto.
    iIntros "H". iApply MONO. iStopProof. eauto.
  Qed.

  (* Try RR` -∗#=> RR *)
  Lemma isim_wand
        r g ps pt {R} RR RR' sti_src sti_tgt        
    :
      bi_entails
        ((∀ st_src ret_src st_tgt ret_tgt,
            ((RR' (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR (st_src, ret_src) (st_tgt, ret_tgt)))) ∗ (@isim r g R RR' ps pt sti_src sti_tgt))
        (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    rr. rewrite Seal.sealing_eq. i.
    guclo hpsim_frameC_spec.
    apply iProp_Own in H. eapply iProp_sepconj in H; des; eauto. subst.
    apply iProp_Own in H0.
    econs; cycle 1.
    { iIntros "[P Q]". iSplitL "Q". eauto.
      iPoseProof (H0 with "P") as "P". eauto.
    }
    
    destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i). rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec. econs; eauto.
    { apply H1. }
    i. gstep. econs. ii. esplits; eauto. econs; eauto.
    iIntros "H". iPoseProof (RET with "H") as "H". iMod "H".
    iModIntro. iIntros "Y". iApply "Y". eauto.
  Qed.

  Lemma isim_frame 
    r g {R} RR ps pt sti_src sti_tgt
    P
  :
    bi_entails
      (P ∗ @isim r g R RR ps pt sti_src sti_tgt)
      (isim r g (fun str_src str_tgt => P ∗ RR str_src str_tgt) ps pt sti_src sti_tgt)%I.
  Proof.
    iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto.
  Qed.

  Lemma isim_bind 
    r g ps pt {R S} RR st_src st_tgt i_src i_tgt k_src k_tgt        
  :
    bi_entails
    (@isim r g S
          (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
              (@isim r g R RR false false (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt))%I)
          ps pt (st_src, i_src) (st_tgt, i_tgt))
        (isim r g RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    uiprop. i.
    guclo hpsim_bindC_spec. econs; eauto.
    i. guclo hpsim_updateC_spec. econs.
    uiprop in RET. ii. exploit RET; eauto; try refl.
    i; des. esplits; eauto. eapply Own_Upd; eauto.
  Qed.


  (* Simulation rules *)
  Lemma isim_ret
    r g ps pt {R} RR st_src st_tgt v_src v_tgt
  :
    bi_entails
      (RR (st_src, v_src) (st_tgt, v_tgt))
      (@isim r g R RR ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. uiprop. i. eauto using iProp_mono.
  Qed.

  Lemma isim_tau_src
    r g ps pt {R} RR st_src st_tgt i_src i_tgt
  :
    bi_entails
      (@isim r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_tau_tgt
    r g ps pt {R} RR st_src st_tgt i_src i_tgt
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_call 
    r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg
  :
    bi_entails
      ((Ist st_src st_tgt) ∗
       (∀ st_src0 st_tgt0 vret
            (NODS: List.NoDup (List.map fst st_src0))
            (NODD: List.NoDup (List.map fst st_tgt0)),
          (Ist st_src0 st_tgt0) -∗ @isim r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
      (isim r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof.
    rr. unseal "iProp". i.
    guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst. 
    { eapply iProp_Own in H.
      iIntros "OWN".
      iPoseProof (H with "OWN") as "(IST & SIM)".
      iFrame. iSplitL""; eauto.
    }
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! st_src0 st_tgt0 vret NODS NODD).
    iApply "B". eauto.
  Qed.

  Lemma isim_io
    r g ps pt {R} RR st_src st_tgt I O k_src k_tgt fn (varg: I)
  : 
    bi_entails
      (∀ (vret: O), @isim r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
      (isim r g RR ps pt (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto. i.
    eapply iProp_Own in H.
    eapply isim_init; eauto.
    iIntros "H". iApply (H with "H").   
  Qed.

  Lemma isim_inline_src
    r g ps pt {R} RR st_src st_tgt k_src i_tgt f fn varg 
    (FIND: alist_find fn fl_src = Some f)
  :
  bi_entails
    (@isim r g R RR true pt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    (@isim r g R RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. grind.
    pattern (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_src x).
    replace (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_src x) with (f varg >>= k_src); grind.
    rewrite <- bind_bind. f_equal. etrans.
    { instantiate (1:=  (`x : Any.t <- f varg;; Ret x)). grind. } 
    f_equal. extensionality x. grind.
  Qed.

  Lemma isim_inline_tgt
    r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. grind.
    pattern (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_tgt x).
    replace (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_tgt x) with (f varg >>= k_tgt); grind.
    rewrite <- bind_bind. f_equal. etrans.
    { instantiate (1:= (`x : Any.t <- f varg;; Ret x)). grind. }
    f_equal. extensionality x. grind. 
  Qed.
  
  Lemma isim_take_src
    X r g ps pt {R} RR st_src st_tgt k_src i_tgt 
  :
    bi_entails
      (∀ x, @isim r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    eapply isim_init; eauto. eapply iProp_Own in H.
    iIntros "H". iApply (H with "H").
  Qed.

  Lemma isim_take_tgt
    X x r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_choose_src
    X x r g ps pt {R} RR st_src st_tgt k_src i_tgt
  :
    bi_entails
      (@isim r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_choose_tgt
    X r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (∀x, @isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    eapply isim_init; eauto. eapply iProp_Own in H.
    iIntros "H". iApply (H with "H").
  Qed.

  Lemma isim_asm_src
    (P: Prop) r g ps pt {R} RR st_src st_tgt k_src i_tgt 
  :
    bi_entails
      (∀ (_: P), @isim r g R RR true pt (st_src, k_src ()) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, assume P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_src. rewrite bind_ret_l. eauto.
  Qed.
  
  Lemma isim_asm_tgt
    (P: Prop) r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    P ->
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt ()))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, assume P >>= k_tgt)).
  Proof.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_tgt. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.
  
  Lemma isim_guar_src
    (P: Prop) r g ps pt {R} RR st_src st_tgt k_src i_tgt
  :
    P ->
    bi_entails
      (@isim r g R RR true pt (st_src, k_src ()) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, guarantee P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_src. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_tgt
    (P: Prop) r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (∀ (_:P), @isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt ()))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, guarantee P >>= k_tgt)).
  Proof. 
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_tgt. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_sput_src
    r g ps pt {R} RR  k v st_src st_tgt k_src i_tgt
    :
    bi_entails
      (@isim r g R RR true pt (alist_add k v st_src, k_src tt) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_sput_src_sandbox
    r g ps pt {R} RR  k v st_src st_tgt k_src i_tgt scopes
    :
    In k.1 scopes ->
    bi_entails
      (@isim r g R RR true pt (alist_add k v st_src, k_src tt) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, HModSem.sandbox scopes (trigger (SPut k v)) >>= k_src) (st_tgt, i_tgt)).
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
  
  Lemma isim_sput_tgt
    r g ps pt {R} RR k v st_src st_tgt i_src k_tgt
    :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (alist_add k v st_tgt, k_tgt tt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_sput_tgt_sandbox
    r g ps pt {R} RR k v st_src st_tgt i_src k_tgt scopes
    :
    In k.1 scopes ->
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (alist_add k v st_tgt, k_tgt tt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, HModSem.sandbox scopes (trigger (SPut k v)) >>= k_tgt)).
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
  
  Lemma isim_sget_src
    r g ps pt {R} RR k st_src st_tgt k_src i_tgt
    :
    bi_entails
      (@isim r g R RR true pt (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_sget_src_sandbox
    r g ps pt {R} RR k st_src st_tgt k_src i_tgt scopes
    :
    In k.1 scopes ->
    bi_entails
      (@isim r g R RR true pt (st_src, k_src (or_else (alist_find k st_src) tt↑)) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, HModSem.sandbox scopes (trigger (SGet k)) >>= k_src) (st_tgt, i_tgt)).
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
  
  Lemma isim_sget_tgt
    r g ps pt {R} RR k st_src st_tgt i_src k_tgt
    :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.

  Lemma isim_sget_tgt_sandbox
    r g ps pt {R} RR k st_src st_tgt i_src k_tgt scopes
    :
    In k.1 scopes ->
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt (or_else (alist_find k st_tgt) tt↑)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, HModSem.sandbox scopes (trigger (SGet k)) >>= k_tgt)).
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
  
  Lemma isim_Assume_src
    r g ps pt {R} RR iP st_src st_tgt k_src i_tgt 
    :
    bi_entails
      (iP -∗ (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
      (@isim r g R RR ps pt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. i.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in NEW. edestruct NEW; eauto; try refl. des.
    guclo hpsim_updateC_spec. econs. ii. subst.
    esplits.
    - eapply H; eauto.
      eapply URA.wf_extends.
      { eapply URA.extends_add. eauto. }
      specialize (H3 ε). rewrite URA.add_comm. revert H3. r_solve. eauto.
    - eapply Own_Upd. ii. apply H3 in H2. eapply URA.wf_extends; eauto.
      rewrite (URA.add_comm a b). repeat apply URA.extends_add. eauto.
  Qed.

  Lemma isim_Assume_tgt
    r g ps pt {R} RR iP st_src st_tgt i_src k_tgt 
    :
    bi_entails
      (iP ∗ (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt)).
  Proof.
    uiprop. i. des. subst. 
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    { instantiate (1:= (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt))).
      eapply iProp_Own in H0.
      iIntros "[A B]". iPoseProof (H0 with "A") as "A". iFrame. iStopProof.
      eapply iProp_Own. uiprop. eauto.
    }
    eapply isim_init; eauto.
    iIntros "H". iApply isim_upd. iStopProof; eauto.
  Qed.

  Lemma isim_Guarantee_src
    r g ps pt {R} RR iP st_src st_tgt k_src i_tgt 
    :
    bi_entails
      (iP ∗ (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
      (@isim r g R RR ps pt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. des. subst.
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    { instantiate (1:= (@isim r g R RR true pt (st_src, k_src ()) (st_tgt, i_tgt))).
      eapply iProp_Own in H0.
      iIntros "[A B]". iPoseProof (H0 with "A") as "A". iFrame. iStopProof.
      eapply iProp_Own. uiprop. eauto.
    }
    eapply isim_init; eauto.
    iIntros "H". iApply isim_upd. iStopProof; eauto.
  Qed.

  Lemma isim_Guarantee_tgt
    r g ps pt {R} RR iP st_src st_tgt i_src k_tgt 
    :
    bi_entails
      (iP -∗ (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. i.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in NEW. edestruct NEW; eauto; try refl. des.
    guclo hpsim_updateC_spec. econs. ii. subst.
    esplits.
    - eapply H; eauto.
      eapply URA.wf_extends.
      { eapply URA.extends_add. eauto. }
      specialize (H3 ε). rewrite URA.add_comm. revert H3. r_solve. eauto.
    - eapply Own_Upd. ii. apply H3 in H2. eapply URA.wf_extends; eauto.
      rewrite (URA.add_comm a b). repeat apply URA.extends_add. eauto.
  Qed.

  Lemma isim_progress
    r g {R} RR st_src st_tgt i_src i_tgt
    :
    bi_entails
      (@isim g g R RR false false (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR true true (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. eapply hpsim_progress_flag. eauto.
  Qed.  

  Lemma isim_triggerUB_src
    r g {R} RR ps pt X st_src st_tgt (k_src: X -> _) i_tgt
    :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    iIntros "H". unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger
    r g {R} RR ps pt st_src st_tgt i_tgt
    :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply isim_triggerUB_src. auto.
  Qed.

  Lemma isim_triggerNB_tgt
    r g {R} RR ps pt X st_src st_tgt i_src (k_tgt: X -> _)
    :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger
    r g {R} RR ps pt st_src st_tgt i_src
    :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply isim_triggerNB_tgt. auto.
  Qed.

  Lemma isim_unwrapU_src
    r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. auto. }
  Qed.

  Lemma isim_unwrapN_src
    r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∗ @isim r g R RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (isim r g RR ps pt (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma isim_unwrapU_tgt
    r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
    :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∗ @isim r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (isim r g RR ps pt (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapN_tgt
    r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
    :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -∗ @isim r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (isim r g RR ps pt (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. auto. }
  Qed.

  Lemma isim_base r g R RR
    ps pt sti_src sti_tgt
    :
    bi_entails
      (r R RR ps pt sti_src sti_tgt)
      (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. gfinal. left. econs; eauto.  eapply iProp_Own in H.
    iIntros "H". iModIntro. iStopProof. eauto.
  Qed.

  Lemma isim_reset 
    r g {R} RR ps pt sti_src sti_tgt
    :
    bi_entails
      (@isim r g R RR false false sti_src sti_tgt)
      (@isim r g R RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. eapply hpsim_flag_down. eauto. 
  Qed.
  
  Lemma isim_coind (r g: rel) A P RA RRA psA ptA srcA tgtA
    (COIND: forall (g0: rel) (a:A),
        bi_entails
          ((□ ((∀ R RR ps pt src tgt, g R RR ps pt src tgt -∗ g0 R RR ps pt src tgt) ∗
                  (∀ a, P a -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))) ∗
             P a)
          (@isim r g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))
    :
    forall (a:A),
      bi_entails
        (P a)
        (@isim r g (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)).
  Proof.
    i. iIntros "H". iPoseProof (bupd_intro with "H") as "H". iStopProof.
    rr. autorewrite with iprop.
    revert a. gcofix CIH. i.
    uiprop in H0. des.
    guclo hpsim_updateC_spec. econs. ii. exists r2.
    esplits; cycle 1.
    { uiprop. i. exists r2. split; try refl.
      i. eapply H1. eapply URA.wf_extends; eauto. apply URA.extends_add; eauto. }
    clear r1 H1 H WF.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    specialize (COIND
                  (fun R RR ps pt src tgt =>
                     g R RR ps pt src tgt ∨
                       ∃ a, P a ∗ ⌜@existT Type (fun _ => _) R (RR,ps,pt,src,tgt) =
                               existT (RA a) (RRA a,psA a,ptA a,srcA a,tgtA a)⌝)%I a).
    rr in COIND. autorewrite with iprop in COIND.
    eapply gpaco7_mon. eapply COIND; eauto.
    - rr. autorewrite with iprop. exists ε, r2. r_solve.
      esplits; eauto. eapply Own_iProp, URA.wf_unit.
      iIntros "_". iModIntro. iSplitL "".
      + iIntros (R RR ps pt src tgt) "H". iFrame.
      + iIntros (a0) "HP". iRight. iExists a0. iFrame. eauto.
    - eauto.
    - i. destruct PR. rr in REL. autorewrite with iprop in REL.
      exploit REL; eauto using Own_iProp. clear REL.
      intros REL. rr in REL. autorewrite with iprop in REL.
      des. rr in REL. autorewrite with iprop in REL. des.
      + eapply CIH0. econs; eauto.
        rr; i. uiprop. i. esplits; eauto.
        i. apply REL0. eapply URA.wf_extends, H2. eapply URA.extends_add; eauto.
      + repeat (rr in REL; autorewrite with iprop in REL; des). subst.
        rr in REL2. uiprop in REL2. depdes REL2.
        eapply CIH; eauto. uiprop. esplits; eauto.
        i. apply REL0 in H1. eapply URA.wf_mon with (b:=b).
        eapply eq_ind; eauto. r_solve.
  Qed.

  Lemma combine_quant A (B: A -> Type) (P: forall a (b: B a), Prop)
      (PR: forall (ab: sigT B), P (projT1 ab) (projT2 ab)):
    forall a b, P a b.
  Proof. i. eapply (PR (existT a b)). Qed.

  Definition isim_fsem RR: relation (Any.t -> itree hmodE Any.t) :=
    (eq ==> (fun itr_src itr_tgt =>
               forall st_src st_tgt
                      (NODS: List.NoDup (List.map fst st_src))
                      (NODD: List.NoDup (List.map fst st_tgt)),
                 Ist st_src st_tgt ⊢ @isim ibot ibot Any.t RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  (* Definition isim_fnsem RR: relation (string * (Any.t -> itree hmodE Any.t)) := RelProd eq (isim_fsem RR). *)
  
End SIM.

Global Opaque isim.

Module HModSemR.
  Section SIM.
    Import HModSem.
    Context `{_W: CtxWD.t}. 
    Variable (ms_src ms_tgt: HModSem.t).
    Variable Ist: alist key Any.t -> alist key Any.t -> iProp.

    Let scopes_src := ms_src.(scopes).
    Let scopes_tgt := ms_tgt.(scopes).
    Let fnsems_src := ms_src.(fnsems).
    Let fnsems_tgt := ms_tgt.(fnsems).
    Let init_src := ms_src.(initial_st).
    Let init_tgt := ms_tgt.(initial_st).
    Let cond_src := ms_src.(initial_cond).
    Let cond_tgt := ms_tgt.(initial_cond).

    Definition sim_fun fn : Prop :=
      forall
        (NODUPFS: List.NoDup (List.map fst fnsems_src))
        (NODUPFT: List.NoDup (List.map fst fnsems_tgt))
        fs (FIND: alist_find fn fnsems_src = Some fs),
      exists ft, alist_find fn fnsems_tgt = Some ft /\
                   isim_fsem
                     (List.map (map_snd HModSem.sandbox_body) fnsems_src)
                     (List.map (map_snd HModSem.sandbox_body) fnsems_tgt)
                     Ist (fun '(st_src, v_src) '(st_tgt, v_tgt) => (Ist st_src st_tgt ∗ ⌜v_src = v_tgt⌝))%I
                     (HModSem.sandbox_body fs) (HModSem.sandbox_body ft).

    Inductive sim: Prop :=
      mk {
          sim_initial:
            cond_src ⊢ cond_tgt ∗ (Ist init_src init_tgt);
          sim_scopes:
            sub_perm scopes_tgt scopes_src; 
          sim_length:
            List.length fnsems_src = List.length fnsems_tgt;
          sim_match:
            forall fn (IN: In fn (List.map fst fnsems_tgt)),
              In fn (List.map fst fnsems_src);
          sim_fnsems:
            forall fn (IN: In fn (List.map fst fnsems_src)),
              sim_fun fn;
        }.

  End SIM.
End HModSemR.


Module HModR.
  Section SIM.
    Context `{_W: CtxWD.t}. 
    Variable (md_src md_tgt: HMod.t).
    Variable Ist: Sk.t -> alist key Any.t -> alist key Any.t -> iProp.

    Inductive sim: Prop :=
      mk {
          sim_modsem:
            forall sk (SKINCL: Sk.incl md_tgt.(HMod.sk) sk) (SKWF: Sk.wf sk),
              <<SIM: HModSemR.sim (md_src.(HMod.get_modsem) sk) (md_tgt.(HMod.get_modsem) sk) (Ist sk)>>;
          sim_sk: <<SIM: md_src.(HMod.sk) = md_tgt.(HMod.sk)>>;
        }.

    Definition sim_fun fn : Prop :=
      forall sk,
        HModSemR.sim_fun (HMod.get_modsem md_src sk) (HMod.get_modsem md_tgt sk) (Ist sk) fn.

  End SIM.
End HModR.

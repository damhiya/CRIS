Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod.
Require Import MSimCommon MSim LSim LSimTactics.

(* MSIM_FRAME *)
Lemma msim_ist_frame `{Σ: GRA} contextual fl_src fl_tgt Rs Rt RR Ist P ps pt nths (sti_s: _ * itree crisE Rs) (sti_t: _ * itree crisE Rt) fmr0 fmr
  (SIM : msim contextual fl_src fl_tgt Ist RR ps pt nths sti_s sti_t fmr0)
  (FMR: Own fmr ⊢ |==> P ∗ Own fmr0)
  :
  msim contextual fl_src fl_tgt (λ x y z, P ∗ Ist x y z)%I (λ x y z, P ∗ RR x y z)%I ps pt nths sti_s sti_t fmr.
Proof.
  ginit. revert_until P. gcofix CIH. i.
  gstep.
  punfold SIM. move SIM before CIH. revert_until SIM.
  pattern ps, pt, nths, sti_s, sti_t, fmr0.
  eapply _msim_tarski, SIM. i.
  econs. ii.
  exploit IN; et.
  { eapply Own_wand_valid, H. rewrite FMR. iIntros "[_ H]". et. }
  i; des. esplits; et.
  destruct x0;
    try by econs; et; i; eapply K; et;
           rewrite FMR x1; iIntros ">[? >?]"; iFrame; et.
  - econs; et. rewrite FMR x1 RET. iIntros ">[? >>?]". iFrame. et.
  - econs; et.
    { rewrite FMR x1 INV. iIntros ">[? >>[? ?]]". iFrame. et. }
    i. rewrite -assoc in INV0.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in INV0; et. des.
    eapply K; et; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - econs; et; i.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - econs; et; i.
    (* { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. } *)
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[> > ? ?]". iFrame. et.
  - econs; et; i.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply K; et; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - econs; et; i.
    { rewrite FMR x1 CUR //. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et.
    }
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); et; cycle 1.
    + rewrite NEW1; iIntros "$ //".
    + rewrite NEW NEW0. et.
    + eapply Own_wand_valid; [iIntros "H"; iMod (NEW with "H") as "[_ $]"|]; ss.
  - econs; et; i.
    { rewrite FMR x1 INV. iIntros ">[? >>[? ?]]". iFrame. et. }
    rewrite -assoc in INV0.
    destruct (classic (✓ fmr3)); [| econs; ii; ss].
    eapply Own_bupd_split in INV0; et. des.
    eapply K; et; cycle 1.
    + rewrite INV0 INV1. et.
    + rewrite INV2. et.
  - pclearbot. econs; et; i.
    gbase. eapply CIH; et.
    rewrite FMR x1. iIntros ">[? >?]". iFrame. et.
Qed.

(* MSIM_ADEQUACY *)

(*** Used only in hsim_adequacy. ***)
Lemma own_upd_in_middle `{Σ: GRA} mr_src mr_tgt ctx fmr fmr0
    (UPD : Own mr_src ⊢ |==> Own (ctx ⋅ fmr ⋅ mr_tgt))
    (FMR : Own fmr ⊢ |==> Own fmr0) :
  Own mr_src ⊢ |==> Own (ctx ⋅ fmr0 ⋅ mr_tgt).
Proof.
  etrans; eauto. iIntros "> [[CTX FMR] MRT]".
  iMod (FMR with "FMR") as "FMR"; iModIntro; iSplitR "MRT"; last done.
  iSplitR "FMR"; done.
Qed.
Local Hint Resolve own_upd_in_middle : core.

Definition ctx_sem `{Σ: GRA} (ctx : list Σ) : Σ :=
  [^(⋅) list] r ∈ ctx, r.

Definition ctx_set `{Σ: GRA} (my_tid : nat) (ctx : list Σ) (r : Σ) : list Σ :=
  <[my_tid := r]> ctx.

Definition ctx_add `{Σ: GRA} (my_tid : nat) (ctx : list Σ) (r : Σ) : list Σ :=
  ctx_set my_tid ctx ((or_else (ctx !! my_tid) ε) ⋅ r).

Lemma ctx_set_sem `{Σ: GRA} (my_tid : nat) ctx r r' (IN : my_tid < List.length ctx) :
  ctx_sem (ctx_set my_tid ctx (r ⋅ r')) ≡ ctx_sem (ctx_set my_tid ctx r) ⋅ r'.
Proof.
  unfold ctx_set. revert my_tid r r' IN.
  induction ctx; i; ss; try nia.
  destruct my_tid; s.
  { rewrite /ctx_sem; rewrite !big_opL_cons. rewrite -assoc (comm _ r') assoc; done. }
  { move: IHctx; rewrite /ctx_sem !big_opL_cons => IHctx; rewrite IHctx; last by lia.
    by rewrite assoc. }
Qed.

Lemma ctx_add_sem `{Σ: GRA} (my_tid : nat) ctx r (IN : my_tid < List.length ctx) :
  ctx_sem (ctx_add my_tid ctx r) ≡ ctx_sem ctx ⋅ r.
Proof.
  destruct (ctx !! my_tid) eqn:emy; cycle 1.
  { hexploit (lookup_lt_is_Some_2 ctx); eauto; rewrite emy; ss; intros []; clarify. }
  { by rewrite /ctx_add; rewrite emy; ss; rewrite ctx_set_sem //= /ctx_set list_insert_id; ss. }
Qed.

Lemma le_mine_in `{Σ: GRA} (my_tid : nat) (ctx0 ctx : list Σ)
    (CTXLE : le_mine eq my_tid ctx0 ctx)
    (IN : my_tid < List.length ctx0) :
  my_tid < List.length ctx.
Proof.
  destruct CTXLE.
  eapply lookup_lt_is_Some_2 in IN. rdes IN.
  eapply H0 in IN. des. subst.
  eapply lookup_lt_is_Some_1. eauto.
Qed.

Lemma ctx_set_le_others `{Σ: GRA} (my_tid : nat) ctx r :
  le_others my_tid ctx (ctx_set my_tid ctx r).
Proof.
  unfold ctx_set. r; esplits.
  - rewrite length_insert. eauto.
  - i. rewrite list_lookup_insert_ne; eauto.
Qed.

Lemma ctx_le_mine_sem `{Σ: GRA} (my_tid : nat) (w0 w1 : list Σ)
    (IN : my_tid < List.length w0)
    (LE : le_mine eq my_tid w0 w1) :
  ctx_sem w1 = ctx_sem (ctx_set my_tid w1 (or_else (w0 !! my_tid) ε)).
Proof.
  unfold ctx_sem, ctx_set.
  move w1 before Σ. revert_until w1.
  induction w1; i; eauto.
  destruct w0; ss; try nia.
  destruct LE.
  destruct my_tid; ss.
  - exploit H0; ss. i; des. inv x0. eauto.
  - erewrite IHw1; eauto; try nia.
    split; et. nia.
Qed.

Variant interp_inv `{Σ: GRA} (Ist: ist_type Σ) : list Σ -> nat * Any.t * Any.t -> Prop :=
| interp_inv_intro
    (ctx : list Σ) (mr_src mr_tgt : Σ) nths st_src st_tgt mr
    (WF : ✓ mr_src)
    (MRS : Own mr_src ⊢ |==> Own (ctx_sem ctx ⋅ mr ⋅ mr_tgt))
    (MR : Own mr ⊢ |==> Ist nths st_src st_tgt)
    (NODUPS : List.NoDup (List.map fst st_src))
    (NODUPT : List.NoDup (List.map fst st_tgt)) :
  interp_inv Ist ctx (nths, Any.pair (ModTr.alist_encode st_src) mr_src↑, Any.pair (ModTr.alist_encode st_tgt) mr_tgt↑).

(* Adequacy requires 'contextual = closed'*)
Lemma msim_adequacy
  `{Σ : GRA}
  (fl_src : alist (option string) (Any.t -> itree crisE Any.t))
  (fl_tgt : alist (option string) (Any.t -> itree crisE Any.t))
  (Ist : ist_type Σ)
  (my_tid : nat)
  (NODUPFS : List.NoDup (List.map fst fl_src))
  (NODUPFT : List.NoDup (List.map fst fl_tgt))
  (fl_src0 fl_tgt0 : alist (option string) (Any.t -> itree lmodE Any.t))
  (FLS : fl_src0 = List.map (fun '(s, f) => (s, ModTr.trans_ktree f)) fl_src)
  (FLT : fl_tgt0 = List.map (fun '(s, f) => (s, ModTr.trans_ktree f)) fl_tgt)
  ps pt nths st_src st_tgt itr_src itr_tgt
  RR
  (NODUPS : List.NoDup (List.map fst st_src))
  (NODUPT : List.NoDup (List.map fst st_tgt))
  (ctx0 ctx : list Σ) (mr_src mr_tgt fmr : Σ)
  (CTXLE : @le_mine Σ eq my_tid ctx0 ctx)
  (TID : my_tid < List.length ctx0)
  (TID' : my_tid < nths)
  (SIM : msim closed fl_src fl_tgt Ist (ist_with_eq RR) ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
  (WF : ✓ mr_src)
  (FMR : Own mr_src ⊢ |==> Own ((ctx_sem ctx) ⋅ fmr ⋅ mr_tgt))
  :
  lsim fl_src0 fl_tgt0 ε (interp_inv Ist) eq my_tid
    (interp_inv RR) ctx0 ps pt ctx nths
    (Any.pair (ModTr.alist_encode st_src) mr_src ↑, ModTr.trans itr_src)
    (Any.pair (ModTr.alist_encode st_tgt) mr_tgt ↑, ModTr.trans itr_tgt).
Proof.
  revert_until FLT. ginit. gcofix CIH. i.
  remember (st_src, itr_src). remember (st_tgt, itr_tgt).
  move SIM before FLT. revert_until SIM. punfold SIM.
  pattern ps, pt, nths, p, p0, fmr.
  eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
  assert (wffmr : ✓ fmr).
  { hexploit Own_wand_valid; eauto; intros wf.
    apply cmra_valid_op_l, cmra_valid_op_r in wf; ss.
  }
  exploit IN; i; try (subst sti_src sti_tgt; eauto; fail).
  des; clear IN.
  assert (wffmr0 : ✓ fmr0).
  { by eapply Own_wand_valid. }

  destruct x0; i; des.

  - clear CIH; clarify.
    step.
    econs; eauto.
    esplits; et; cycle 1.
    { eapply Own_pure_soundness; eauto.
      iIntros "H". iPoseProof (RET with "H") as "[EQ _]".
      iPoseProof (bupd_elim with "EQ") as "EQ"; done.
    }
    econs; et; cycle 1.
    { iIntros "H". iMod (x1 with "H") as "H"; iPoseProof (RET with "H") as "[_ H]"; ss. }

  - clarify; ired.
    hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
    guclo lflagC_spec; econs; try instantiate (1:=ctx_add my_tid ctx frame); eauto using ctx_set_le_others.
    step.
    { econs; eauto.
      { iIntros "H"; iMod (FMR with "H") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
        iMod (UPD with "FMR") as "[IST FRAME]".
        rewrite ctx_add_sem; eauto using le_mine_in; iModIntro; iSplitR "MRT"; last done;
          iSplitR "IST"; last done; iSplitR "FRAME"; done.
      }
      iIntros "H"; iModIntro; iApply Hist; done.
    }
    ired. inv WF0.
    guclo lflagC_spec; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
      eauto using ctx_set_le_others.
    eapply (K _ _ st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { instantiate (1:= or_else (ctx !! my_tid) ε).
      eapply le_mine_trans; first by ii; subst.
      { apply CTXLE. }
      { split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        ii; esplits; eauto; rewrite IN /ctx_set list_lookup_insert; ss; eauto.
        eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
      }
    }
    iIntros "H"; iMod (MRS with "H") as "[[CTX FMR] MRT]"; iSplitR "MRT"; last done.
    rewrite assoc; iSplitR "FMR"; last done.
    erewrite (ctx_le_mine_sem my_tid (ctx_add my_tid ctx frame) w1); eauto using le_mine_in; cycle 1.
    { rewrite /ctx_add length_insert; eauto using le_mine_in. }
    rewrite -ctx_set_sem; cycle 1.
    { eapply le_mine_in; eauto; rewrite length_insert; eauto using le_mine_in. }
    rewrite /ctx_add /ctx_set list_lookup_insert; eauto using le_mine_in.

  - clarify. step. ired. eapply K; eauto.

  - clarify. step; eauto.
    { instantiate (1:= ModTr.trans_ktree f). rewrite alist_find_map FUN. et. }

    rewrite /ModTr.trans_ktree.
    exploit (K _ _ st_src st_tgt _ _ _ _ _ _ mr_src mr_tgt); eauto.
    clear K CIH; intros K.

    match goal with [|- _ ?t _] => pattern t end.
    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - clarify. step; eauto.
    { instantiate (1:= ModTr.trans_ktree f). rewrite alist_find_map FUN. et. }

    rewrite /ModTr.trans_ktree.
    exploit (K _ _ st_src st_tgt _ _ _ _ _ _ mr_src mr_tgt); eauto.
    clear K CIH; intros K.

    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - clarify; steps; eapply K; eauto.
  - clarify; steps; eapply K; eauto.
  - clarify; steps; eapply K; eauto.
  - clarify; steps; eapply K; eauto.
  - clarify; steps; eapply K; eauto.
  - clarify; steps; eapply K; eauto.

  - clarify; steps.
    rewrite /ModTr.mput_kv; steps.
    rewrite Any.pair_split /= ModTr.alist_encode_decode; steps; eapply K; eauto.
    eapply alist_upd_nodup; eauto.

  - clarify; steps.
    rewrite /ModTr.mput_kv; steps.
    rewrite Any.pair_split /= ModTr.alist_encode_decode; steps; eapply K; eauto.
    eapply alist_upd_nodup; eauto.

  - clarify; steps.
    rewrite /ModTr.mget_kv; steps.
    rewrite Any.pair_split /= ModTr.alist_encode_decode; steps; eapply K; eauto.

  - clarify; steps.
    rewrite /ModTr.mget_kv; steps.
    rewrite Any.pair_split /= ModTr.alist_encode_decode; steps; eapply K; eauto.

  - clarify; steps.
    rewrite Red.Assume /ModTr.handle_Assume; steps.
    rewrite /ModTr.put_res; steps. des.
    apply Own_bupd_split in _ASSUME0. des.
    eapply (K (fmr0 ⋅ a1)); eauto.
    { iIntros "[FMR X]"; iMod (CUR with "FMR") as "FMR". iFrame.
      iModIntro. iApply _ASSUME1. eauto.
    }
    { rewrite _ASSUME0.
      iIntros "> [X MRS]". iPoseProof (_ASSUME2 with "MRS") as "MRS".
      iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iModIntro; iSplitR "MRT"; eauto.
      iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
    }
    { eauto. }

  - clarify; steps.
    rewrite Red.AssumeRes /ModTr.handle_AssumeRes /assume /ModTr.put_res.
    move FMR at bottom. move CUR at bottom.
    steps.
    rewrite !Own_op in FMR.
    eapply (K (fmr0 ⋅ r0)); eauto.
    { rewrite !Own_op CUR; iIntros "[> $ $] //". }
    { rewrite !Own_op FMR x1; iIntros "[$ > [[$ > $] $]] //". }


    (* assert (PRE' : Own ε ⊢ precise iP).
    { iIntros "_"; iApply PRE. }
    eapply Own_general_soundness in PRE'; rr in PRE'.
    rewrite seal_eq /= in PRE'.
    destruct PRE' as [_ PRE']; rr in PRE'.
    do 2 (rewrite seal_eq /= in PRE'; rr in PRE').
    destruct PRE' as [a PRE'].
    eapply Own_general_completeness in PRE'.
    (* eapply Own_bupd_split in CUR; et. i; des. *)
    (* rewrite /precise bi.intuitionistically_exist in CUR0. *)
    (* rewrite {1}/Own {1}seal_eq in CUR0. *)
    (* assert (Va1: ✓ a1).
    { eapply Own_wand_valid in wffmr0; et. rewrite CUR. iIntros "[H1 _]"; et. } *)
    (* eapply uPred.ownM_general_soundness in CUR0; et. *)
    (* rr in CUR0. rewrite seal_eq in CUR0. ss. des. *)
    (* eapply Own_general_completeness in CUR0.
    eapply own_core_completeness in CUR0; et. *)

    steps; et.
    { instantiate (1:=a).
      iPoseProof (PRE') as "P".
      iModIntro; iModIntro; iApply "P".
      iPoseProof (Own_unit) as "$".
    }
    { rewrite /ModTr.put_res; steps. eapply K; et; cycle 1.
      - rewrite ?Own_op FMR.
        iIntros "[A > [[C FMR] T]]".
        iCombine "A" "FMR" as "A".
        iFrame. done.
      - rewrite !Own_op x1 CUR.
        iIntros "(A & > > AC)". iFrame.
        iPoseProof (PRE' with "[]") as "[EQ _]".
        { iApply Own_unit. }
        iApply "EQ"; done.
    }
    ss. *)

  - clarify; steps.
    rewrite Red.Guarantee /ModTr.handle_Guarantee; steps.
    rewrite /ModTr.put_res; steps. des.
    hexploit (Own_bupd_split); eauto.
    { hexploit (Own_wand_valid _ _ FMR); eauto using cmra_valid_op_r. }
    intros [rP [frt [UPD [HP Hx]]]]; eapply (K (fmr0 ⋅ rP)); eauto.
    { iIntros "[FMR P]"; iPoseProof (HP with "P") as "P"; iMod (CUR with "FMR") as "FMR";
        iModIntro; iSplitL "P"; iFrame. }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]";
        iMod (UPD with "MRT") as "[P FRT]"; iMod (x1 with "FMR") as "FMR";
        iPoseProof (Hx with "FRT") as "X"; iModIntro;
        iSplitR "X"; [iSplitL "CTX"; [|iSplitL "FMR"]|]; iFrame.
    }

  - clarify; steps.
    hexploit (Own_bupd_split fmr0); eauto; intros [rP [rFMR [SPLIT [HP HFMR]]]].
    rewrite Red.Guarantee /ModTr.handle_Guarantee; steps.
    rewrite /ModTr.put_res.
    instantiate (1 := (ctx_sem ctx ⋅ rFMR ⋅ mr_tgt)).
    rewrite /guarantee; force_l; [split|].
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]".
      iSplitR "MRT"; eauto. iSplitL "CTX"; eauto.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]". iPoseProof (HP with "P") as "P".
      iSplitL "P"; eauto. iSplitR "MRT"; eauto. iSplitR "FMR"; eauto.
    }
    steps; eapply K; eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[_ FMR]"; iModIntro; iSplitR "MRT"; [iSplitL "CTX"|]; iFrame.
    }

  - clarify; steps.
    hexploit (Own_bupd_split fmr0); eauto; intros [rP [rFMR [SPLIT [HP HFMR]]]].
    rewrite Red.Assume /ModTr.handle_Assume; steps.
    rewrite /ModTr.get_res /ModTr.put_res; steps.
    instantiate (1 := rP ⋅ mr_tgt).
    rewrite /assume; force_r; [split|].
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[_ FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[RP _]"; iModIntro; iSplitL "RP"; iFrame.
    }
    { iIntros "(P & MRT)". iFrame. iApply HP. eauto. }
    steps.
    eapply K; eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[P FMR]";
        iModIntro; iSplitR "P MRT"; [iSplitR "FMR"; iFrame|]; iSplitL "P"; iFrame.
    }

  - clarify; steps.
    rewrite Red.AssumeRes /ModTr.handle_AssumeRes /assume /ModTr.get_res; steps.
    { eapply Own_wand_valid; [|apply WF].
      rewrite FMR !Own_op x1 CUR; iIntros "> [[_ > > [$ ?]] $] //".
    }
    { rewrite /ModTr.put_res; steps.
      hexploit Own_bupd_split; first apply CUR; eauto.
      intros [fmr1 [fmr2 [Hfmr [? Hfmr2]]]].
      eapply (K fmr2); eauto.
      { eapply Own_wand_valid; [iIntros "H"; iMod (Hfmr with "H") as "[_ $]"|]; ss. }
      { rewrite Hfmr2; iIntros "$ //". }
      { rewrite FMR !Own_op x1 Hfmr H.
        iIntros "> [[$ > > [$ $]] $] //".
      }
    }
    (* rename _GUARANTEE into G.
    assert (PRE : ⊢ precise iP).
    { iExists x. iPoseProof (G) as "G"; iModIntro; iSplitL.
      { iIntros "X"; iMod ("G") as "[G _]"; iApply "G"; done. }
      { iIntros "X"; iMod ("G") as "[_ G]"; iApply "G"; done. }
    }
    hexploit CUR; eauto; intros [cur1 [cur2 [Hcur [Hcur1 Hcur2]]]]%Own_bupd_split.
    (* hexploit (Own_bupd_split fmr0); eauto. intros [rP [rFMR [SPLIT [HP HFMR]]]]. *)

    rewrite /assume. steps.
    { eapply Own_wand_valid; [|eapply WF].
      rewrite FMR !Own_op x1 CUR //.
      iIntros "> [[_ > > [P _]] $]".
      iMod G as "#[_ G]"; iApply "G"; done.
    }
    rewrite /ModTr.put_res; steps.
    (* _force_r. *)
    
    (* eapply Own_bupd_split in G; cycle 1; i; des.
    { eapply Own_wand_valid in WF; et. rewrite FMR. iIntros ">[_ H]". et. }
    assert (Va1: ✓ a1).
    { eapply Own_wand_valid in WF; et.
      rewrite FMR !Own_op G. iIntros ">[_ >[H _]]". et. } *)
    (* eapply (own_core_completeness ε (⊢ |==> □ ((Own )))) in G; et. *)
    (* hexploit (K (x ⋅ mr_tgt)). clear K; i; des.
    { eapply Own_wand_valid in WF; et.
      rewrite FMR !Own_op x1 G. iIntros ">[[_ >?] >[? _]]". iFrame. et. }
    { rewrite !Own_op CUR -(cmra_core_l a1) Own_op G0.
      rewrite /precise bi.intuitionistically_exist.
      iIntros "[[H _] >F]". iFrame. et.
    }
    rename H0 into K.

    eapply Own_bupd_split in H; cycle 1; i; des.
    { clear K. eapply Own_wand_valid in WF; et.
      rewrite FMR !Own_op G x1. iIntros ">[[_ >?] [>? _]]". iFrame. et. }

    assert (VALID: ✓ (x ⋅ x0)).
    { clear K. eapply (Own_wand_valid mr_src); eauto.
      rewrite FMR !Own_op G G1 x1 -(cmra_core_l a1) Own_op G0.
      iIntros ">[[C >F] >[[[#PR1 #PR2] A] X]]". iFrame.
      iCombine "A F" as "H". rewrite H H0. iMod "H" as "[P F]".
      iApply "PR2"; et.
    }
    rewrite /assume /ModTr.get_res /ModTr.put_res; steps. *)

    eapply (K cur2); clear K; eauto.
    { eapply Own_wand_valid; [iIntros "H"; iMod (Hcur with "H") as "[_ $]"|]; ss. }
    { rewrite Hcur2; iIntros "$ //". }
    { rewrite FMR !Own_op x1 Hcur Hcur1.
      iIntros "> [[$ > > [P $]] $]".
      iMod G as "#[_ G]"; iApply "G"; done.
    }
    { done. } *)

  (* - clarify; steps.
    rewrite Red.AssumeRes /ModTr.handle_AssumeRes /guarantee /assume.
    set (_HIDE:=itreeV_itree) at 1. remember _HIDE as HIDE. subst _HIDE. guardH HeqHIDE.
    do 4 step. ired.
    unguard. subst HIDE.
    set (_HIDE:=Take) at 2. remember _HIDE as HIDE. subst _HIDE. guardH HeqHIDE.
    do 2 step. instantiate (1:= x).
    step. instantiate (1:= ctx_sem ctx ⋅ fmr ⋅ x0).
    step.
    { clear K. rewrite FMR !Own_op x2.
      iIntros ">[[C F] >[P X]]". iFrame. et. }
    step. unguard. subst HIDE. step.
    { eapply Own_wand_valid in x3; et. rewrite !Own_op.
      iIntros "[? [_ ?]]"; iFrame. et. }
    rewrite /ModTr.put_res.
    do 4 step.
    eapply K; et.
    rewrite !Own_op x1. iIntros "[? [[? >?] ?]]". iFrame. et. *)

  - clarify. step. ired. eapply K; eauto.
    { eapply le_mine_trans; eauto; first ii; subst; ss.
      split.
      { rewrite length_app. s. nia. }
      ii; esplits; ss; rewrite lookup_app_l; eauto using le_mine_in.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iModIntro; iSplitR "MRT"; [iSplitR "FMR"|]; iFrame.
      rewrite /ctx_sem big_opL_app /= ?right_id; eauto.
    }

  - clarify.
    hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
    guclo lflagC_spec; econs; try instantiate (1:=ctx_add my_tid ctx frame); eauto using ctx_set_le_others.
    step.
    { econs; eauto.
      { iIntros "H"; iMod (FMR with "H") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
        iMod (UPD with "FMR") as "[IST FRAME]".
        rewrite ctx_add_sem; eauto using le_mine_in; iModIntro; iSplitR "MRT"; last done;
          iSplitR "IST"; last done; iSplitR "FRAME"; done.
      }
      iIntros "H"; iModIntro; iApply Hist; done.
    }
    ired. inv WF0.
    guclo lflagC_spec; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
      eauto using ctx_set_le_others.
    eapply (K _ st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { eapply le_mine_trans; first by ii; subst.
      { apply CTXLE. }
      { instantiate (1:= or_else (ctx !! my_tid) ε).
        split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        ii; esplits; eauto; rewrite IN /ctx_set list_lookup_insert; ss; eauto.
        eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
      }
    }
    iIntros "H"; iMod (MRS with "H") as "[[CTX FMR] MRT]"; iSplitR "MRT"; last done.
    rewrite assoc; iSplitR "FMR"; last done.
    erewrite (ctx_le_mine_sem my_tid (ctx_add my_tid ctx frame) w1); eauto using le_mine_in; cycle 1.
    { rewrite /ctx_add length_insert; eauto using le_mine_in. }
    rewrite -ctx_set_sem; cycle 1.
    { eapply le_mine_in; eauto; rewrite length_insert; eauto using le_mine_in. }
    rewrite /ctx_add /ctx_set list_lookup_insert; eauto using le_mine_in.

  - clarify. prep. guclo lsim_indC_spec. econs 16.
    rewrite alist_find_map FUN. et.

  - clarify. prep. guclo lsim_indC_spec. econs 17.
    rewrite alist_find_map FUN. et.

  - clarify. pclearbot. gstep; econs; econs; eauto; cycle 1.
    { gfinal; left; eapply CIH; eauto. }
    by apply le_others_refl.
Qed.

(* Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto. *)

(* Lemma _msim_close `{Σ: GRA} fls flt Ist: *)
(*   @_msim _ fls flt Ist <10= @_msim _ closed fls flt Ist. *)
(* Proof. *)
(*   i. ss.  *)
(*   eapply _msim_tarski; eauto. i.  *)
(*   econs. ii. exploit IN; eauto. i. des. *)
(*   esplits; eauto. clear IN. *)
(*   destruct x10; ss; try by econs; eauto. *)
(* Qed. *)

(* Lemma msim_close `{Σ: GRA} *)
(*   fl_src fl_tgt Ist *)
(*   ps pt nths st_src st_tgt itr_src itr_tgt fmr *)
(*   (SIM: msim_body open fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr) *)
(* : *)
(*   msim_body closed fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr. *)
(* Proof. *)
(*   ginit. s. revert_until Ist. gcofix CIH. i. *)
(*   remember (st_src, itr_src). remember (st_tgt, itr_tgt). *)
(*   move SIM before CIH. revert_until SIM. punfold SIM. *)
(*   pattern ps, pt, nths, p, p0, fmr. *)
(*   eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr. *)
(*   guclo msim_wfC_spec. econs. i. *)
(*   guclo msim_nodupC_spec. econs. i. *)
(*   exploit IN; i; des; eauto. clear IN. *)
(*   destruct x0; i; des; try by inv Heqp; try inv Heqp0; clarify; mstep. *)
(*   { guclo msimC_spec. econs. econs; et. econs; et. i. *)
(*     hexploit K; et. i; des. esplits; et. } *)
(*   pclearbot. gstep. econs. ii. esplits; et. econs; et. *)
(*   gfinal. right. eapply paco9_mon_bot; eauto using _msim_close. *)
(* Qed.  *)

From CRIS.modules Require Import Mod ModTr.
From CRIS.simulations.msim Require Import MSimCommon MSim.
From CRIS.simulations.lsim Require Import LSim LSimTactics.
From iris.proofmode Require Import proofmode.

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

Variant interp_inv `{Σ : GRA} (Ist : ist_type Σ) :
    list Σ → lstateT * lstateT → Prop :=
| interp_inv_intro
    (ctx : list Σ) (mr_src mr_tgt : Σ) st_src st_tgt mr
    (WF : ✓ mr_src)
    (MRS : Own mr_src ⊢ |==> Own (ctx_sem ctx ⋅ mr ⋅ mr_tgt))
    (MR : Own mr ⊢ |==> Ist st_src st_tgt)
    (NODUPS : map_Forall (const is_Some) st_src)
    (NODUPT : map_Forall (const is_Some) st_tgt)
    :
  interp_inv Ist ctx
    ((st_src, mr_src↑), (st_tgt, mr_tgt↑)).

Definition IstWorld `{Σ : GRA} (Ist : ist_type Σ) : LWorld :=
  {|
    world := Σ;
    winit := ε;
    wf := interp_inv Ist;
    wle := eq;
    wle_refl := λ _, eq_refl;
    wle_trans := λ x y z, @eq_trans Σ x y z
  |}.

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

Lemma le_mine_in `{Σ: GRA} {Ist : ist_type Σ}
    (my_tid : nat) (ctx0 ctx : list Σ)
    (CTXLE : le_mine (IstWorld Ist) my_tid ctx0 ctx)
    (IN : my_tid < List.length ctx0) :
  my_tid < List.length ctx.
Proof.
  destruct CTXLE.
  eapply lookup_lt_is_Some_2 in IN. rdes IN.
  eapply H0 in IN. des. subst.
  eapply lookup_lt_is_Some_1. eauto.
Qed.

Lemma ctx_set_le_others `{Σ: GRA} {Ist : ist_type Σ}
    (my_tid : nat) ctx r :
  le_others (IstWorld Ist) my_tid ctx (ctx_set my_tid ctx r).
Proof.
  unfold ctx_set. r; esplits.
  - rewrite length_insert. eauto.
  - i. rewrite list_lookup_insert_ne; eauto.
Qed.

Lemma ctx_le_mine_sem `{Σ: GRA} {Ist : ist_type Σ}
    (my_tid : nat) (w0 w1 : list Σ)
    (IN : my_tid < List.length w0)
    (LE : le_mine (IstWorld Ist) my_tid w0 w1) :
  ctx_sem w1 = ctx_sem (ctx_set my_tid w1 (or_else (w0 !! my_tid) ε)).
Proof.
  unfold ctx_sem, ctx_set.
  move w1 before Σ. revert_until w1.
  induction w1; i; eauto.
  destruct w0; ss; try nia.
  destruct LE.
  destruct my_tid; ss.
  - exploit H0; ss. i; des. inv x0. eauto.
  - erewrite (IHw1 Ist my_tid w0); eauto; try nia.
    unfold le_mine; simpl.
    split; first nia.
    intros wi Hwi. eapply H0 in Hwi as [wi' [Hwi ->]].
    exists wi'. split; done.
Qed.

(* Adequacy requires 'contextual = closed'*)
Lemma msim_adequacy
    `{Σ : GRA}
    (fl_src fl_tgt : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : ist_type Σ)
    (my_tid : nat)
    (fl_src0 fl_tgt0 : gmap fname (Any.t → itree lmodE Any.t))
    (FLS : fl_src0 = ModTr.trans_fnsem <$> (omap id fl_src))
    (FLT : fl_tgt0 = ModTr.trans_fnsem <$> (omap id fl_tgt))
    ps pt st_src st_tgt itr_src itr_tgt
    RR
    (ctx0 ctx : list Σ) (mr_src mr_tgt fmr : Σ)

    (NODUPFS : map_Forall (const is_Some) fl_src)
    (NODUPFT : map_Forall (const is_Some) fl_tgt)
    (NODUPS : map_Forall (const is_Some) st_src)
    (NODUPT : map_Forall (const is_Some) st_tgt)
    (CTXLE : le_mine (IstWorld Ist) my_tid ctx0 ctx)
    (TID : my_tid < List.length ctx0)
    (SIM : msim closed fl_src fl_tgt Ist (ist_with_eq RR) ps pt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
    (WF : ✓ mr_src)
    (FMR : Own mr_src ⊢ |==> Own ((ctx_sem ctx) ⋅ fmr ⋅ mr_tgt)) :
  lsim fl_src0 fl_tgt0 (IstWorld Ist) my_tid
    (interp_inv RR) ctx0 ps pt ctx
    ((st_src, mr_src ↑), ModTr.trans itr_src)
    ((st_tgt, mr_tgt ↑), ModTr.trans itr_tgt).
Proof.
  revert_until FLT. ginit. gcofix CIH. i.
  remember (st_src, itr_src). remember (st_tgt, itr_tgt).
  move SIM before FLT. revert_until SIM. punfold SIM.
  pattern ps, pt, p, p0, fmr.
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

  - (* Ret *)
    clear CIH; clarify.
    step.
    econs; eauto.
    esplits; et; cycle 1.
    { eapply Own_pure_soundness; eauto.
      iIntros "H". iPoseProof (RET with "H") as "[EQ _]".
      iPoseProof (bupd_elim with "EQ") as "EQ"; done.
    }
    econs; et; cycle 1.
    { iIntros "H". iMod (x1 with "H") as "H"; iPoseProof (RET with "H") as "[_ H]"; ss. }

  - (* Call *)
    clarify; ired.
    hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
    guclo_lflagC; econs; try instantiate (1:=ctx_add my_tid ctx frame);
      eauto using ctx_set_le_others.
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
    guclo_lflagC; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
      eauto using ctx_set_le_others.
    eapply (K _ st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { instantiate (1:= default ε (ctx !! my_tid)).
      eapply (le_mine_trans (IstWorld Ist) my_tid).
      { apply CTXLE. }
      { split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        intros ? Hlookup.
        rewrite Hlookup /=.
        rewrite /ctx_set list_lookup_insert; eauto.
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

  - (* IO *)
    clarify. step. ired. eapply K; eauto.

  - (* inline src *)
    clarify. step; eauto.
    { instantiate (1:= ModTr.trans_fnsem f).
      rewrite lookup_fmap /= lookup_omap FUN //.
    }

    rewrite /ModTr.trans_fnsem.
    exploit (K _ _ st_src st_tgt _ _ _ _ mr_src mr_tgt); eauto.
    clear K CIH; intros K.

    match goal with [|- _ ?t _] => pattern t end.
    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - (* inline tgt *)
    clarify. step; eauto.
    { instantiate (1:= ModTr.trans_fnsem f).
      rewrite lookup_fmap /= lookup_omap FUN //.
    }

    rewrite /ModTr.trans_fnsem.
    exploit (K _ _ st_src st_tgt _ _ _ _ mr_src mr_tgt); eauto.
    clear K CIH; intros K.

    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - (* Tau src *)
    clarify; steps; eapply K; eauto.
  - (* Tau tgt *)
    clarify; steps; eapply K; eauto.
  - (* Take src *)
    clarify; steps; eapply K; eauto.
  - (* Choose tgt *)
    clarify; steps; eapply K; eauto.
  - (* Choose src *)
    clarify; steps; eapply K; eauto.
  - (* Take tgt *)
    clarify; steps; eapply K; eauto.

  - (* SPut src *)
    clarify; steps; eapply K; eauto.
    apply map_Forall_insert_2; ss.

  - (* SPut tgt *)
    clarify; steps; eapply K; eauto.
    apply map_Forall_insert_2; ss.

  - (* SGet src *)
    clarify; steps; eapply K; eauto.

  - (* SGet tgt *)
    clarify; steps; eapply K; eauto.

  - (* Assume src *)
    clarify; steps.
    rewrite Red.Assume /ModTr.handle_Assume /assume; steps.
    rewrite /ModTr.put_res; steps. des.
    apply Own_bupd_split in x2; des.
    eapply (K (fmr0 ⋅ a1)); eauto.
    { iIntros "[FMR X]"; iMod (CUR with "FMR") as "FMR". iFrame.
      iModIntro. iApply x3. eauto.
    }
    { rewrite x2.
      iIntros "> [X MRS]". iPoseProof (x4 with "MRS") as "MRS".
      iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iModIntro; iSplitR "MRT"; eauto.
      iSplitL "CTX"; eauto. iSplitL "FMR"; eauto.
    }
    { eauto. }

  - (* Assume tgt *)
    clarify; steps.
    hexploit (Own_bupd_split fmr0); eauto; intros [rP [rFMR [SPLIT [HP HFMR]]]].
    rewrite Red.Assume /ModTr.handle_Assume /assume; steps.
    instantiate (1 := rP ⋅ mr_tgt).
    (* rewrite /assume; force_r; [split|]. *)
    split.
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[_ FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[RP _]"; iModIntro; iSplitL "RP"; iFrame.
    }
    { iIntros "(P & MRT)". iFrame. iApply HP. eauto. }
    rewrite /ModTr.get_res /ModTr.put_res; steps.
    steps.
    eapply K; eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[P FMR]";
        iModIntro; iSplitR "P MRT"; [iSplitR "FMR"; iFrame|]; iSplitL "P"; iFrame.
    }

  - (* AssumeRes src *)
    clarify; steps.
    rewrite Red.AssumeRes /ModTr.handle_AssumeRes /assume /ModTr.put_res.
    move FMR at bottom. move CUR at bottom.
    steps.
    rewrite !Own_op in FMR.
    eapply (K (fmr0 ⋅ r0)); eauto.
    { rewrite !Own_op CUR; iIntros "[> $ $] //". }
    { rewrite !Own_op FMR x1; iIntros "[$ > [[$ > $] $]] //". }

  - (* AssumeRes tgt *)
    clarify; steps.
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

  - (* Guarantee src *)
    clarify; steps.
    hexploit (Own_bupd_split fmr0); eauto; intros [rP [rFMR [SPLIT [HP HFMR]]]].
    rewrite Red.Guarantee /ModTr.handle_Guarantee /guarantee; steps.
    instantiate (1 := (ctx_sem ctx ⋅ rFMR ⋅ mr_tgt)).
    (* rewrite /guarantee; force_l; [split|]. *)
    split.
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]".
      iSplitR "MRT"; eauto. iSplitL "CTX"; eauto.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]". iPoseProof (HP with "P") as "P".
      iSplitL "P"; eauto. iSplitR "MRT"; eauto. iSplitR "FMR"; eauto.
    }
    rewrite /ModTr.put_res. steps. eapply K; eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[_ FMR]"; iModIntro; iSplitR "MRT"; [iSplitL "CTX"|]; iFrame.
    }

  - (* Guarantee tgt *)
    clarify; steps.
    rewrite Red.Guarantee /ModTr.handle_Guarantee /guarantee; steps.
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

  - (* Spawn *)
    clarify. step. ired. eapply K; eauto.
    { eapply (le_mine_trans (IstWorld Ist) my_tid); eauto; ss.
      split.
      { rewrite length_app. s. nia. }
      ii; esplits; ss; rewrite lookup_app_l; eauto using le_mine_in.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
        iModIntro; iSplitR "MRT"; [iSplitR "FMR"|]; iFrame.
      rewrite /ctx_sem big_opL_app /= ?right_id; eauto.
    }

  - (* Yield *)
    clarify.
    hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
    guclo_lflagC; econs; try instantiate (1:=ctx_add my_tid ctx frame); eauto using ctx_set_le_others.
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
    guclo_lflagC; econs; try instantiate (1:=ctx_set w1 (default ε (ctx !! my_tid)));
      eauto using ctx_set_le_others.
    eapply (K st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { eapply (le_mine_trans (IstWorld Ist) my_tid).
      { apply CTXLE. }
      { instantiate (1:= default ε (ctx !! my_tid)).
        split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        intros ? Hlookup.
        rewrite Hlookup /=.
        rewrite /ctx_set list_lookup_insert; eauto.
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

  - (* GetTid *)
    clarify. step. eapply K; eauto.

  - (* Call none *)
    clarify. prep. guclo lsim_indC_spec. econs 17.
    rewrite lookup_fmap lookup_omap; destruct (_ !! _); ss; clarify.

  - (* Spawn none *)
    clarify. prep. guclo lsim_indC_spec. econs 18.
    rewrite lookup_fmap lookup_omap; destruct (_ !! _); ss; clarify.

  - (* progress *)
    clarify. pclearbot. gstep; econs; econs; eauto; cycle 1.
    { gfinal; left; eapply CIH; eauto. }
    by apply le_others_refl.
Qed.

Require Import Common.

Require Import HMod.
Require Import HPSim ModSim ModSimTactics.

Section HPSIM_ADEQUACY. 
  Context `{Σ : GRA}.
  Notation iProp := (iProp Σ).

  Variable contextual: contextuality.
  Variable fl_src : alist string (Any.t -> itree hmodE Any.t).
  Variable fl_tgt : alist string (Any.t -> itree hmodE Any.t).
  Variable Ist : nat -> alist key Any.t -> alist key Any.t -> iProp.
  Variable my_tid : nat.

  (*** Used only in hpsim_adequacy. ***)
  Lemma own_upd_in_middle mr_src mr_tgt ctx fmr fmr0
      (UPD : Own mr_src ⊢ |==> Own (ctx ⋅ fmr ⋅ mr_tgt))
      (FMR : Own fmr ⊢ |==> Own fmr0) :
    Own mr_src ⊢ |==> Own (ctx ⋅ fmr0 ⋅ mr_tgt).
  Proof.
    etrans; eauto. iIntros "> [[CTX FMR] MRT]".
    iMod (FMR with "FMR") as "FMR"; iModIntro; iSplitR "MRT"; last done.
    iSplitR "FMR"; done.
  Qed.
  Local Hint Resolve own_upd_in_middle : core.

  Definition ctx_sem (ctx : list Σ) : Σ :=
    [^(⋅) list] r ∈ ctx, r.

  Definition ctx_set (ctx : list Σ) (r : Σ) : list Σ :=
    <[my_tid := r]> ctx.
  
  Definition ctx_add (ctx : list Σ) (r : Σ) : list Σ :=
    ctx_set ctx ((or_else (ctx !! my_tid) ε) ⋅ r).

  Lemma ctx_set_sem ctx r r' (IN : my_tid < List.length ctx) :
    ctx_sem (ctx_set ctx (r ⋅ r')) ≡ ctx_sem (ctx_set ctx r) ⋅ r'.
  Proof.
    unfold ctx_set. revert my_tid r r' IN.
    induction ctx; i; ss; try nia.
    destruct my_tid; s.
    { rewrite /ctx_sem; rewrite !big_opL_cons. rewrite -assoc (comm _ r') assoc; done. }
    { move: IHctx; rewrite /ctx_sem !big_opL_cons => IHctx; rewrite IHctx; last by lia.
      by rewrite assoc. }
  Qed.
  
  Lemma ctx_add_sem ctx r (IN : my_tid < List.length ctx) :
    ctx_sem (ctx_add ctx r) ≡ ctx_sem ctx ⋅ r.
  Proof.
    destruct (ctx !! my_tid) eqn:emy; cycle 1.
    { hexploit (lookup_lt_is_Some_2 ctx); eauto; rewrite emy; ss; intros []; clarify. }
    { by rewrite /ctx_add; rewrite emy; ss; rewrite ctx_set_sem //= /ctx_set list_insert_id; ss. }
  Qed.

  Lemma le_mine_in (ctx0 ctx : list Σ)
      (CTXLE : le_mine eq my_tid ctx0 ctx)
      (IN : my_tid < List.length ctx0) :
    my_tid < List.length ctx.
  Proof.
    unfold le_mine in *.
    eapply lookup_lt_is_Some_2 in IN. rdes IN.
    eapply CTXLE in IN. des. subst.
    eapply lookup_lt_is_Some_1. eauto.
  Qed.

  Lemma ctx_set_le_others ctx r :
    le_others my_tid ctx (ctx_set ctx r).
  Proof.
    unfold ctx_set. r; esplits.
    - rewrite length_insert. eauto.
    - i. rewrite list_lookup_insert_ne; eauto.
  Qed.

  Lemma ctx_le_mine_sem (w0 w1 : list Σ)
      (IN : my_tid < List.length w0)
      (LE : le_mine eq my_tid w0 w1) :
    ctx_sem w1 = ctx_sem (ctx_set w1 (or_else (w0 !! my_tid) ε)).
  Proof.
    unfold ctx_sem, ctx_set.
    move w1 before Ist. revert_until w1.
    induction w1; i; eauto.
    destruct w0; ss; try nia.
    destruct my_tid; ss.
    - exploit LE; ss. i; des. inv x0. eauto.
    - erewrite IHw1; eauto. nia.
  Qed.

  Variant interp_inv : list Σ -> nat * Any.t * Any.t -> Prop :=
  | interp_inv_intro
      (ctx : list Σ) (mr_src mr_tgt : Σ) nths st_src st_tgt mr
      (WF : ✓ mr_src)
      (MRS : Own mr_src ⊢ |==> Own (ctx_sem ctx ⋅ mr ⋅ mr_tgt))
      (MR : Own mr ⊢ |==> Ist nths st_src st_tgt)
      (NODUPS : List.NoDup (List.map fst st_src))
      (NODUPT : List.NoDup (List.map fst st_tgt)) :
    interp_inv ctx (nths, Any.pair (alist_encode st_src) mr_src↑, Any.pair (alist_encode st_tgt) mr_tgt↑).

  (* Adequacy requires 'contextual = closed'*)
  Lemma hpsim_adequacy
      (NODUPFS : List.NoDup (List.map fst fl_src))
      (NODUPFT : List.NoDup (List.map fst fl_tgt))
      (fl_src0 fl_tgt0 : alist string (Any.t -> itree modE Any.t))
      (FLS : fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
      (FLT : fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
      ps pt nths st_src st_tgt itr_src itr_tgt
      (NODUPS : List.NoDup (List.map fst st_src))
      (NODUPT : List.NoDup (List.map fst st_tgt))
      (ctx0 ctx : list Σ) (mr_src mr_tgt fmr : Σ)
      (CTXLE : @le_mine Σ eq my_tid ctx0 ctx)
      (TID : my_tid < List.length ctx0)
      (SIM : hpsim_body closed fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
      (WF : ✓ mr_src)
      (FMR : Own mr_src ⊢ |==> Own ((ctx_sem ctx) ⋅ fmr ⋅ mr_tgt)) :
    @sim_itree fl_src0 fl_tgt0 Σ ε interp_inv eq my_tid ctx0 ps pt ctx nths
      (Any.pair (alist_encode st_src) mr_src↑, interp_hp itr_src)
      (Any.pair (alist_encode st_tgt) mr_tgt↑, interp_hp itr_tgt).
  Proof.
    exploit SIM; eauto; clear SIM; intros SIM.
    revert_until FLT. ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before FLT. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    assert (wffmr : ✓ fmr).
    { hexploit Own_wand_valid; eauto; intros wf.
      apply cmra_valid_op_l, cmra_valid_op_r in wf; ss.
    }
    exploit IN; i; des; eauto; clear IN.
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
    - clarify; prep.
      hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
      guclo lflagC_spec; econs; try instantiate (1:=ctx_add ctx frame); eauto using ctx_set_le_others.
      step.
      { econs; eauto.
        { iIntros "H"; iMod (FMR with "H") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
          iMod (UPD with "FMR") as "[IST FRAME]".
          rewrite ctx_add_sem; eauto using le_mine_in; iModIntro; iSplitR "MRT"; last done;
            iSplitR "IST"; last done; iSplitR "FRAME"; done.
        }
        iIntros "H"; iModIntro; iApply Hist; done.
      }
      do 2 step; prep.
      inv WF0.
      guclo lflagC_spec; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
        eauto using ctx_set_le_others.
      eapply (K _ _ st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto.
      { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
      { eapply le_mine_trans; first by ii; subst.
        { apply CTXLE. }
        { ii; esplits; eauto; rewrite IN /ctx_set list_lookup_insert; ss; eauto.
          eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
        }
      }
      iIntros "H"; iMod (MRS with "H") as "[[CTX FMR] MRT]"; iSplitR "MRT"; last done.
      rewrite assoc; iSplitR "FMR"; last done.
      erewrite (ctx_le_mine_sem (ctx_add ctx frame) w1); eauto using le_mine_in; cycle 1.
      { rewrite /ctx_add length_insert; eauto using le_mine_in. }
      rewrite -ctx_set_sem; cycle 1.
      { eapply le_mine_in; eauto; rewrite length_insert; eauto using le_mine_in. }
      rewrite /ctx_add /ctx_set list_lookup_insert; eauto using le_mine_in.
    - clarify. do 3 step; prep. eapply K; eauto.
    - clarify. step; eauto.
      { instantiate (1:= interp_hp_fun f). rewrite alist_find_map FUN. et. }

      rewrite /interp_hp_fun.
      exploit (K _ _ st_src st_tgt _ _ _ _ _ _ mr_src mr_tgt); eauto.
      clear K CIH; intros K.

      match goal with [|- _ ?t _] => pattern t end.
      eapply eq_ind; eauto.
      rewrite ?interp_hp_bind bind_bind.
      repeat f_equal. extensionalities x.
      grind. rewrite !interp_hp_tau ?bind_tau. repeat f_equal. rewrite interp_hp_ret; grind.
    - clarify. step; eauto.
      { instantiate (1:= interp_hp_fun f). rewrite alist_find_map FUN. et. }

      rewrite /interp_hp_fun.
      exploit (K _ _ st_src st_tgt _ _ _ _ _ _ mr_src mr_tgt); eauto.
      clear K CIH; intros K.

      eapply eq_ind; eauto.
      rewrite ?interp_hp_bind bind_bind.
      repeat f_equal. extensionalities x.
      grind. rewrite !interp_hp_tau ?bind_tau. repeat f_equal. rewrite interp_hp_ret; grind.
    - clarify; steps; eapply K; eauto.
    - clarify; steps; eapply K; eauto.
    - clarify; steps; eapply K; eauto.
    - clarify; steps; eapply K; eauto.
    - clarify; steps; eapply K; eauto.
    - clarify; steps; eapply K; eauto.
    - clarify; steps.
      rewrite /mput_kv; steps.
      rewrite Any.pair_split /= alist_encode_decode; steps; eapply K; eauto.
      eapply alist_upd_nodup; eauto.
    - clarify; steps.
      rewrite /mput_kv; steps.
      rewrite Any.pair_split /= alist_encode_decode; steps; eapply K; eauto.
      eapply alist_upd_nodup; eauto.
    - clarify; steps.
      rewrite /mget_kv; steps.
      rewrite Any.pair_split /= alist_encode_decode; steps; eapply K; eauto.
    - clarify; steps.
      rewrite /mget_kv; steps.
      rewrite Any.pair_split /= alist_encode_decode; steps; eapply K; eauto.
    - clarify; steps.
      rewrite interp_hp_Assume /handle_Assume; steps.
      rewrite /get_res /put_res; steps. des.
      apply bi.wand_entails, Own_bupd_split in _ASSUME0. des.
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
      rewrite interp_hp_Guarantee /handle_Guarantee; steps.
      rewrite /get_res /put_res; steps. des.
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
      rewrite interp_hp_Guarantee /handle_Guarantee; steps.
      rewrite /get_res /put_res; steps.
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
      rewrite interp_hp_Assume /handle_Assume; steps.
      rewrite /get_res /put_res; steps.
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
      rewrite interp_hp_spawn; do 3 step; prep.
      eapply K; eauto.
      { eapply le_mine_trans; eauto; first ii; subst; ss.
        ii; esplits; ss; rewrite lookup_app_l; eauto using le_mine_in.
      }
      { iIntros "MRS"; iMod (FMR with "MRS") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR";
          iModIntro; iSplitR "MRT"; [iSplitR "FMR"|]; iFrame.
        rewrite /ctx_sem big_opL_app /= ?right_id; eauto.
      }
    - clarify; prep.
      hexploit (Own_bupd_split fmr0); eauto; intros [ist [frame [UPD [Hist Hframe]]]].
      guclo lflagC_spec; econs; try instantiate (1:=ctx_add ctx frame); eauto using ctx_set_le_others.
      step.
      { econs; eauto.
        { iIntros "H"; iMod (FMR with "H") as "[[CTX FMR] MRT]"; iMod (x1 with "FMR") as "FMR".
          iMod (UPD with "FMR") as "[IST FRAME]".
          rewrite ctx_add_sem; eauto using le_mine_in; iModIntro; iSplitR "MRT"; last done;
            iSplitR "IST"; last done; iSplitR "FRAME"; done.
        }
        iIntros "H"; iModIntro; iApply Hist; done.
      }
      do 2 step; prep.
      inv WF0.
      guclo lflagC_spec; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
        eauto using ctx_set_le_others.
      eapply (K _ st_src1 st_tgt1) with (fmr0:=(frame ⋅ mr)); eauto.
      { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
      { eapply le_mine_trans; first by ii; subst.
        { apply CTXLE. }
        { ii; esplits; eauto; rewrite IN /ctx_set list_lookup_insert; ss; eauto.
          eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
        }
      }
      iIntros "H"; iMod (MRS with "H") as "[[CTX FMR] MRT]"; iSplitR "MRT"; last done.
      rewrite assoc; iSplitR "FMR"; last done.
      erewrite (ctx_le_mine_sem (ctx_add ctx frame) w1); eauto using le_mine_in; cycle 1.
      { rewrite /ctx_add length_insert; eauto using le_mine_in. }
      rewrite -ctx_set_sem; cycle 1.
      { eapply le_mine_in; eauto; rewrite length_insert; eauto using le_mine_in. }
      rewrite /ctx_add /ctx_set list_lookup_insert; eauto using le_mine_in.
    - clarify. prep. guclo sim_itree_indC_spec. econs 16.
      { rewrite alist_find_map FUN. et. }
      rewrite /interp_hp_fun.
      exploit (K _ _ st_src st_tgt _ _ _ _ _ _ mr_src mr_tgt); eauto.
      clear K CIH; intros K.
      eapply eq_ind; eauto.
      rewrite interp_hp_bind.
      repeat f_equal. 
      { rewrite interp_hp_triggerNB. eauto. }
      extensionalities x. grind. rewrite !interp_hp_tau. eauto.
    - clarify. pclearbot. gstep; econs; econs; eauto; cycle 1.
      { gfinal; left; eapply CIH; eauto.
        { ginit; guclo hpsim_updateC_spec; econs; ii; esplits; eauto.
          by gfinal; right.
        }
      }
      by apply le_others_refl.
  Qed.
End HPSIM_ADEQUACY.

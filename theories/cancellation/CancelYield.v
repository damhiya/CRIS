Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma list_lookup_exists {A} (l: list A) n (LT: n < length l) :
  ∃ x, l !! n = Some x.
Proof.
  gen n. induction l; ss; [nia|]; i.
  destruct n; [esplits; eauto|].
  eapply Nat.succ_lt_mono in LT. hexploit IHl; eauto.
Qed.

Lemma cancel_yield `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp tid :
  CANCEL_GOAL md sp (NativeYieldE tid) (HoareYieldE tid).
Proof.
  r; i. subst.
  ziter_l; ziter_r. rewrite x0 x1 /=. zstep_l.
  zstep_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ired.
  ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

  des.
  assert (EQ: x = cid).
  { eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S"; iPoseProof (RS with "S") as ">[_ [R [TA _]]]".
    iPoseProof (x5 with "R") as ">[[T _] _]".
    iApply (TidToken_agree with "T"); iFrame. }
  subst.

  assert (RS0: Own r_s ⊢
                 |==> (([∗ list] i ∈ rs_diff, Own i) ∗ TIDAUTH tid ∗ YIELDAUTH (length rs_diff)) ∗
                 ((TID tid ∗ YIELD tid ∗ winv (⊤, ⊤)) ∗ Own x3)).
  { rewrite RS x5. iIntros ">[$ [>[[T [$ $]] $] [TA $]]]".
  iApply (TidToken_upd with "[TA T]"); iFrame. }
  hexploit (Own_bupd_split); eauto.
  intros [r_t1 [r_t2 [Hr_t1 [Hr_t2 Hr_t3]]]].

  assert (TVALID: ✓ r_t2).
  { eapply Own_wand_valid with (a1:=r_s); eauto.
    rewrite Hr_t1. iIntros ">[_ $]"; eauto. }

  destruct (decide (tid < length rs_diff)); cycle 1.
  {
    ziter_l. destruct (<[cid:=_]> srcs !! tid) eqn:FIND.
    { eapply lookup_lt_Some in FIND. rewrite length_insert in FIND. nia. }
    { zstep_l. zstep_l. }
  }
  destruct (decide (tid = cid)); subst.
  {
    ziter_l. zstep_l. ziter_r. zstep_r. ziter_r. zstep_r. ired.
    ziter_r. zstep_r.
    exists r_t2. zstep_r. ziter_r. zstep_r. unshelve eexists; ired.
    { des; split; eauto. rewrite Hr_t3. eapply bupd_intro. }
    zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
    eapply KEY with (r_diff:=ε); eauto.
    { rewrite length_insert list_insert_id //.
      iIntros "S". iPoseProof (Hr_t1 with "S") as ">[S $]"; iStopProof.
      rewrite Hr_t2. eapply bupd_intro. }
    { eapply thread_rel_body; eauto. eapply KTR. }
  }
  { do 2 dup l. rename l into SRC, l0 into TGT, l1 into RES.
    rewrite EQLEN2 in SRC. rewrite EQLEN2 EQLEN in TGT.
    dup SRC; dup TGT; dup RES.
    eapply list_lookup_exists in SRC, TGT, RES; des.
    hexploit REL; eauto; intros RELTID. inv RELTID.
    { (* first execution *)
      ziter_l; ziter_r. rewrite !list_lookup_insert_ne // SRC TGT /=.
      zstep_l. ziter_l. zstep_l.
      zstep_r. exists tid. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ired.
      ziter_r. zstep_r. exists r_t2. zstep_r.
      ziter_r. zstep_r. unshelve eexists; ired.
      { split; eauto. rewrite Hr_t3. eapply bupd_intro. }
      zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. exists x8. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. exists varg. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. exists (x7 ⋅ r_t2). zstep_r.
      ziter_r. zstep_r. unshelve eexists; ired.
      { split; eauto.
        { eapply Own_wand_valid with (a1:=r_s); eauto.
          rewrite Hr_t1 Hr_t2 big_sepL_lookup_acc // Own_op.
          iIntros ">[[[$ _] _] $]"; eauto.
        }
        rewrite Own_op H4. iIntros "[>$ $]"; eauto.
      }
      zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r.
      gstep. econs. econs; try exact smj_lt_mid_top.
      gbase. eapply CIH with (rs_diff:=<[tid:=ε]>rs_diff); eauto.
      { r. esplits; try rewrite !length_insert //.
        ii. destruct (decide (tid = i)); subst.
        {
          rewrite list_lookup_insert ?length_insert // in H1.
          rewrite list_lookup_insert ?length_insert // in H2.
          rewrite list_lookup_insert ?length_insert // in H3.
          des_ifs. econs; [..|rewrite interpV_bind //]; i; ss; eauto.
        }
        {
          destruct (decide (cid = i)); subst.
          {
            rewrite list_lookup_insert_ne // ?length_insert // in H1.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H2.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H3.
            des_ifs. eapply thread_rel_yield; eauto. eapply KTR.
          }
          rewrite !list_lookup_insert_ne // ?length_insert // in H1.
          rewrite !list_lookup_insert_ne // ?length_insert // in H2.
          rewrite !list_lookup_insert_ne // ?length_insert // in H3.
          hexploit REL; eauto; i. inv H6.
          { eapply thread_rel_spawn; eauto. }
          { eapply thread_rel_yield; eauto. }
        }
      }
      {
        rewrite Hr_t1 Hr_t2 Own_op -!assoc (assoc _ _ (Own x7)) length_insert.
        iIntros ">(D & $ & $ & $)". iModIntro.
        iPoseProof (big_sepL_insert_acc with "D") as "[$ D]"; [eapply RES|].
        iApply "D". iApply Own_unit.
      }
    }
    { (* middle of execution *)
      ziter_l; ziter_r. rewrite !list_lookup_insert_ne // SRC TGT /=.
      zstep_l. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. exists r_t2.
      zstep_r. ziter_r. zstep_r. unshelve eexists.
      { split; eauto. rewrite Hr_t3. eapply bupd_intro. }
      zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
      gstep; econs; econs; try exact smj_lt_mid_top.
      gbase. eapply CIH with (rs_diff:=<[tid:=ε]>rs_diff); eauto.
      { r; esplits; try rewrite !length_insert //.
        ii. destruct (decide (tid = i)); subst.
        {
          rewrite list_lookup_insert ?length_insert // in H1.
          rewrite list_lookup_insert ?length_insert // in H2.
          rewrite list_lookup_insert ?length_insert // in H4.
          des_ifs. eapply thread_rel_body; cycle 1; eauto.
        }
        {
          destruct (decide (cid = i)); subst.
          {
            rewrite list_lookup_insert_ne // ?length_insert // in H1.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H2.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H4.
            des_ifs. eapply thread_rel_yield; eauto. eapply KTR.
          }
          rewrite !list_lookup_insert_ne // ?length_insert // in H1.
          rewrite !list_lookup_insert_ne // ?length_insert // in H2.
          rewrite !list_lookup_insert_ne // ?length_insert // in H4.
          hexploit REL; eauto; i. inv H5.
          { eapply thread_rel_spawn; eauto. }
          { eapply thread_rel_yield; eauto. }
        }
      }
      {
        rewrite Hr_t1 Hr_t2 -!assoc length_insert.
        iIntros ">(D & $ & $ & $)". iModIntro.
        iPoseProof (big_sepL_insert_acc with "D") as "[_ D]"; [eapply RES|].
        iApply "D". iApply Own_unit.
      }
    }
  }
(*SLOW*)Qed.

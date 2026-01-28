Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma list_lookup_exists {A} (l: list A) n (LT: n < length l) :
  ∃ x, l !! n = Some x.
Proof.
  gen n. induction l; ss; [nia|]; i.
  destruct n; [esplits; eauto|].
  eapply Nat.succ_lt_mono in LT. hexploit IHl; eauto.
Qed.

Local Ltac sil := iter_l; rewrite !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite !list_insert_insert ?bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite !list_lookup_insert ?length_insert -EQLEN //
  end.
Local Ltac snr := norm_r; rewrite !list_insert_insert ?bind_ret_l.

Lemma cancel_yield `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) mm ntid :
  CANCEL_GOAL md sp PQ mm (HoareYieldE false ntid) (HoareYieldE true ntid).
Proof.
  r; i. subst.
  iter_l; iter_r. rewrite x0 x1 /=.
  step_l. norm_l. rewrite !bind_ret_l.
  step_r. intros ttid. ired.
  
  (* step_r. norm_r. rewrite !bind_ret_l. *)

  (* sir. step_r. snr. sir. step_r. snr. *)
  (* rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l. *)
  norm_r. step_r. norm_r. sir. step_r. snr. sir. step_r. snr.
  rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
  (* step_r. snr. *)
  sir. step_r. i. step_r. snr.
  sir. step_r. i. step_r. snr. sir. step_r. snr. rewrite Any.pair_split /=. sir. step_r. snr.
  sir. step_r. snr. sir. step_r. snr.
  
  des.
  assert (EQ: ttid = cid).
  { eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S"; iPoseProof (RS with "S") as ">[_ [R [TA _]]]".
    iPoseProof (x4 with "R") as ">[[T _] _]".
    iApply (TidToken_agree with "T"); iFrame. }
  subst.

  destruct (decide (ntid < length rs_diff)); cycle 1.
  {
    iter_l. destruct (<[cid:=_]> srcs !! ntid) eqn:FIND.
    { eapply lookup_lt_Some in FIND. rewrite length_insert in FIND. nia. }
    { step_l. rewrite /triggerUB. step_l. i; ss. }
  }
  
  assert (RS0: Own r_s ⊢
        |==> (([∗ list] i ∈ rs_diff, Own i) ∗ TIDAUTH ntid ∗ YIELDAUTH (length rs_diff)) ∗
        ((TID ntid ∗ YIELD ntid ∗ winv (⊤, ⊤)) ∗ Own x)).
  { rewrite RS x4. iIntros ">[$ [>[[T [$ $]] $] [TA $]]]".
    iApply (TidToken_upd with "[TA T]"); iFrame. }
  hexploit (Own_bupd_split); eauto.
  intros [r_t1 [r_t2 [Hr_t1 [Hr_t2 Hr_t3]]]].

  assert (TVALID: ✓ r_t2).
  { eapply Own_wand_valid with (a1:=r_s); eauto.
    rewrite Hr_t1. iIntros ">[_ $]"; eauto. }
  destruct (decide (ntid = cid)); subst.
  {
    
    sil. step_l. snl. sir. step_r. snr. sir. step_r. snr.
    rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
    sir. step_r. exists r_t2. step_r. snr. sir. step_r. 
    unshelve eexists; ired.
    { des; split; eauto. rewrite Hr_t3. eapply bupd_intro. }
    step_r. snr. sir. step_r. snr. rewrite Any.pair_split /= bind_ret_l.
    sir. step_r. snr. sir. step_r. snr.
    eapply KEY with (r_diff:=ε); eauto.
    { rewrite length_insert list_insert_id //.
      iIntros "S". iPoseProof (Hr_t1 with "S") as ">[S $]"; iStopProof.
      rewrite Hr_t2. eapply bupd_intro. }
    { eapply thread_rel_body; eauto. eapply KTR. }
  }
  {
  revert n; clear_until l; intros n.
  assert (Hntid : is_Some (rs_diff !! ntid)).
  { rewrite lookup_lt_is_Some //. }
  destruct Hntid as [rsntid Hntid].
  assert (RS0: Own r_s ⊢
                 |==> (([∗ list] i ∈ <[ntid:=ε]> rs_diff, Own i) ∗ TIDAUTH ntid ∗ YIELDAUTH (length rs_diff)) ∗
                 ((TID ntid ∗ YIELD ntid ∗ winv (⊤, ⊤)) ∗ Own (rsntid) ∗ Own x)).
  { rewrite RS x4. iIntros ">[A [>[[T [$ $]] $] [TA $]]]".
    iPoseProof (TidToken_upd with "[TA T]") as "> [$ $]"; iFrame.
    iPoseProof (big_sepL_insert_acc with "A") as "[$ A]"; auto using Hntid.
    iApply "A"; iApply Own_unit.
  }
  hexploit (Own_bupd_split); eauto.
  intros [r_t1 [r_t2 [Hr_t1 [Hr_t2 Hr_t3]]]].

  assert (TVALID: ✓ r_t2).
  { eapply Own_wand_valid with (a1:=r_s); eauto.
    rewrite Hr_t1. iIntros ">[_ $]"; eauto. }

     do 2 dup l. rename l into SRC, l0 into TGT, l1 into RES.
    rewrite EQLEN2 in SRC. rewrite EQLEN2 EQLEN in TGT.
    dup SRC; dup TGT; dup RES.
    eapply list_lookup_exists in SRC, TGT, RES; des.
    hexploit REL; eauto; intros RELTID. inv RELTID.
    { (* first execution *)
      iter_l; iter_r. rewrite !list_lookup_insert_ne // SRC TGT /=.
      step_l. norm_l. step_r. exists x8. step_r. norm_r.
      sir. step_r. snr. sir. step_r. exists varg. step_r. snr.
      sir. step_r. snr. sir. step_r. snr.
      rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
      sir. step_r. exists r_t2. step_r. snr.
      sir. step_r. unshelve eexists.
      { split; eauto. rewrite Hr_t3 H4. iIntros "[[? [? ?]] [> A $]]"; iApply ("A" with "[$] [$] [$]"). }
      s. ired.
      step_r. snr.
      sir. step_r. snr. rewrite Any.pair_split /= bind_ret_l.
      sir. step_r. snr. sir. step_r. snr.
      (* sir. step_r. snr. rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
      sir. step_r. exists (x7 ⋅ r_t2). step_r. snr.
      sir. step_r. unshelve eexists.
      { split; eauto.
        { eapply Own_wand_valid with (a1:=r_s); eauto.
          rewrite Hr_t1 Hr_t2 big_sepL_lookup_acc // Own_op.
          iIntros ">[[[$ _] _] $]"; eauto.
        }
        rewrite Own_op H4. iIntros "[>$ $]"; eauto.
      }
      step_r. snr. sir. step_r. snr. rewrite Any.pair_split /= bind_ret_l.
      sir. step_r. snr. sir. step_r. snr.
      rewrite /ModTr.trans in TGT. *)
      sil. step_l. snl.

      gstep. econs. econs; try exact smj_lt_mid_top.
      gbase. eapply CIH with (rs_diff:=<[ntid:=ε]>rs_diff); eauto.
      { r. esplits; try rewrite !length_insert //.
        ii. destruct (decide (ntid = i)); subst.
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
            des_ifs. ired. eapply thread_rel_yield; eauto. eapply KTR.
          }
          rewrite !list_lookup_insert_ne // ?length_insert // in H1.
          rewrite !list_lookup_insert_ne // ?length_insert // in H2.
          rewrite !list_lookup_insert_ne // ?length_insert // in H3.
          hexploit REL; eauto; i. inv H6.
          { eapply thread_rel_spawn; cycle 4; eauto. }
          { eapply thread_rel_yield; eauto. }
        }
      }
      {
        rewrite Hr_t1 Hr_t2 length_insert.
        (* Own_op -!assoc (assoc _ _ (Own x7)) length_insert. *)
        iIntros ">[[$ $] $] //".
        (* iModIntro.
        iPoseProof (big_sepL_insert_acc with "D") as "[$ D]"; [eapply RES|].
        iApply "D". iApply Own_unit. *)
      }
    }
    { (* middle of execution *)
      iter_l; iter_r. rewrite !list_lookup_insert_ne // SRC TGT /=.
      step_l. norm_l. step_r. norm_r.
      sir. step_r. snr.
      rewrite Any.pair_split /= bind_ret_l Any.upcast_downcast /= bind_ret_l.
      sir. step_r. exists r_t2. step_r. snr.
      sir. step_r. unshelve eexists.
      { split; eauto. rewrite Hr_t3. iIntros "[$ [? $]] //". }
      step_r. snr.
      sir. step_r. snr. rewrite Any.pair_split /= bind_ret_l.
      sir. step_r. snr. sir. step_r. snr.

      gstep; econs; econs; try exact smj_lt_mid_top.
      gbase. eapply CIH with (rs_diff:=<[ntid:=ε]>rs_diff); eauto.
      { r; esplits; try rewrite !length_insert //.
        ii. destruct (decide (ntid = i)); subst.
        {
          rewrite list_lookup_insert ?length_insert // in H.
          rewrite list_lookup_insert ?length_insert // in H2.
          rewrite list_lookup_insert ?length_insert // in H3.
          des_ifs. eapply thread_rel_body; cycle 1; eauto.
        }
        {
          destruct (decide (cid = i)); subst.
          {
            rewrite list_lookup_insert_ne // ?length_insert // in H.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H2.
            rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H3.
            des_ifs. ired. eapply thread_rel_yield; eauto. eapply KTR.
          }
          rewrite !list_lookup_insert_ne // ?length_insert // in H.
          rewrite !list_lookup_insert_ne // ?length_insert // in H2.
          rewrite !list_lookup_insert_ne // ?length_insert // in H3.
          hexploit REL; eauto; i. inv H5.
          { eapply thread_rel_spawn; cycle 4; eauto. }
          { eapply thread_rel_yield; eauto. }
        }
      }
      {
        rewrite Hr_t1 Hr_t2 -!assoc length_insert.
        iIntros ">($ & $ & $ & $) //".
        (* iModIntro.
        iPoseProof (big_sepL_insert_acc with "D") as "[_ D]"; [eapply RES|].
        iApply "D". iApply Own_unit. *)
      }
    }
  }
(*SLOW*)Qed.

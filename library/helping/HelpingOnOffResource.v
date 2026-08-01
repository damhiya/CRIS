From CRIS.common Require Import CRIS.
From CRIS.helping Require Import HelpingResource.
From iris.algebra Require Import gmap_view.
From iris.bi Require Import big_op.

(* Private authority used only by the HelpingOn/HelpingOff refinement. *)
#[local] Existing Instance helpingG.
#[local] Existing Instance helping_inG.

Section protocol.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition HelpAuth (reqmap : gmap nat help_state) : iProp Σ :=
    own help_name
      (None, Some (gmap_view_auth (DfracOwn 1)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO help_state))))).

  Definition help_erasure_init_cond : iProp Σ := HelpAuth ∅.

  Lemma HelpAuth_Help reqmap reqid df st :
    HelpAuth reqmap -∗ Help reqid df st -∗ ⌜reqmap !! reqid = Some st⌝.
  Proof.
    iIntros "● ◯".
    iCombine "● ◯" gives %[_ WF].
    rewrite /= -Some_op Some_valid in WF.
    eapply gmap_view_both_dfrac_valid_discrete in WF as
      [? [? [_ [WF [_ INCL]]]]].
    eapply Some_pair_included_r in INCL as INCL.
    rewrite lookup_fmap_Some in WF.
    destruct WF as [? [<- Hwf]]. rewrite Hwf.
    rewrite Some_included_total to_agree_included_L in INCL. clarify.
  Qed.

  Lemma HelpAuth_issue reqmap reqid N arg :
    reqmap !! reqid = None →
    HelpAuth reqmap ==∗
      HelpAuth (<[reqid := Pend N arg]> reqmap) ∗ HelpPend reqid N arg.
  Proof.
    iIntros (Hfresh) "●".
    rewrite /HelpAuth /HelpPend /Help.
    iMod (own_update _ _ ((None, _) ⋅ (None, _)) with "●") as "[$ $]".
    { eapply prod_update; ss.
      etransitivity; first apply option_update.
      { eapply (gmap_view_alloc
          (to_agree <$> reqmap : gmap nat (agreeR (leibnizO help_state)))
          reqid (DfracOwn 1) (to_agree (Pend N arg))).
        { rewrite lookup_fmap Hfresh //. }
        { rewrite dfrac_valid //. }
        { ss. }
      }
      rewrite Some_op -fmap_insert //.
    }
    done.
  Qed.

  Lemma HelpAuth_update reqmap reqid st1 st2 :
    HelpAuth reqmap -∗ Help reqid (DfracOwn 1) st1 ==∗
      HelpAuth (<[reqid := st2]> reqmap) ∗
      Help reqid (DfracOwn 1) st2.
  Proof.
    rewrite /HelpAuth /Help. iIntros "● ◯".
    iPoseProof (HelpAuth_Help with "● ◯") as "%".
    iMod (own_update_2 with "● ◯") as "[$ $]"; eauto.
    eapply prod_update; ss. rewrite -!Some_op. eapply option_update.
    etrans; first eapply gmap_view_replace.
    { instantiate (1 := to_agree st2). ss. }
    rewrite fmap_insert //.
  Qed.

  Lemma HelpAuth_claim reqmap reqid N arg :
    HelpAuth reqmap -∗ HelpPend reqid N arg ==∗
      HelpAuth (<[reqid := InProgress]> reqmap) ∗
      Help reqid (DfracOwn 1) InProgress.
  Proof. apply HelpAuth_update. Qed.

  Lemma HelpAuth_publish reqmap reqid ret :
    HelpAuth reqmap -∗ Help reqid (DfracOwn 1) InProgress ==∗
      HelpAuth (<[reqid := Done ret]> reqmap) ∗ HelpDone reqid ret.
  Proof.
    iIntros "● ◯".
    iMod (HelpAuth_update reqmap reqid InProgress (Done ret) with "● ◯")
      as "[$ ◯]".
    by iMod (Help_persist with "◯") as "$".
  Qed.

  Lemma HelpAuth_observe_done reqmap reqid ret :
    HelpAuth reqmap -∗ HelpDone reqid ret -∗
      ⌜reqmap !! reqid = Some (Done ret)⌝.
  Proof. apply HelpAuth_Help. Qed.
End protocol.

Section global_protocol.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition HelpRun (reqmap : gmap nat help_state) : iProp Σ :=
    ([∗ map] reqid ↦ st ∈ reqmap,
      match st with
      | InProgress => Help reqid (DfracOwn 1) InProgress
      | _ => emp
      end)%I.

  Definition res_rel (reqmap : gmap nat help_state) (rt rs : Σ) : Prop :=
    ✓ rs ∧ (Own rs ⊢ |==> Own rt ∗ HelpAuth reqmap ∗ HelpRun reqmap).

  Lemma HelpRun_empty : HelpRun ∅ ⊣⊢ emp.
  Proof. by rewrite /HelpRun big_sepM_empty. Qed.

  Lemma HelpRun_lookup_acc reqmap reqid st :
    reqmap !! reqid = Some st →
    HelpRun reqmap -∗
      (match st with
       | InProgress => Help reqid (DfracOwn 1) InProgress
       | _ => emp
       end) ∗
      ((match st with
        | InProgress => Help reqid (DfracOwn 1) InProgress
        | _ => emp
        end) -∗ HelpRun reqmap).
  Proof.
    intros Hlookup. rewrite /HelpRun.
    iIntros "Hrun".
    iApply (big_sepM_lookup_acc with "Hrun").
    exact Hlookup.
  Qed.

  Lemma HelpRun_lookup_in_progress reqmap reqid :
    reqmap !! reqid = Some InProgress →
    HelpRun reqmap -∗
      Help reqid (DfracOwn 1) InProgress ∗
      (Help reqid (DfracOwn 1) InProgress -∗ HelpRun reqmap).
  Proof. apply HelpRun_lookup_acc. Qed.

  Lemma HelpRun_delete reqmap reqid st :
    reqmap !! reqid = Some st →
    HelpRun reqmap ⊣⊢
      (match st with
       | InProgress => Help reqid (DfracOwn 1) InProgress
       | _ => emp
       end) ∗ HelpRun (delete reqid reqmap).
  Proof.
    intros Hlookup. rewrite /HelpRun.
    iSplit; iIntros "Hrun".
    - iDestruct (big_sepM_delete _ reqmap reqid st Hlookup with "Hrun")
        as "[$ $]".
    - rewrite (big_sepM_delete _ reqmap reqid st Hlookup). iFrame.
  Qed.

  Lemma HelpRun_insert reqmap reqid st :
    HelpRun (<[reqid := st]> reqmap) ⊣⊢
      (match st with
       | InProgress => Help reqid (DfracOwn 1) InProgress
       | _ => emp
       end) ∗ HelpRun (delete reqid reqmap).
  Proof.
    rewrite /HelpRun.
    iSplit; iIntros "Hrun".
    - iDestruct (big_sepM_insert_delete with "Hrun") as "[$ $]".
    - rewrite big_sepM_insert_delete. iFrame.
  Qed.

  Lemma res_rel_init rt rs :
    ✓ rs →
    (Own rs ⊢ |==> Own rt ∗ help_erasure_init_cond) →
    res_rel ∅ rt rs.
  Proof.
    intros Hvalid Hinit. split; first done.
    iIntros "Hrs".
    iMod (Hinit with "Hrs") as "[Hrt Hauth]".
    iModIntro. iFrame.
    rewrite HelpRun_empty. done.
  Qed.

  Lemma HelpRun_claim reqmap reqid N arg :
    HelpAuth reqmap -∗ HelpRun reqmap -∗ HelpPend reqid N arg ==∗
      HelpAuth (<[reqid := InProgress]> reqmap) ∗
      HelpRun (<[reqid := InProgress]> reqmap).
  Proof.
    iIntros "Hauth Hrun Hpend".
    iPoseProof (HelpAuth_Help with "Hauth Hpend") as "%Hlookup".
    iDestruct (HelpRun_delete reqmap reqid (Pend N arg) Hlookup with "Hrun")
      as "[_ Hrun]".
    iMod (HelpAuth_claim with "Hauth Hpend") as "[Hauth Htoken]".
    iModIntro. iFrame "Hauth".
    rewrite HelpRun_insert /=. iFrame.
  Qed.

  Lemma HelpRun_publish reqmap reqid ret :
    reqmap !! reqid = Some InProgress →
    HelpAuth reqmap -∗ HelpRun reqmap ==∗
      HelpAuth (<[reqid := Done ret]> reqmap) ∗
      HelpRun (<[reqid := Done ret]> reqmap) ∗
      HelpDone reqid ret.
  Proof.
    iIntros (Hlookup) "Hauth Hrun".
    iDestruct (HelpRun_delete reqmap reqid InProgress Hlookup with "Hrun")
      as "[Htoken Hrun]".
    iMod (HelpAuth_publish with "Hauth Htoken") as "[Hauth Hdone]".
    iModIntro. iFrame "Hauth Hdone".
    rewrite HelpRun_insert /=. iFrame.
  Qed.

  Lemma res_rel_issue reqmap rt rs reqid N arg :
    reqmap !! reqid = None →
    res_rel reqmap rt rs →
    ∃ rt2, ✓ rt2 ∧
      (Own rt2 ⊢ |==> HelpPend reqid N arg ∗ Own rt) ∧
      res_rel (<[reqid := Pend N arg]> reqmap) rt2 rs.
  Proof.
    intros Hfresh [Hvalid Hrel].
    assert (Hissue :
      Own rs ⊢ |==>
        (HelpPend reqid N arg ∗ Own rt) ∗
        (HelpAuth (<[reqid := Pend N arg]> reqmap) ∗
         HelpRun (<[reqid := Pend N arg]> reqmap))).
    { iIntros "Hrs".
      iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
      iMod (HelpAuth_issue reqmap reqid N arg Hfresh with "Hauth")
        as "[Hauth Hpend]".
      iModIntro. iSplitL "Hpend Hrt"; first iFrame.
      iFrame "Hauth".
      rewrite HelpRun_insert /= (delete_notin reqmap reqid Hfresh). iFrame. }
    eapply Own_bupd_split in Hissue
      as [rt2 [rhidden
        [Hsplit [Hpublic [Hhidden Hsplit_valid]]]]]; [|exact Hvalid].
    exists rt2. split.
    { eauto using cmra_valid_op_l. }
    split.
    { iIntros "Hrt2".
      iPoseProof (Hpublic with "Hrt2") as "[Hpend Hrt]".
      iModIntro. iFrame. }
    split; first exact Hvalid.
    iIntros "Hrs".
    iMod (Hsplit with "Hrs") as "[Hrt2 Hhidden]".
    iPoseProof (Hhidden with "Hhidden") as "[Hauth Hrun]".
    iModIntro. iFrame.
  Qed.

  Lemma res_rel_claim reqmap rt rs reqid N arg rt2 :
    res_rel reqmap rt rs →
    (Own rt ⊢ |==> HelpPend reqid N arg ∗ Own rt2) →
    reqmap !! reqid = Some (Pend N arg) ∧
    res_rel (<[reqid := InProgress]> reqmap) rt2 rs.
  Proof.
    intros [Hvalid Hrel] Hclaim.
    assert (Hlookup : reqmap !! reqid = Some (Pend N arg)).
    { eapply (Own_pure_soundness rs); first exact Hvalid.
      iIntros "Hrs".
      iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
      iMod (Hclaim with "Hrt") as "[Hpend Hrt2]".
      iApply (HelpAuth_Help with "Hauth Hpend"). }
    split; first exact Hlookup.
    split; first exact Hvalid.
    iIntros "Hrs".
    iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
    iMod (Hclaim with "Hrt") as "[Hpend Hrt2]".
    iMod (HelpRun_claim with "Hauth Hrun Hpend") as "[Hauth Hrun]".
    iModIntro. iFrame.
  Qed.

  Lemma res_rel_publish reqmap rt rs reqid ret :
    reqmap !! reqid = Some InProgress →
    res_rel reqmap rt rs →
    ∃ rt2, ✓ rt2 ∧
      (Own rt2 ⊢ |==> HelpDone reqid ret ∗ Own rt) ∧
      res_rel (<[reqid := Done ret]> reqmap) rt2 rs.
  Proof.
    intros Hlookup [Hvalid Hrel].
    assert (Hpublish :
      Own rs ⊢ |==>
        (HelpDone reqid ret ∗ Own rt) ∗
        (HelpAuth (<[reqid := Done ret]> reqmap) ∗
         HelpRun (<[reqid := Done ret]> reqmap))).
    { iIntros "Hrs".
      iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
      iMod (HelpRun_publish reqmap reqid ret Hlookup with "Hauth Hrun")
        as "[Hauth [Hrun Hdone]]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in Hpublish
      as [rt2 [rhidden
        [Hsplit [Hpublic [Hhidden Hsplit_valid]]]]]; [|exact Hvalid].
    exists rt2. split.
    { eauto using cmra_valid_op_l. }
    split.
    { iIntros "Hrt2".
      iPoseProof (Hpublic with "Hrt2") as "[Hdone Hrt]".
      iModIntro. iFrame. }
    split; first exact Hvalid.
    iIntros "Hrs".
    iMod (Hsplit with "Hrs") as "[Hrt2 Hhidden]".
    iPoseProof (Hhidden with "Hhidden") as "[Hauth Hrun]".
    iModIntro. iFrame.
  Qed.

  Lemma res_rel_observe reqmap rt rs reqid ret rt2 :
    res_rel reqmap rt rs →
    (Own rt ⊢ |==> HelpDone reqid ret ∗ Own rt2) →
    reqmap !! reqid = Some (Done ret) ∧ res_rel reqmap rt2 rs.
  Proof.
    intros [Hvalid Hrel] Hobserve.
    assert (Hlookup : reqmap !! reqid = Some (Done ret)).
    { eapply (Own_pure_soundness rs); first exact Hvalid.
      iIntros "Hrs".
      iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
      iMod (Hobserve with "Hrt") as "[Hdone Hrt2]".
      iApply (HelpAuth_observe_done with "Hauth Hdone"). }
    split; first exact Hlookup.
    split; first exact Hvalid.
    iIntros "Hrs".
    iMod (Hrel with "Hrs") as "[Hrt [Hauth Hrun]]".
    iMod (Hobserve with "Hrt") as "[_ Hrt2]".
    iModIntro. iFrame.
  Qed.
End global_protocol.

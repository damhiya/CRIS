Require Import CRIS.
From CRIS.helping Require Import Header HelpingOn HelpingAux.
Require Import SchHeader SchTactics.
From iris.algebra Require Import gmap_view.

(* Resource algebra for the helping module *)
Definition helpingR (jobID retID : Type) : cmra :=
  gmap_viewR nat (agreeR (leibnizO (option retID * jobID))).

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !inG (helpingR jobID retID) Γ}.

  Definition syn_helping_token n (tid : nat) (jid : jobID) : GTerm.t n :=
    <own> base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid (DfracOwn 1) (to_agree (None, jid))).
  Definition helping_token (tid : nat) (jid : jobID) : iProp Σ :=
    own base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid (DfracOwn 1) (to_agree (None, jid))).
  Global Instance SLRed_helping_token {n} tid jid :
    SLRed (syn_helping_token n tid jid) (helping_token tid jid).
  Proof. econs; rewrite SLRed_red //. Qed.

  Definition syn_helping_done n (tid : nat) (retid : retID) : GTerm.t n :=
    (∃ (jid : τ{jobID}), <own> base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid DfracDiscarded (to_agree (Some retid, jid))))%SAT.
  Definition helping_done (tid : nat) (retid : retID) : iProp Σ :=
    ∃ jid, own base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid DfracDiscarded (to_agree (Some retid, jid))).
  Global Instance SLRed_helping_done n tid retid :
    SLRed (syn_helping_done n tid retid) (helping_done tid retid).
  Proof. econs; rewrite SLRed_red //. Qed. 
  Global Instance helping_done_persistent tid retid : Persistent (helping_done tid retid).
  Proof. apply _. Qed.

  Definition syn_helping_auth n q (reqmap : gmap nat (option retID * jobID)) : GTerm.t n :=
    (<own> base_γ
      (gmap_view_auth (DfracOwn q)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO (option retID * jobID))))))%SAT.
  Definition helping_auth q (reqmap : gmap nat (option retID * jobID)) : iProp Σ :=
    own base_γ
      (gmap_view_auth (DfracOwn q)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO (option retID * jobID))))).
  Global Instance SLRed_helping_auth n q reqmap :
    SLRed (syn_helping_auth n q reqmap) (helping_auth q reqmap).
  Proof. econs; rewrite SLRed_red //. Qed.

  Lemma helping_auth_split (q : Qp) (reqmap : gmap nat (option retID * jobID)) :
    (q < 1)%Qp →
    helping_auth 1 reqmap -∗
    (helping_auth q reqmap ∗ (∀ reqmap', helping_auth q reqmap' -∗ helping_auth 1 reqmap)).
  Proof.
    intros Hq.
    assert (Hr : (∃ r, 1 - q = Some r)%Qp).
    { destruct (1 - q)%Qp as [r'|] eqn : Hq'; first eauto.
      apply Qp.sub_None in Hq'. exfalso. apply (StrictOrder_Asymmetric _ 1%Qp q); eauto.
      apply Qp.le_lteq in Hq'; des; subst; eauto.
    }
    destruct Hr as [r Hr%Qp.sub_Some]; rewrite Hr {1}/helping_auth.
    rewrite -dfrac_op_own. iIntros "Help●"; iDestruct "Help●" as "[$ H]".
    iIntros (reqmap') "H2"; iCombine "H" "H2" gives %WF%gmap_view_auth_dfrac_op_inv.
    iCombine "H" "H2" as "H"; rewrite comm -Hr -WF -gmap_view_auth_dfrac_op dfrac_op_own -Hr.
    iFrame; ss.
  Qed.

  Lemma helping_auth_done q reqmap reqid ret :
    helping_auth q reqmap -∗ helping_done reqid ret -∗
    ∃ jid, ⌜reqmap !! reqid = Some (Some ret, jid)⌝.
  Proof.
    iIntros "● [%jid ◯]"; iExists jid.
    iCombine "● ◯" gives %[? [? [_ [WF [_ INCL]]]]]%gmap_view_both_dfrac_valid_discrete.
    eapply Some_pair_included_r in INCL as INCL.
    rewrite lookup_fmap_Some in WF; destruct WF as [? [<- Hwf]]; rewrite Hwf.
    rewrite Some_included_total to_agree_included_L in INCL; clarify.
  Qed.

  Lemma helping_auth_token q reqmap reqid jid :
    helping_auth q reqmap -∗ helping_token reqid jid -∗
    ⌜reqmap !! reqid = Some (None, jid)⌝.
  Proof.
    iIntros "● ◯".
    iCombine "● ◯" gives %[? [? [_ [WF [_ INCL]]]]]%gmap_view_both_dfrac_valid_discrete.
    eapply Some_pair_included_r in INCL as INCL.
    rewrite lookup_fmap_Some in WF; destruct WF as [? [<- Hwf]]; rewrite Hwf.
    rewrite Some_included_total to_agree_included_L in INCL; clarify.
  Qed.

  Lemma helping_auth_commit reqmap reqid jid ret :
    helping_auth 1 reqmap -∗ helping_token reqid jid ==∗
    helping_auth 1 (<[reqid := (Some ret, jid)]> reqmap) ∗ helping_done reqid ret.
  Proof.
    rewrite /helping_auth /helping_token; iIntros "● ◯".
    iPoseProof (helping_auth_token with "● ◯") as "%H".
    iMod (own_update_2 with "● ◯") as "[$ $]"; eauto.
    { etrans; first eapply gmap_view_replace.
      { instantiate (1:=to_agree (Some ret, jid)); ss. }
      rewrite fmap_insert cmra_update_op; try refl.
      apply gmap_view_frag_persist.
    }
  Qed.
End resource.

Section help.
  Context (jobID retID : Type).
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !inG (helpingR jobID retID) Γ}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : alist key Any.t → alist key Any.t → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  (* Helping related context *)
  Context (jobs : jobID → itree Helping.pureE retID).
  Context (mn : string) (sp : sp_type).

  Definition IstHelp (Ist : ist_type Σ) : ist_type Σ := λ st_src st_tgt,
    (∃ (reqmap_s reqmap_t : gmap nat (option retID * jobID)),
      ⌜st_src = [(HelpingOn.v_reqs mn, reqmap_s↑)] ∧
       st_tgt = [(HelpingOn.v_reqs mn, reqmap_t↑)]⌝ ∗
      helping_auth 1 reqmap_s)%I.

  (* Lemma IstHelp_split (q : Qp) :
    (q < 1)%Qp →
    IstHelp Ist st_src st_tgt -∗
    (∃ reqmap, helping_auth q reqmap ∗ (helping_auth q reqmap -∗ IstHelp Ist st_src st_tgt)).
  Proof.
    iIntros (Hq) "[% [% [% [% [% [Help● IST]]]]]]"; hss.
    assert (Hr : (∃ r, 1 - q = Some r)%Qp).
    { destruct (1 - q)%Qp as [r'|] eqn : Hq'; first eauto.
      apply Qp.sub_None in Hq'. exfalso. apply (StrictOrder_Asymmetric _ q 1%Qp); eauto.
      apply Qp.le_lteq in Hq'; des; subst; eauto.
    }
    destruct Hr as [r Hr%Qp.sub_Some]; rewrite Hr {1}/helping_auth.
    rewrite -dfrac_op_own.
    iExists reqmap; iDestruct "Help●" as "[$ H]".
    iIntros "H2"; iCombine "H" "H2" as "H"; rewrite comm -Hr; iFrame; iExists _; ss.
  Qed.

  Lemma IstHelp_done req_id job_id (reqmap : gmap nat (option retID * jobID)) (ret : retID) :
    helping_token req_id job_id -∗
    IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src) st_tgt ==∗
    helping_done req_id ret ∗
    IstHelp Ist
      ((HelpingOn.v_reqs mn, (<[req_id := (Some ret, job_id)]> reqmap)↑) :: st_src) st_tgt.
  Proof.
    iIntros "Help [% [% [% [% [% [Help● IST]]]]]]"; hss.
    iMod (own_update_2 with "Help● Help") as "[Help● Help]".
    { eapply gmap_view_replace. instantiate (1:=(to_agree (Some ret, job_id))); done. }
    iMod (own_update with "Help") as "$".
    { eapply gmap_view_frag_persist. }
    iExists _, _, _, _; iModIntro; iSplit; first done.
    rewrite -fmap_insert; iFrame "Help●"; done.
  Qed.

  Lemma wsim_helping_run (parg : jobID) k_s k_t E1 E2 r g img_t msk_t scp_t :
    alist_find (Some (Helping.run mn)) fl_s =
      Some (SB.sandbox_body
        (SModTr.trans_ktree sp
          (true, wmask_all, HelpingOn.scopes mn, (None, HelpingOn.run mn jobs)))) →
    (msk_t (Helping.run mn) : bool) →
    IstHelp Ist st_src st_tgt -∗
    (∀ st_src st_tgt req_id,
      IstHelp Ist st_src st_tgt -∗
      helping_token req_id parg -∗
      wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR true pt
        (st_src,
          SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp 𝒴);;;
          x_ <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (r <- HelpingOn.try_run mn jobs req_id;; 𝒴;;; Ret (r↑)));;
          x_0 <- (tau;; Ret x_);;
          x_1 <- (SB.sandbox img_t msk_t scp_t (Ret x_0));; k_s x_1)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR ps pt
      (st_src, x <- (SB.sandbox img_t msk_t scp_t (trigger (Call (Helping.run mn) parg↑)));; k_s x)
      (st_tgt, k_t).
  Proof.
    iIntros (Hfind Hmsk) "IST K".
    inline_l. steps_l. hss. rename _q into pargs.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [Help● IST]]]]]]". steps_l. hss. rename _q into reqmap. ired.
    iMod (own_update with "Help●") as "[Help● Help◯]".
    { eapply (gmap_view_alloc _ (fresh (dom reqmap)) (DfracOwn 1)); eauto.
      { apply not_elem_of_dom. rewrite dom_fmap. apply is_fresh. }
      { rewrite dfrac_valid; eauto. }
      { instantiate (1:=(to_agree (None, pargs))); ss. }
    }
    set (st_src := _ :: _). set (st_tgt := _ :: _).
    iAssert (IstHelp Ist st_src st_tgt)%I with "[IST Help●]" as "IST".
    { iFrame. subst st_src. ss. iExists _, _; iSplit; first done.
      rewrite -fmap_insert //.
    }
    iApply ("K" $! st_src st_tgt (fresh (dom reqmap)) with "IST Help◯").
  Qed.

  (* TODO : modify helping so that we do not see cput after job execution *)
  Lemma wsim_helping_try_run (req_id : nat) (parg : jobID) k_s k_t E1 E2 r g img_t msk_t scp_t :
    helping_token req_id parg -∗
    IstHelp Ist st_src st_tgt -∗
    (∀ (reqmap : gmap nat (option retID * jobID)) st_src0,
      helping_token req_id parg -∗
      IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0) st_tgt -∗
      wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR true pt
        ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0,
          x_ <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (r <- Helping.trans (jobs parg);;
            (cput (HelpingOn.v_reqs mn) (<[req_id := (Some r, parg)]> reqmap));;;
            Ret (r)));;
          x_0 <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (𝒴;;; Ret (x_↑)));;
          x_1 <- (tau;; Ret x_0);;
          x_2 <- (SB.sandbox img_t msk_t scp_t (Ret x_1));; k_s x_2)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
          (HelpingOn.try_run mn jobs req_id));;
        x_0 <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
          (𝒴;;; Ret x_↑));;
        x_1 <- (tau;; Ret x_0);;
        x_2 <- (SB.sandbox img_t msk_t scp_t (Ret x_1));; k_s x_2)
      (st_tgt, k_t).
  Proof.
    iIntros "Help IST K".
    iDestruct "IST" as "[% [% [% [% [[-> ->] [Help● IST]]]]]]".
    rewrite /HelpingOn.try_run.
    steps_l. hss. rename _q into reqmap.
    iCombine "Help●" "Help" gives %[v' [? [_ [WF [_ EQ]]]]]%gmap_view_both_dfrac_valid_discrete.
    apply lookup_fmap_Some in WF as [[ro parg'] [? Hlookup]]; clarify.
    rewrite Hlookup. apply Some_pair_included in EQ as [_ EQ].
    rewrite Some_included_total to_agree_included in EQ; inv EQ; clarify.
    iApply ("K" $! reqmap st_src1 with "Help"). iFrame. eauto.
  Qed. *)
End help.

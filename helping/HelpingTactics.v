Require Import CRIS.
Require Export HelpingOn HelpingOff.
Require Import SchHeader SchTactics SchI SchA.
From iris.algebra Require Import gmap_view.

(* Resource algebra for the helping module *)
Definition helpingR (jobID retID : Type) : cmra :=
  gmap_viewR nat (agreeR (leibnizO (option retID * jobID))).

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !inG (helpingR jobID retID) Γ}.

  Definition syn_helping_token n (tid : nat) (jid : jobID) : GTerm.t n :=
    sown base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid (DfracOwn 1) (to_agree (None, jid))).
  Definition helping_token (tid : nat) (jid : jobID) : iProp Σ :=
    own base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid (DfracOwn 1) (to_agree (None, jid))).
  Global Instance SLRed_helping_token n tid jid :
    SLRed n (syn_helping_token n tid jid) (helping_token tid jid).
  Proof. solve_sl_red. Qed.

  Definition syn_helping_done n (tid : nat) (retid : retID) : GTerm.t n :=
    (∃ (jid : τ{jobID}), sown base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid DfracDiscarded (to_agree (Some retid, jid))))%SAT.
  Definition helping_done (tid : nat) (retid : retID) : iProp Σ :=
    ∃ jid, own base_γ
      (gmap_view_frag (V:=agreeR $ leibnizO (option retID * jobID))
        tid DfracDiscarded (to_agree (Some retid, jid))).
  Global Instance SLRed_helping_done n tid retid :
    SLRed n (syn_helping_done n tid retid) (helping_done tid retid).
  Proof. solve_sl_red. Qed. 
  Global Instance helping_done_persistent tid retid : Persistent (helping_done tid retid).
  Proof. apply _. Qed.

  Definition syn_helping_auth n q (reqmap : gmap nat (option retID * jobID)) : GTerm.t n :=
    (sown base_γ
      (gmap_view_auth (DfracOwn q)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO (option retID * jobID))))))%SAT.
  Definition helping_auth q (reqmap : gmap nat (option retID * jobID)) : iProp Σ :=
    own base_γ
      (gmap_view_auth (DfracOwn q)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO (option retID * jobID))))).
  Global Instance SLRed_helping_auth n q reqmap :
    SLRed n (syn_helping_auth n q reqmap) (helping_auth q reqmap).
  Proof. solve_sl_red. Qed.

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

  Definition IstHelp (mn : string) : ist_type Σ :=
    λ st_src st_tgt,
      (∃ (reqmap_s : gmap nat (option retID * jobID)),
        ⌜st_src = {[HelpingOn.v_reqs mn # reqmap_s↑]} ∧ st_tgt = ∅⌝ ∗
        helping_auth 1 reqmap_s)%I.
End resource.

Section help.
  Context (jobID retID : Type).
  Context `{!crisG Γ Σ α β τ _S _I, !inG (helpingR jobID retID) Γ}.

  Local Notation state := (gmap key (option Any.t)).
  Local Notation post R_s R_t := (state * R_s → state * R_t → iProp Σ).
  
  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (st_src st_tgt : state).

  (* Helping related context *)
  Context (jobs : jobID → itree crisE retID).
  Context (mn : string) (sp : specmap).

  Local Definition IstFull := IstProd (IstSB [mn] (IstHelp mn)) IstEq.

  Lemma wsim_helping_run (ps pt : bool) (parg : jobID) k_s k_t E1 E2 r g :
    fl_s !! fid (Helping.run mn) =
      Some (Some (SB.sandbox_body
        (msk_scp (HelpingOn.scopes mn) msk_true, (SModTr.trans_fnsem sp (None, HelpingOn.run mn jobs))))) →
    IstFull st_src st_tgt -∗
    (∀ (st_src st_tgt : state) req_id,
      IstFull st_src st_tgt -∗
      helping_token req_id parg -∗
      wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR true pt
        (st_src,
          SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true) (SModTr.trans sp 𝒴);;;
          x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true) (SModTr.trans sp
            (r <- HelpingOn.try_run mn jobs req_id;; 𝒴;;; Ret (r↑)));;
          x_0 <- (tau;; Ret x_);;
          x <- Ret x_0;;
          k_s x)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR ps pt
      (st_src, x <- (trigger (Call (Helping.run mn) parg↑));; k_s x)
      (st_tgt, k_t).
  Proof using.
    iIntros (Hfind) "IST K".
        (* TODO : factor out this proof into a lemma *)
    cInlineS. cStepsS. rewrite /HelpingOn.run. cStepsS.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[% [% [[-> ->] ●Help]]] ->]]]]]]".
    cStepsS.
    iMod (own_update with "●Help") as "[●Help Help◯]".
    { eapply (gmap_view_alloc _ (fresh (dom reqmap_s)) (DfracOwn 1)); eauto.
      { apply not_elem_of_dom. rewrite dom_fmap. apply is_fresh. }
      { rewrite dfrac_valid; eauto. }
      { instantiate (1:=(to_agree (None, _))); ss. }
    }
    set (st_src := union_with _ _ _). set (st_tgt := union_with _ _ _).
    iAssert (IstFull st_src st_tgt)%I with "[●Help]" as "IST".
    { iExists _, _, _, _; subst st_src st_tgt; repeat iSplit; eauto.
      { iPureIntro; set_solver. }
      rewrite -fmap_insert //. iFrame; done.
    }
    iAssert (helping_token (fresh (dom _)) _)%I with "Help◯" as "Tkn".
    iPoseProof ("K" $! st_src st_tgt _ with "IST Tkn") as "K".
    iApply "K".
  Qed.

  Lemma wsim_helping_pend_try_run (ps pt : bool) k_s k_t E1 E2 r g req_id x :
    helping_token req_id x -∗
    IstFull st_src st_tgt -∗
    (wsim fl_s fl_t IstFull (E1, E2) r g retID ()
      (λ '(st_s, r_s) '(st_t, r_t), ⌜st_s = st_src ∧ st_t = st_tgt⌝ ∗ winv (E1, E2) ∗
        (∀ st_src st_tgt,
          helping_done req_id r_s -∗
          IstFull st_src st_tgt -∗
          wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR true false
            (st_src, k_s r_s) (st_tgt, k_t)))
      true pt
        (st_src, SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (SB.sandbox msk_pure (jobs x))))
        (st_tgt, Ret ())) -∗
    wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.try_run mn jobs req_id));;
        k_s x_)
      (st_tgt, k_t).
  Proof using.
    iIntros "Pend IST K".
    rewrite /HelpingOn.try_run; cStepsS.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[% [% [[-> ->] Auth]]] IST]]]]]]".
    cStepsS.
    iPoseProof (helping_auth_token with "Auth Pend") as "%Hlookup"; rewrite Hlookup /=; cStepsS.
    replace k_t with (x <- Ret ();; (λ _, k_t) x) at 1 by grind.
    iApply wsim_bind.
    iSplitR "Pend Auth IST".
    { iApply "K". }
    iIntros (? ? ? ?) "[[-> ->] [W K]]"; iApply wsim_fold; iSplitL "W"; iFrame.
    cStepsS.
    iMod (helping_auth_commit with "Auth Pend") as "[Auth Pend]".
    set (st_src := union_with _ _ _); set (st_tgt := union_with _ _ _).
    iAssert (IstFull st_src st_tgt)%I with "[IST Auth]" as "IST".
    { iExists _, _, _, _; iFrame. repeat iSplit; eauto. iPureIntro; set_solver. }
    iApply ("K" with "Pend IST").
  Qed.

  Lemma wsim_helping_done_try_run (ps pt : bool) k_s k_t E1 E2 r g req_id ret_id :
    helping_done req_id ret_id -∗
    IstFull st_src st_tgt -∗
    (IstFull st_src st_tgt -∗
      wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR true pt
        (st_src, k_s ret_id)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t IstFull (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.try_run mn jobs req_id));; k_s x_)
      (st_tgt, k_t).
  Proof using.
    iIntros "#Done IST K".
    rewrite /HelpingOn.try_run /=. cStepsS.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[% [% [[-> ->] ●Help]]] IST]]]]]]".
    cStepsS.
    iPoseProof (helping_auth_done with "●Help Done") as "[% %Heq]"; rewrite Heq; clear Heq.
    cStepsS.
    iApply ("K" with "[IST ●Help]").
    iFrame; iExists _, _; iSplit; eauto.
  Qed.

  Lemma wsim_helping_help
      `{!schGS} (ps pt : bool) k_s k_t E r g (req_id : nat) x arg (mtid stid : nat) :
    sp.1 !! (fid SchHdr.yield) = fsp_some (SchA.yield_spec E) →
    Tid mtid stid -∗
    helping_token req_id x -∗
    IstFull st_src st_tgt -∗
    (wsim fl_s fl_t IstFull (E, E) r g retID ()
      (λ '(st_s, r_s) '(st_t, r_t), ⌜st_s = st_src ∧ st_t = st_tgt⌝ ∗ winv (E, E) ∗
        (∀ st_src st_tgt,
          Tid mtid stid -∗
          helping_done req_id r_s -∗
          IstFull st_src st_tgt -∗
          wsim fl_s fl_t IstFull (E, E) r g R_s R_t RR true false
            (st_src, k_s ()↑) (st_tgt, k_t)))
      true pt
        (st_src, SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (SB.sandbox msk_pure (jobs x))))
        (st_tgt, Ret ())) -∗
    wsim fl_s fl_t IstFull (E, E) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.help mn jobs sp arg));; k_s x_)
      (st_tgt, k_t).
  Proof using.
    iIntros (Hsp) "TID Tkn IST SIM".
    rewrite /HelpingOn.help Hsp.
    cForceS req_id. cForceS (stid, mtid, tt). cForcesS. iFrame. iSplit; eauto.
    cStepsS. destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".
    iApply (wsim_helping_pend_try_run with "Tkn IST").
    appendRetS. prependRetT ().
    iApply wsim_bind.
    iSplitL "SIM"; iFrame.
    s. iIntros (sts1 stt1 rets []) "[[-> ->] [? SIM]]"; iApply wsim_fold; iFrame.
    cStep; iFrame. iSplit; first auto.
    clear_st. iIntros (st_src st_tgt) "Tkn IST".
    cForcesS. iFrame. iSplit; eauto.
    cStepsS. iDestruct "ASM" as "[TID [_ ->]]". iApply ("SIM" with "[$] [$]"); done.
  Qed.
     
  (* Lemma IstHelp_split (q : Qp) :
    (q < 1)%Qp →
    IstHelp Ist st_src st_tgt -∗
    (∃ reqmap, helping_auth q reqmap ∗ (helping_auth q reqmap -∗ IstHelp Ist st_src st_tgt)).
  Proof.
    iIntros (Hq) "[% [% [% [% [% [Help● IST]]]]]]"; cSimpl.
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
    iIntros "Help [% [% [% [% [% [Help● IST]]]]]]"; cSimpl.
    iMod (own_update_2 with "Help● Help") as "[Help● Help]".
    { eapply gmap_view_replace. instantiate (1:=(to_agree (Some ret, job_id))); done. }
    iMod (own_update with "Help") as "$".
    { eapply gmap_view_frag_persist. }
    iExists _, _, _, _; iModIntro; iSplit; first done.
    rewrite -fmap_insert; iFrame "Help●"; done.
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
    cStepsS. cSimpl. rename _q into reqmap.
    iCombine "Help●" "Help" gives %[v' [? [_ [WF [_ EQ]]]]]%gmap_view_both_dfrac_valid_discrete.
    apply lookup_fmap_Some in WF as [[ro parg'] [? Hlookup]]; clarify.
    rewrite Hlookup. apply Some_pair_included in EQ as [_ EQ].
    rewrite Some_included_total to_agree_included in EQ; inv EQ; clarify.
    iApply ("K" $! reqmap st_src1 with "Help"). iFrame. eauto.
  Qed. *)
End help.

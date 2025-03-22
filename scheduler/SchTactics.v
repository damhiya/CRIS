Require Import CRIS SchHeader SchA.
Require Import ITactics.

Section wrapper.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ}.
  Definition w_fspec_sch (υ: univ_id) (fsp : fspec) : fspec :=
    w_fspec υ
     (mk_fspec (meta := nat * (fsp).(meta))
        (fun '(tid, x) varg arg =>
          SchAS.tid_user tid ∗ fsp.(precond) x varg arg)%I
        (fun '(tid, x) vret ret =>
          SchAS.tid_user tid ∗ fsp.(postcond) x vret ret)%I).
End wrapper.

Section wsim.
  Import SchAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ, !SchAGΓ Γ}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree hmodE R_s → state * itree hmodE R_t → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (υ ν : univ_id).
  Context (E : coPset).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  Lemma wsim_yield_tgt_u0 r g scp_s scp_t ginv spc spc_user k_s k_t my_tid
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    (∀ nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODT: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp Sch.yield)) >>= k_t).
  Proof.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "SIM P".
    iApply isim_nodup. iIntros (? ? ? ?). hss.
    rewrite /Sch.yield; unseal "Sch".
    (* iApply isim_reset. *)
    iStopProof.
    revert nths. 
    combine_quant NODS. combine_quant NODD.
    combine_quant st_s. combine_quant st_t. combine_quant ps. combine_quant pt.
    eapply isim_coind.
    iIntros (g' [pt [ps [st_t' [st_s' [NODD [NODS nths']]]]]]) "%MON [[[IST [TID SIM]] P] #CIH]". s.

    unfold_iter_r.
    steps_r. destruct q.
    { steps_r. iPoseProof ("SIM" $! _ _ _ NODS NODD with "IST TID P") as "SIM"; iFrame.
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>"; iApply MON; ss. }
    }

    steps_r.
    unfold_iter_l; steps_l.
    force_l false; steps_l.
    iApply isim_progress.
    forces_l. iSplitL "P TID"; iFrame; eauto.
    steps_l.

    (* "hss" removes nodup-assumption *)
    iApply isim_call. iSplitL "IST"; iFrame.
    iIntros "% % % % % %"; iIntros "IST".
    assert (NODSS: Seal.sealing "" (List.NoDup (List.map fst st_src0))).
    { unseal ""; eauto. }
    assert (NODDT: Seal.sealing "" (List.NoDup (List.map fst st_tgt0))).
    { unseal ""; eauto. }
    
    steps_l. iDestruct "ASM" as "[P [[-> TID] ->]]". hss. steps_l.
    steps_r. hss. steps_r.
    iApply isim_base.
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s.
    iApply "CIH".
    iFrame.
    iIntros (nths st_s st_t NODS1 NODD1) "IST TID GINV".
    iPoseProof ("SIM" $! nths _ _ NODS1 NODD1 with "IST TID GINV") as "SIM".
    iApply (isim_flag_mon with "SIM"); eauto.
    Unshelve. all: revert NODSS NODDT; unseal ""; ss.
  (*FAST*)Qed.

  Lemma wsim_yield_tgt_uu r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t ∗
    (∀ nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗
      wsim fl_s fl_t Ist None υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist None υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, (HMod.sandbox scp_t (interp_smod ginv spc Sch.yield)) >>= k_t).
  Proof.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "SIM P".
    iApply isim_nodup. iIntros (? ? ? ?). hss.
    rewrite /Sch.yield; unseal "Sch".
    (* iApply isim_reset. *)
    iStopProof.
    revert nths.
    combine_quant NODS; combine_quant NODD.
    combine_quant st_s. combine_quant st_t. combine_quant ps. combine_quant pt.
    eapply isim_coind.
    iIntros (g' [pt [ps [st_t' [st_s' [NODD [NODS nths']]]]]]) "%MON [[[IST SIM] P] #CIH]". s.

    unfold_iter_r.
    steps_r. destruct q.
    { steps_r. iPoseProof ("SIM" $! nths' _ _ NODS NODD with "IST P") as "SIM".
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>"; iApply MON; ss. }
    }

    steps_r.
    unfold_iter_l; steps_l.
    force_l false; steps_l. iDestruct "GRT" as "[P' [[-> TID] _]]".
    forces_l. iFrame. iSplit; eauto.
    iApply isim_progress.
    steps_l.

    iApply isim_call. iSplitL "IST"; iFrame.
    iIntros "% % % % % %"; iIntros "IST".
    assert (NODSS: Seal.sealing "" (List.NoDup (List.map fst st_src0))).
    { unseal ""; eauto. }
    assert (NODDT: Seal.sealing "" (List.NoDup (List.map fst st_tgt0))).
    { unseal ""; eauto. }

    steps_l. iDestruct "ASM" as "[P' [[-> TID] ->]]". hss. steps_l.
    steps_r. forces_r. iFrame; iSplit; eauto. steps_r. hss. steps_r.
    iApply isim_base.
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s.
    iApply "CIH".
    iFrame.
    iIntros (nths st_s st_t NODS1 NODD1) "IST GINV".
    iPoseProof ("SIM" $! nths _ _ NODS1 NODD1 with "IST GINV") as "SIM".
    iApply (isim_flag_mon with "SIM"); eauto.
    Unshelve. all: revert NODSS NODDT; unseal ""; ss.
  (*FAST*)Qed.

  Lemma wsim_yield_tgt_uv r g scp_s scp_t ginv_s ginv_t spc_s spc_t spc_user_s spc_user_t k_s k_t
      (SchInSpcs : spc_incl (SchAS.spc υ spc_user_s) spc_s)
      (SchInSpct : spc_incl (SchAS.spc ν spc_user_t) spc_t)
      `{υ > ν} :
    Ist nths st_s st_t ∗
    (∀ nths st_s st_t
        (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗
      wsim fl_s fl_t Ist (Some false) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, (HMod.sandbox scp_s (interp_smod ginv_s spc_s Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (Some false) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv_s spc_s Sch.yield)) >>= k_s)
      (st_t, (HMod.sandbox scp_t (interp_smod ginv_t spc_t Sch.yield)) >>= k_t).
  Proof.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "SIM P".
    iApply isim_nodup. iIntros (? ? ? ?). hss.
    rewrite /Sch.yield; unseal "Sch".
    (* iApply isim_reset. *)
    iStopProof.
    revert nths.
    combine_quant NODS; combine_quant NODD.
    combine_quant st_s. combine_quant st_t. combine_quant ps. combine_quant pt.
    eapply isim_coind.
    iIntros (g' [pt [ps [st_t' [st_s' [NODD [NODS nths']]]]]]) "%MON [[[IST SIM] P] #CIH]". s.

    unfold_iter_r.
    steps_r. destruct q.
    { steps_r. iPoseProof ("SIM" $! nths' _ _ NODS NODD with "IST P") as "SIM".
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>"; iApply MON; ss. }
    }

    steps_r.
    unfold_iter_l; steps_l.
    force_l false; steps_l. iDestruct "GRT" as "[P' [[-> TID] _]]".
    iDestruct "P" as "[O [W W']]"; iPoseProof ("W'" with "P'") as "> P".
    forces_l. iFrame. iSplit; eauto.
    iApply isim_progress.
    steps_l.

    iApply isim_call. iSplitL "IST"; iFrame.
    iIntros "% % % % % %"; iIntros "IST".
    assert (NODSS: Seal.sealing "" (List.NoDup (List.map fst st_src0))).
    { unseal ""; eauto. }
    assert (NODDT: Seal.sealing "" (List.NoDup (List.map fst st_tgt0))).
    { unseal ""; eauto. }

    steps_l. iDestruct "ASM" as "[P' [[-> TID] ->]]". hss. steps_l.
    iPoseProof (wsim_ginv_split with "P'") as "> [U V]"; first eauto.
    steps_r. forces_r. iFrame; iSplit; eauto. steps_r. hss. steps_r.
    iApply isim_base.
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s.
    iApply "CIH".
    iFrame.
    iIntros (nths st_s st_t NODS1 NODD1) "IST GINV".
    iPoseProof ("SIM" $! nths _ _ NODS1 NODD1 with "IST GINV") as "SIM".
    iApply (isim_flag_mon with "SIM"); eauto.
    Unshelve. all: revert NODSS NODDT; unseal ""; ss.
  (*FAST*)Qed.

  Lemma wsim_yield_src r g scp_s ginv spc spc_user k_s i_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    wsim fl_s fl_t Ist t υ ν E r g R_s R_t RR true pt nths
      (st_s, k_s tt)
      (st_t, i_t)
    ⊢ wsim fl_s fl_t Ist t υ ν E r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, i_t).
  Proof.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; steps_l.
    force_l true; steps_l. iApply "SIM".
  Qed.

  Lemma wsim_spawn fn vargs args fn_spec (P : SAny.t → SAny.t → iProp Σ) (Q : SAny.t → SAny.t → SynDepO)
      r g scp_s scp_t ginv spc spc_user k_s k_t my_tid
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc)
      (CalleeInSpc : spc_user fn = Some fn_spec)
      (Spawnable : SchAS.fspec_spawnable υ fn_spec P Q) :
    Ist nths st_s st_t ∗
    tid_user my_tid ∗
    P vargs args ∗
    (∀ tid nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
        Ist nths st_s st_t
        -∗ tid_user my_tid
        -∗ token_th tid Q
        -∗ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s tid) (st_t, k_t tid))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.spawn (fn, vargs)))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.spawn (fn, args)))) >>= k_t).
  Proof.
    iIntros "(I & TID & P & SIM)". rewrite /Sch.spawn; unseal "Sch".
    steps_l. forces_l. iSplitL "P TID".
    { iExists (fn, vargs); iSplit; eauto.
      instantiate (1:=(fn, args)↑).
      instantiate (1:=(my_tid, args, vargs, P, Q, fn)).
      iFrame. iPureIntro. esplits; eauto. unfold find_fsp. rewrite CalleeInSpc. eauto.
    }
    steps_l. steps_r.
    
    iApply wsim_call. iSplitL "I"; iFrame.
    iIntros "% % % % % %"; iIntros "IST".
    assert (NODSS: Seal.sealing "" (List.NoDup (List.map fst st_s'))).
    { unseal ""; eauto. }
    assert (NODDT: Seal.sealing "" (List.NoDup (List.map fst st_t'))).
    { unseal ""; eauto. }
    
    steps_l. steps_r.
    iDestruct "ASM" as (vr) "[% [[%tid [[-> ->] TKN]] TID]]". hss. steps_r.
    revert NODSS NODDT; unseal ""; i.
    iApply ("SIM" $! _ nths' _ _ NODSS NODDT with "IST TID TKN").
  Qed.

  Lemma wsim_join tid (Q : SAny.t → SAny.t → SynDepO)
      r g scp_s scp_t ginv spc spc_user k_s k_t my_tid
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t ∗
    tid_user my_tid ∗
    token_th tid Q ∗
    (∀ nths st_s st_t vret ret (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
        Ist nths st_s st_t
        -∗ tid_user my_tid
        -∗ interp_cond (Q vret ret)
        -∗ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s vret) (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.join tid))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.join tid))) >>= k_t).
  Proof.
    iIntros "(IST & TID & TK & SIM)". rewrite /Sch.join; unseal "Sch".
    steps_l. force_l (tid, Q, my_tid). steps_l. force_l (tid↑). steps_l. force_l.
    iFrame; iSplit; eauto. steps_l.

    steps_r.
    
    iApply wsim_call. iSplitL "IST"; iFrame.
    iIntros "% % % % % %"; iIntros "IST".
    assert (NODSS: Seal.sealing "" (List.NoDup (List.map fst st_s'))).
    { unseal ""; eauto. }
    assert (NODDT: Seal.sealing "" (List.NoDup (List.map fst st_t'))).
    { unseal ""; eauto. }
    
    steps_l. iDestruct "ASM" as "(% & % & (% & % & % & Q) & TID)".
    subst; hss. steps_r. hss. steps_r. hss. step_r.
    revert NODSS NODDT; unseal ""; i.
    iApply ("SIM" $! nths' _ _ _ _ NODSS NODDT with "IST TID Q").
  Qed.
End wsim.

Ltac sch_yield_l :=
  norm with (iApply wsim_yield_src; try eassumption).

Ltac sch_yield_r :=
  norm with (first [
    (iApply wsim_yield_tgt_u0; try eassumption)
    | (iApply wsim_yield_tgt_uu; try eassumption)
    | (iApply wsim_yield_tgt_uv; try eassumption)]).

Ltac sch_spawn :=
  norm with (iApply wsim_spawn; try eassumption).

Ltac sch_join :=
  norm with (iApply wsim_join; try eassumption).

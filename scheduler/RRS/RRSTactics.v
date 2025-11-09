Require Import CRIS RRSHeader RRSA.
Require Import ITactics.
Require Import MSim WSim.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !rrsG}.

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

  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma wsim_yield_tgt
      (tid_res : bool)
      (E : coPset)
      (r g : rel)
      (img_s img_t img_s' img_t' : bool)
      (msk_s msk_t : string → bool)
      (scp_s scp_t : list string)
      (sp_s sp_t : string → option fspec)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (mtid stid ssch : nat) :
    (tid_res = false ∧
     sp_s RRSHdr.yield_global = None ∧
     sp_t RRSHdr.yield_global = None ∧
     E = ∅) ∨
    (tid_res = true ∧
     ∃ sp_user_s,
       sp_incl (RRSAS.sp sp_user_s E get_stid PYIP) sp_s ∧ img_s = true ∧
       sp_t RRSHdr.yield_global = None) ∨
    (tid_res = false ∧
    ∃ sp_user_s sp_user_t E_s E_t,
      sp_incl (RRSAS.sp sp_user_s E_s get_stid PYIP) sp_s ∧ img_s = true ∧
      sp_incl (RRSAS.sp sp_user_t E_t get_stid PYIP) sp_t ∧ img_t = true ∧
      (E_s ≡ E_t ∪ E) ∧ (E ## E_t)) →
    msk_s RRSHdr.yield_global →
    msk_t RRSHdr.yield_global →
    Ist st_src st_tgt ∗ (if tid_res then RRSAS.Tid mtid stid ssch else emp) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ (if tid_res then RRSAS.Tid mtid stid ssch else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s' sp_s ℛ𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s' sp_s ℛ𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans img_t' sp_t ℛ𝒴)) >>= k_t).
  Proof using.
    intros Hcase Hmsks Hmskt. iIntros "[IST [TID SIM]]".
    rewrite /RRS.yield_global; unseal "RRS".
    iStopProof.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH. iIntros "[IST [TID SIM]]".
    unfold_iterC_r. steps_r. destruct _q; cycle 1.
    { unfold_iterC_l. steps_l. force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { unfold_iterC_l. steps_l. force_l (Some false). steps_l.
      steps_r. by_coind CIH. iFrame.
    }
    unfold_iterC_l. steps_l. force_l (Some true). steps_l.
    steps_r.

    destruct Hcase as [Hcase|[Hcase|Hcase]]; des; subst.
    { rewrite Hcase0 Hcase1 /=.
      call "IST".
      steps_l. steps_r. hss. steps_l. steps_r.
      by_coind CIH. iFrame.
    }
    { replace (sp_s RRSHdr.yield_global) with (Some (RRSAS.yield_global_spec E)); cycle 1.
      { erewrite (proj2 Hcase0); et. rewrite /RRSAS.sp; unseal CRIS; et. }
      rewrite Hcase2.
      steps_l. force_l (mtid, stid, ssch). forces_l. iSplitL "TID"; iFrame; eauto.
      steps_l.
      call "IST".
      steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss. steps_l. steps_r.
      by_coind CIH. iFrame.
    }
    { replace (sp_s RRSHdr.yield_global) with (Some (RRSAS.yield_global_spec E_s)); cycle 1.
      { erewrite (proj2 Hcase0); et. unfold RRSAS.sp; unseal CRIS; et. }
      replace (sp_t RRSHdr.yield_global) with (Some (RRSAS.yield_global_spec E_t)); cycle 1.
      { erewrite (proj2 Hcase2); et. unfold RRSAS.sp; unseal CRIS; et. }
      steps_r. iDestruct "GRT" as "[[-> TID0] _]". iClear "TID". iRename "TID0" into "TID".
      force_l (_, _, _). forces_l. iFrame "TID". iSplit; eauto.
      call "IST".
      steps_l. hss. iDestruct "ASM" as "[[-> TID] _]". steps_l.
      steps_r. forces_r. iSplitL "TID"; et.
      steps_r.
      by_coind CIH. iFrame.
      hss. iFrame.
    }
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g (img_s img_s' : bool) (msk_s: _ → bool) scp_s sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s' sp_s ℛ𝒴)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /RRS.yield_global; unseal "RRS".
    unfold_iterC_l; steps_l.
    force_l None; steps_l. iApply "SIM".
  (*SLOW*)Qed.
End wsim.

Ltac clear_st :=
  hrepeat do 1 match goal with [st: alist key Any.t |- _] => clear st end.

Ltac clear_emp :=
  hrepeat do 1 match goal with [|- context[environments.Esnoc _ ?H (emp%I)]] => iClear H end.
  
Ltac rrs_yield_l :=
  norm_l with do 1 iApply wsim_yield_src.

Ltac rrs_auto :=
  hrepeat first [progress iFrame | iSplit; iFrame; et; []].

Ltac rrs_intros :=
  clear_st; iIntros (??); iIntrosFresh "IST"; iIntrosFresh "TID"; clear_emp.

Ltac rrs_yield_rr :=
  norm_r; iApply wsim_yield_tgt;
  [left; esplits; [refl|..]; et; try set_solver|et|et|rrs_auto; [..|try rrs_intros]].

Ltac rrs_yield_ir :=
  norm_r; iApply wsim_yield_tgt;
  [right; left; esplits; [refl|..]; et; try set_solver|et|et|rrs_auto; [..|try rrs_intros]].

Ltac rrs_yield_ii :=
  norm_r; iApply wsim_yield_tgt;
  [right; right; esplits; [refl|..]; et; try set_solver|et|et|rrs_auto; [..|try rrs_intros]].

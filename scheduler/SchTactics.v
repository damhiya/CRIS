Require Import CRIS SchHeader SchA.
Require Import ITactics.

Section wsim.
  Import SchAS.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Lemma wsim_yield_tgt (tid_res : bool) (E : coPset) (q : Qp)
      (r g : rel)
      (img_s img_t : bool)
      (msk_s msk_t : string → bool)
      (scp_s scp_t : list string)
      (sp_s sp_t : string → option fspec)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (my_tid : nat) :
    (tid_res = false ∧
     sp_s SchHdr.yield = None ∧
     sp_t SchHdr.yield = None ∧
     E = ∅ ∧
     q = 1%Qp (* unused value *)) ∨
    (tid_res = true ∧
     ∃ sp_user_s,
       sp_incl (SchAS.sp sp_user_s E q) sp_s ∧ img_s = true ∧
       sp_t SchHdr.yield = None) ∨
    (tid_res = true ∧
    ∃ sp_user_s sp_user_t E_s E_t q_s q_t,
      sp_incl (SchAS.sp sp_user_s E_s q_s) sp_s ∧ img_s = true ∧
      sp_incl (SchAS.sp sp_user_t E_t q_t) sp_t ∧ img_t = true ∧
      (E_s ≡ E_t ∪ E) ∧ (E ## E_t) ∧
      (q_s ≡ q_t + q)%Qp) →
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    Ist st_src st_tgt ∗ (if tid_res then tid_user q my_tid else emp) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ (if tid_res then tid_user q my_tid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        (st_tgt, k_t tt))
    ⊢ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴)) >>= k_s)
    (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hcase Hmsks Hmskt. iIntros "[IST [TID SIM]]".
    rewrite /Sch.yield; unseal "Sch".
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
    { replace (sp_s SchHdr.yield) with (Some (SchAS.yield_spec E q)); cycle 1.
      { erewrite (proj2 Hcase0); et. unfold sp; unseal CRIS; et. }
      rewrite Hcase2.
      forces_l. iSplitL "TID"; iFrame; eauto.
      steps_l.
      call "IST".
      steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss. steps_l. steps_r.
      by_coind CIH. iFrame.
    }
    { replace (sp_s SchHdr.yield) with (Some (SchAS.yield_spec E_s q_s)); cycle 1.
      { erewrite (proj2 Hcase0); et. unfold sp; unseal CRIS; et. }
      replace (sp_t SchHdr.yield) with (Some (SchAS.yield_spec E_t q_t)); cycle 1.
      { erewrite (proj2 Hcase2); et. unfold sp; unseal CRIS; et. }
      steps_r. iDestruct "GRT" as "[[-> TID0] _]".
      iPoseProof (tid_user_unique with "[TID TID0]") as "%"; iFrame; subst.
      forces_l. iSplitL "TID TID0".
      { do 2 (iSplit; et).
        iPoseProof (tid_user_merge with "[TID TID0]") as "TID"; iFrame.
        rewrite -Hcase6. et.
      }
      call "IST".
      steps_l. hss. iDestruct "ASM" as "[[-> TID] _]". steps_l.
      rewrite Hcase6.
      iPoseProof (tid_user_split with "[TID]") as "[TID0 TID]"; et.
      steps_r. forces_r. iSplitL "TID0"; et.
      steps_r. hss. steps_r.
      by_coind CIH. iFrame.
    }
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g img_s (msk_s: _ → bool) sc_s sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s 𝒴)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iterC_l; steps_l.
    force_l None; steps_l. iApply "SIM".
  (*SLOW*)Qed.

End wsim.

Ltac sch_yield_l :=
  norm_l with do 1 iApply wsim_yield_src.

Ltac sch_resolve :=
  esplits; et; try set_solver.

Ltac sch_auto :=
  hrepeat first [progress iFrame | iSplit; iFrame; et; []].

Ltac sch_intros :=
  iIntros (??); iIntrosFresh "IST"; iIntrosFresh "TID";
  try match goal with [|- context[environments.Esnoc _ ?H (emp%I)]] => iClear H end.

Ltac sch_yield_rr :=
  norm_r with do 1 iApply wsim_yield_tgt;
  [left; sch_resolve|et|et|sch_auto; [..|try sch_intros]].
  
Ltac sch_yield_ir :=
  norm_r with do 1 iApply wsim_yield_tgt;
  [right; left; sch_resolve|et|et|sch_auto; [..|try sch_intros]].

Ltac sch_yield_ii :=
  norm_r with do 1 iApply wsim_yield_tgt;
  [right; right; sch_resolve|et|et|sch_auto; [..|try sch_intros]].

Section FancyReal.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : ist_type Σ).
  Context (R_s R_t : Type).

  Context (r g : rel).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_s st_t : state).

  Local Notation sim Ep r g := (wsim fl_s fl_t Ist Ep r g R_s R_t).

  Lemma wsim_real_peek_both
    X_s X_t (cond_s: X_s → _) (cond_t: X_t → _) k_s k_t
    img_s img_t (msk_s msk_t: _ → bool) scp_s scp_t
    :
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    Ist st_s st_t ∗
    (□ ∀ x_s, ∃ x_t, cond_s x_s ==∗ cond_t x_t ∗ (cond_t x_t ==∗ cond_s x_s)) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ 
      sim (∅,∅) r g RR true true (st_src, k_s ()) (st_tgt, k_t ()))
    ⊢
    sim (∅,∅) r g RR ps pt
      (st_s, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_none (real_peek cond_s 𝒴)) >>= k_s)
      (st_t, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (real_peek cond_t 𝒴)) >>= k_t).
  Proof.
    i. iIntros "H". iApply wsim_reset. iStopProof.
    revert st_s. combine_quant st_t.
    eapply wsim_coind. intros g' Hg CIH [st_t st_s].
    iIntros "[IST [#COND SIM]] /=". destruct_quant CIH.
    
    rewrite /real_peek. unfold_iter_l. steps_l. unfold_iter_r. steps_r.
    sch_yield_rr. sch_yield_l.
    steps_r. force_l _q. destruct _q; cycle 1; steps_l; steps_r.
    { iApply wsim_mono_knowledge; cycle 2.
      { iApply ("SIM" with "[IST]"); et. }
      { et. }
      { i. rewrite Hg. et. }
    }

    ru_r. iIntros (?) "UPD".
    ru_l (Own pr)%I. iSplitL "UPD".
    { iIntros (?) "CS". iDestruct ("COND" $! x) as "[% H]".
      iMod ("H" with "CS") as "[CT R]".
      iMod ("UPD" with "CT") as "[PR CT]".
      iMod ("R" with "CT") as "R". iFrame. et.
    }
    iIntros "PR"; force_r; iFrame.

    steps_l; steps_r.
    by_coind CIH; iFrame; et.
  Unshelve. all: exact 0.
  Qed.

  Lemma wsim_real_peek_tgt
    {X} cond (x: X) E (tid_res : bool) q my_tid
    k_s k_t img_s img_t (msk_s msk_t: _ → bool) scp_s scp_t sp_s
    I
    :
    (tid_res = false ∧
     sp_s SchHdr.yield = None ∧
     E = ∅ ∧
     q = 1%Qp (* unused value *)) ∨
    (tid_res = true ∧
     ∃ sp_user_s,
       sp_incl (SchAS.sp sp_user_s E q) sp_s ∧ img_s = true) →
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    I ∗ Ist st_s st_t ∗ (if tid_res then SchAS.tid_user q my_tid else emp) ∗
    (□ (∀ st_src st_tgt,
        I ∗ Ist st_src st_tgt ∗ (if tid_res then SchAS.tid_user q my_tid else emp) ==∗
        cond x ∗ (cond x ==∗ I ∗ Ist st_src st_tgt ∗ (if tid_res then SchAS.tid_user q my_tid else emp)))) ∗
    (∀ st_src st_tgt,
     I ∗ Ist st_src st_tgt ∗ (if tid_res then SchAS.tid_user q my_tid else emp) -∗
     sim (E,E) r g RR true true
        (st_src, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴) >>= k_s)
        (st_tgt, k_t ()))
    ⊢
    sim (E,E) r g RR ps pt
      (st_s, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴) >>= k_s)
      (st_t, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (real_peek cond 𝒴)) >>= k_t).
  Proof.
    i. iIntros "H". iApply wsim_reset. iStopProof.
    revert st_s. combine_quant st_t.
    eapply wsim_coind. intros g' Hg CIH [st_t st_s].
    iIntros "[I [IST [TID [#COND SIM]]]] /=". destruct_quant CIH.
    
    rewrite /real_peek. unfold_iter_r. steps_r.
    iApply wsim_yield_tgt; [|et|et|try (sch_auto; sch_intros)].
    { des; subst; [left|right;left]; et. }
    steps_r. destruct _q; cycle 1; steps_r.
    { iApply wsim_mono_knowledge; cycle 2.
      { iApply ("SIM" with "[I IST TID]"); et; iFrame. }
      { et. }
      { i. rewrite Hg. et. }
    }

    ru_r. iIntros (?) "UPD".
    iMod ("COND" with "[I IST TID]") as "[C R]"; iFrame.
    iMod ("UPD" with "C") as "[PR C]".
    iMod ("R" with "C") as "[I [IST TID]]".
    force_r; iFrame. steps_r.
    by_coind CIH. iFrame. et.
  Qed.

End FancyReal.

Ltac fancy_peek_rr :=
  norm_r with do 1 iApply wsim_real_peek_tgt;
  [left; sch_resolve|et|et|sch_auto; [..|try sch_intros]].

Ltac fancy_peek_ir :=
  norm_r with do 1 iApply wsim_real_peek_tgt;
  [right; sch_resolve|et|et|sch_auto; [..|try sch_intros]].

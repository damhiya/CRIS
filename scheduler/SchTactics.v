Require Import CRIS SchHeader SchA.
Require Import ITactics.

Section wsim.
  Import SchAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

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
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  Lemma wsim_yield_sp E_s r g (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid :
    sp_incl (SchAS.sp E_s sp_user) sp →
    msk_s SchHdr.yield → msk_t SchHdr.yield →
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    (∀ nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODT: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗ tid_user my_tid -∗
(* <<<<<<< HEAD *)
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, (SB.sandbox msk_s sc_s (SModTr.trans sp Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (SB.sandbox msk_s sc_s (SModTr.trans sp Sch.yield)) >>= k_s)
      (st_t, (SB.sandbox msk_t sc_t (PModTr.trans Sch.yield)) >>= k_t).
(* ======= *)
(*       wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps true nths *)
(*         (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp Sch.yield)) >>= k_s) *)
(*         (st_t, k_t tt)) *)
(*     ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths *)
(*       (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp Sch.yield)) >>= k_s) *)
(*       (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans Sch.yield)) >>= k_t). *)
(* >>>>>>> master *)
  Proof using.
    i. rewrite !WSim.wsim_eq /WSim.wsim_def.
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
    destruct_quant.

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

    call "IST".
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
    Unshelve. all: eauto.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ss E_s Ep r g (msk_s msk_t : _ → bool) sc_s sc_t sp_s sp_t sp_user_s sp_user_t k_s k_t :
    sp_incl (SchAS.sp E_s sp_user_s) sp_s →
    sp_incl (SchAS.sp E_s sp_user_t) sp_t →
    msk_s SchHdr.yield → msk_t SchHdr.yield →
    Ist nths st_s st_t ∗
    (∀ nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗
      wsim fl_s fl_t Ist Ep r g R_s R_t RR ps true nths
        (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist Ep r g R_s R_t RR ps pt nths
      (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
      (st_t, (HModTr.sandbox msk_t sc_t (SModTr.trans sp_t Sch.yield)) >>= k_t).
  Proof using.
    i. rewrite !WSim.wsim_eq /WSim.wsim_def.
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
    destruct_quant.

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

    call "IST".
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
    Unshelve. all: eauto.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_uv E_s E_s' E_t r g (msk_s msk_t : _ → bool) sc_s sc_t
      sp_s sp_t sp_user_s sp_user_t k_s k_t :
    sp_incl (SchAS.sp E_s sp_user_s) sp_s →
    sp_incl (SchAS.sp E_t sp_user_t) sp_t →
    msk_s SchHdr.yield → msk_t SchHdr.yield →
    E_s = E_t ∪ E_s' →
    Ist nths st_s st_t ∗
    (∀ nths st_s st_t
        (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗
      wsim fl_s fl_t Ist (Some (E_s', E_s')) r g R_s R_t RR ps true nths
        (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (Some (E_s', E_s')) r g R_s R_t RR ps pt nths
      (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
      (st_t, (HModTr.sandbox msk_t sc_t (SModTr.trans sp_t Sch.yield)) >>= k_t).
  Proof using.
    i. rewrite !WSim.wsim_eq /WSim.wsim_def.
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
    destruct_quant.

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
    iMod (wsim_ginv_merge with "[P P']") as "[P %]"; iFrame.

    forces_l. iSplitL "P TID"; eauto.
    { iFrame. iSplit; ss. }
    iApply isim_progress.
    steps_l.

    call "IST".
    steps_l. iDestruct "ASM" as "[P' [[-> TID] ->]]". hss. steps_l.
    iPoseProof (wsim_ginv_split with "P'") as "[U V]"; ss.
    steps_r. forces_r. iFrame; iSplit; eauto. steps_r. hss. steps_r.
    iApply isim_base.
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s.
    iApply "CIH".
    iFrame.
    iIntros (nths st_s st_t NODS1 NODD1) "IST GINV".
    iPoseProof ("SIM" $! nths _ _ NODS1 NODD1 with "IST GINV") as "SIM".
    iApply (isim_flag_mon with "SIM"); eauto.
    Unshelve. all: eauto.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g (msk_s : _ → bool) sc_s sp k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt nths (st_s, k_s tt) (st_t, i_t)
    ⊢ wsim fl_s fl_t Ist Ep r g R_s R_t RR ps pt nths
      (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp Sch.yield)) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; steps_l.
    force_l true; steps_l. iApply "SIM".
  Qed.

  Lemma wsim_spawn E_s fn vargs args fn_spec
      (P : SAny.t → SAny.t → iProp Σ) (Q : SAny.t → SAny.t → SynDepO)
      r g (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid :
    sp_incl (SchAS.sp E_s sp_user) sp →
    sp_user fn = Some fn_spec →
    SchAS.fspec_spawnable E_s fn_spec P Q →
    msk_s SchHdr.spawn  → msk_t SchHdr.spawn →
    Ist nths st_s st_t ∗
    tid_user my_tid ∗
    P vargs args ∗
    (∀ tid nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
        Ist nths st_s st_t
        -∗ tid_user my_tid
        -∗ token_th tid Q
        -∗ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR true true nths
            (st_s, k_s tid) (st_t, k_t tid))
    ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths
      (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp (Sch.spawn (fn, vargs)))) >>= k_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (Sch.spawn (fn, args)))) >>= k_t).
  Proof using.
    iIntros (??CalleeInSp???) "(I & TID & P & SIM)". rewrite /Sch.spawn; unseal "Sch".
    steps_l. forces_l. iSplitL "P TID".
    { iExists (fn, vargs); iSplit; eauto.
      instantiate (1:=(fn, args)↑).
      instantiate (1:=(my_tid, args, vargs, P, Q, fn)).
      iFrame. iPureIntro. esplits; eauto. unfold find_fsp. rewrite CalleeInSp. eauto.
    }
    steps_l. steps_r.

    call "I".
    steps_l. steps_r. replace (E_s ∖ E_s ∪ E_s) with E_s by set_solver. 
    iDestruct "ASM" as (vr) "[% [[%tid [[-> ->] TKN]] TID]]". hss. steps_r.
    iApply ("SIM" $! _ nths' _ _ NODS NODD with "IST TID TKN").
  Qed.

  Lemma wsim_join E_s tid (Q : SAny.t → SAny.t → SynDepO)
      r g (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid
      (SchInSp : sp_incl (SchAS.sp E_s sp_user) sp) :
    msk_s SchHdr.join  → msk_t SchHdr.join →
    Ist nths st_s st_t ∗
    tid_user my_tid ∗
    token_th tid Q ∗
    (∀ nths st_s st_t vret ret (NODS: List.NoDup (List.map fst st_s)) (NODD: List.NoDup (List.map fst st_t)),
        Ist nths st_s st_t
        -∗ tid_user my_tid
        -∗ interp_cond (Q vret ret)
        -∗ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR true true nths
            (st_s, k_s vret) (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths
      (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp (Sch.join tid))) >>= k_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (Sch.join tid))) >>= k_t).
  Proof using.
    i. iIntros "(IST & TID & TK & SIM)". rewrite /Sch.join; unseal "Sch".
    steps_l. force_l (tid, Q, my_tid). steps_l. force_l (tid↑). steps_l. force_l.
    iFrame; iSplit; eauto. steps_l.

    steps_r.

    call "IST".
    steps_l. iDestruct "ASM" as "(% & % & (% & % & % & Q) & TID)".
    subst; hss. steps_r. hss. steps_r. hss. step_r.
    replace (E_s ∖ E_s ∪ E_s) with E_s by set_solver.
    iApply ("SIM" $! nths' _ _ _ _ NODS NODD with "IST TID Q").
  Qed.
End wsim.

Ltac solve_sch_sp :=
  match goal with
  | H : sp_incl (SchAS.sp ?u ?user) ?sp |- sp_incl (SchAS.sp ?u _) ?sp => exact H
  end.

Ltac sch_yield_r_aux :=
  match goal with
  | |- context [wsim _ _ _] =>
    first [
      iApply wsim_yield_sp |
      iApply wsim_yield_tgt_uv; [eauto|eauto|eauto|eauto|try set_solver|idtac]
    ];
    try solve_sch_sp;
    eauto
  end.

Ltac sch_yield_l :=
  norm with (do 1 (iApply wsim_yield_src; try solve_sch_sp; try prove_sb_cond)).

Ltac sch_yield_r :=
  norm with (do 1 sch_yield_r_aux).

Ltac sch_spawn :=
  norm with (do 1 (iApply wsim_spawn; try solve_sch_sp; try prove_sb_cond)).

Ltac sch_join :=
  norm with (do 1 (iApply wsim_join; try solve_sch_sp; try prove_sb_cond)).

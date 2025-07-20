Require Import CRIS SchHeader SchA.
Require Import ITactics.

Section wsim.
  Import SchAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).
  
  Lemma wsim_yield_tgt (E: coPset) (q: Qp)
    r g (img_s img_t: bool) (msk_s msk_t : _ → bool) sc_s sc_t sp_s sp_t k_s k_t my_tid
    (VALID: (sp_s SchHdr.yield = None ∧
             sp_t SchHdr.yield = None ∧
             E = ∅ ∧
             q = 1%Qp (* unused value *))
            ∨
            (sp_s SchHdr.yield = Some (SchAS.yield_spec E q) ∧ img_s = true ∧
             sp_t SchHdr.yield = None)
            ∨
            (∃ E_s E_t q_s q_t,
             sp_s SchHdr.yield = Some (SchAS.yield_spec E_s q_s) ∧ img_s = true ∧
             sp_t SchHdr.yield = Some (SchAS.yield_spec E_t q_t) ∧ img_t = true ∧
             (E_s ≡ E_t ∪ E) ∧ (E ## E_t) ∧
             (q_s ≡ q_t + q)%Qp))
    (MSK_S: msk_s SchHdr.yield)
    (MSK_T: msk_t SchHdr.yield)
    :
    Ist nths st_s st_t ∗ (if is_some (sp_s SchHdr.yield) then tid_user q my_tid else emp) ∗
    (∀ nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODT: List.NoDup (List.map fst st_t)),
      Ist nths st_s st_t -∗ (if is_some (sp_s SchHdr.yield) then tid_user q my_tid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps true nths
        (st_s, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt nths
      (st_s, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
      (st_t, (SB.sandbox img_t msk_t sc_t (SModTr.trans sp_t Sch.yield)) >>= k_t).
  Proof.
    i. iIntros "[IST [TID SIM]]".
    rewrite /Sch.yield; unseal "Sch".
    iStopProof.
    revert nths.
    combine_quant st_s. combine_quant st_t. combine_quant ps. combine_quant pt.
    eapply wsim_coind.
    iIntros (g' [pt [ps [st_t [st_s nths]]]]). destruct_quant.
    iIntros "[IST [TID SIM]] % #CIH".
    unfold_iter_r.
    steps_r. destruct q0.
    { steps_r. iApply wsim_nodup. iIntros (? ?).
      iPoseProof ("SIM" $! _ _ _ NODS NODT with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>". iApply H; ss. }
    }
      
    steps_r.
    unfold_iter_l; steps_l.
    force_l false; steps_l.
    iApply wsim_progress.

    destruct VALID as [VALID|[VALID|VALID]]; des; subst.
    - rewrite VALID VALID0. s.
      call "IST".
      steps_l. steps_r. hss. steps_l. steps_r.
      iApply wsim_base. iIntros "I". iApply "CIH". iFrame.
      iIntros (nths0 st_s0 st_t0 NODS1 NODT1) "IST TID".
      iPoseProof ("SIM" $! nths0 _ _ NODS1 NODT1 with "IST TID") as "SIM".
      iApply (wsim_flag_mon with "SIM"); et.
    - rewrite VALID VALID1. s.
      forces_l. iSplitL "TID"; iFrame; eauto.
      steps_l.
      call "IST".
      steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss. steps_l.
      steps_r. hss. steps_r.
      iApply wsim_base. iIntros "I". iApply "CIH".
      replace (E ∖ E ∪ E) with E by set_solver. iFrame.
      iIntros (nths0 st_s0 st_t0 NODS1 NODT1) "IST TID".
      iPoseProof ("SIM" $! nths0 _ _ NODS1 NODT1 with "IST TID") as "SIM".
      iApply (wsim_flag_mon with "SIM"); et.
    - rewrite VALID VALID1. s.
      steps_r. iDestruct "GRT" as "[[-> TID0] _]".
      iPoseProof (tid_user_unique with "[TID TID0]") as "%"; iFrame; subst.
      forces_l. iSplitL "TID TID0".
      { do 2 (iSplit; et).
        iPoseProof (tid_user_merge with "[TID TID0]") as "TID"; iFrame.
        rewrite VALID5. et.
      }
      simpl WP_space.
      call "IST".
      steps_l. hss. iDestruct "ASM" as "[[-> TID] _]". steps_l.
      iPoseProof (tid_user_split with "[TID]") as "[TID0 TID]"; et.
      steps_r. forces_r. iSplitL "TID0"; et.
      steps_r. hss. steps_r.
      iApply wsim_base. iIntros "I". iApply "CIH". iFrame.
      iIntros (nths0 st_s0 st_t0 NODS1 NODT1) "IST TID".
      iPoseProof ("SIM" $! nths0 _ _ NODS1 NODT1 with "IST TID") as "SIM".
      iApply (wsim_flag_mon with "SIM"); et.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g img_s (msk_s: _ → bool) sc_s sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt nths (st_s, k_s tt) (st_t, i_t)
    ⊢ wsim fl_s fl_t Ist Ep r g R_s R_t RR ps pt nths
      (st_s, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; steps_l.
    force_l true; steps_l. iApply "SIM".
  (*SLOW*)Qed.

  (* Lemma wsim_spawn E_s fn vargs args fn_spec *)
  (*     (P : SAny.t → SAny.t → iProp Σ) (Q : SAny.t → SAny.t → SynDepO) *)
  (*     r g img_s img_t (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid : *)
  (*   sp_incl (SchAS.sp E_s sp_user) sp → *)
  (*   sp_user fn = Some fn_spec → *)
  (*   SchAS.fspec_spawnable E_s fn_spec P Q → *)
  (*   msk_s SchHdr.spawn  → msk_t SchHdr.spawn → *)
  (*   Ist nths st_s st_t ∗ *)
  (*   tid_user my_tid ∗ *)
  (*   P vargs args ∗ *)
  (*   (∀ tid nths st_s st_t (NODS: List.NoDup (List.map fst st_s)) (NODT: List.NoDup (List.map fst st_t)), *)
  (*       Ist nths st_s st_t *)
  (*       -∗ tid_user my_tid *)
  (*       -∗ token_th tid Q *)
  (*       -∗ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR true true nths *)
  (*           (st_s, k_s tid) (st_t, k_t tid)) *)
  (*   ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths *)
  (*     (st_s, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s (Sch.spawn (fn, vargs)))) >>= k_s) *)
  (*     (st_t, (SB.sandbox img_t msk_t sc_t (PModTr.trans sp_t (Sch.spawn (fn, args)))) >>= k_t). *)
  (* Proof using. *)
  (*   iIntros (??CalleeInSp???) "(I & TID & P & SIM)". rewrite /Sch.spawn; unseal "Sch". *)
  (*   steps_l. forces_l. iSplitL "P TID". *)
  (*   { iExists (fn, vargs); iSplit; eauto. *)
  (*     instantiate (1:=(fn, args)↑). *)
  (*     instantiate (1:=(my_tid, args, vargs, P, Q, fn)). *)
  (*     iFrame. iPureIntro. esplits; eauto. unfold find_fsp. rewrite CalleeInSp. eauto. *)
  (*   } *)
  (*   steps_l. steps_r. *)

  (*   call "I". *)
  (*   steps_l. steps_r. replace (E_s ∖ E_s ∪ E_s) with E_s by set_solver.  *)
  (*   iDestruct "ASM" as (vr) "[% [[%tid [[-> ->] TKN]] TID]]". hss. steps_r. *)
  (*   iApply ("SIM" $! _ nths' _ _ NODS NODT with "IST TID TKN"). *)
  (* Qed. *)

  (* Lemma wsim_join E_s tid (Q : SAny.t → SAny.t → SynDepO) *)
  (*     r g (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid *)
  (*     (SchInSp : sp_incl (SchAS.sp E_s sp_user) sp) : *)
  (*   msk_s SchHdr.join  → msk_t SchHdr.join → *)
  (*   Ist nths st_s st_t ∗ *)
  (*   tid_user my_tid ∗ *)
  (*   token_th tid Q ∗ *)
  (*   (∀ nths st_s st_t vret ret (NODS: List.NoDup (List.map fst st_s)) (NODT: List.NoDup (List.map fst st_t)), *)
  (*       Ist nths st_s st_t *)
  (*       -∗ tid_user my_tid *)
  (*       -∗ interp_cond (Q vret ret) *)
  (*       -∗ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR true true nths *)
  (*           (st_s, k_s vret) (st_t, k_t ret)) *)
  (*   ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths *)
  (*     (st_s, (HModTr.sandbox msk_s sc_s (SModTr.trans sp (Sch.join tid))) >>= k_s) *)
  (*     (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (Sch.join tid))) >>= k_t). *)
  (* Proof using. *)
  (*   i. iIntros "(IST & TID & TK & SIM)". rewrite /Sch.join; unseal "Sch". *)
  (*   steps_l. force_l (tid, Q, my_tid). steps_l. force_l (tid↑). steps_l. force_l. *)
  (*   iFrame; iSplit; eauto. steps_l. *)

  (*   steps_r. *)

  (*   call "IST". *)
  (*   steps_l. iDestruct "ASM" as "(% & % & (% & % & % & Q) & TID)". *)
  (*   subst; hss. steps_r. hss. steps_r. hss. step_r. *)
  (*   replace (E_s ∖ E_s ∪ E_s) with E_s by set_solver. *)
  (*   iApply ("SIM" $! nths' _ _ _ _ NODS NODT with "IST TID Q"). *)
  (* Qed. *)
End wsim.

(* Ltac solve_sch_sp := *)
(*   match goal with *)
(*   | H : sp_incl (SchAS.sp ?u ?user) ?sp |- sp_incl (SchAS.sp ?u _) ?sp => exact H *)
(*   end. *)

(* Ltac sch_yield_r_aux := *)
(*   match goal with *)
(*   | |- context [wsim _ _ _] => *)
(*     first [ *)
(*       iApply wsim_yield_sp | *)
(*       iApply wsim_yield_tgt_uv; [eauto|eauto|eauto|eauto|try set_solver|idtac] *)
(*     ]; *)
(*     try solve_sch_sp; *)
(*     eauto *)
(*   end. *)

Ltac sch_yield_l :=
  norm_l; iApply wsim_yield_src.

Ltac sch_yield_r :=
  norm_r; iApply wsim_yield_tgt; [s|..]; et.

(* Ltac sch_spawn := *)
(*   norm with (do 1 (iApply wsim_spawn; try solve_sch_sp; try prove_sb_cond)). *)

(* Ltac sch_join := *)
(*   norm with (do 1 (iApply wsim_join; try solve_sch_sp; try prove_sb_cond)). *)

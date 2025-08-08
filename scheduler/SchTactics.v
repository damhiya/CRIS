Require Import CRIS SchHeader SchA.
Require Import ITactics.

Section wsim.
  Import SchAS.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_src st_tgt : state).

  Lemma wsim_yield_tgt (src_some : bool) (E : coPset) (q : Qp)
      (r g : rel)
      (img_s img_t : bool)
      (msk_s msk_t : string → bool)
      (scp_s scp_t : list string)
      (sp_s sp_t : string → option fspec)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (my_tid : nat) :
    (src_some = false ∧
     sp_s SchHdr.yield = None ∧
     sp_t SchHdr.yield = None ∧
     E = ∅ ∧
     q = 1%Qp (* unused value *)) ∨
    (src_some = true ∧
     ∃ sp_user_s,
       sp_incl (SchAS.sp sp_user_s E q) sp_s ∧ img_s = true ∧
       sp_t SchHdr.yield = None) ∨
    (src_some = true ∧
    ∃ sp_user_s sp_user_t E_s E_t q_s q_t,
      sp_incl (SchAS.sp sp_user_s E_s q_s) sp_s ∧ img_s = true ∧
      sp_incl (SchAS.sp sp_user_t E_t q_t) sp_t ∧ img_t = true ∧
      (E_s ≡ E_t ∪ E) ∧ (E ## E_t) ∧
      (q_s ≡ q_t + q)%Qp) →
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    Ist nths st_src st_tgt ∗ (if src_some then tid_user q my_tid else emp) ∗
    (∀ nths st_src st_tgt (NODS: List.NoDup (List.map fst st_src)) (NODT: List.NoDup (List.map fst st_tgt)),
      Ist nths st_src st_tgt -∗ (if src_some then tid_user q my_tid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true nths
        (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
        (st_tgt, k_t tt))
    ⊢ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt nths
    (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
    (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans sp_t Sch.yield)) >>= k_t).
  Proof.
    intros Hcase Hmsks Hmskt. iIntros "[IST [TID SIM]]".
    rewrite /Sch.yield; unseal "Sch".
    iStopProof.
    revert nths.
    combine_quant st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind.
    iIntros (g' [pt [ps [st_t [st_s nths]]]]). destruct_quant.
    iIntros "[IST [TID SIM]] %Hg #CIH".
    unfold_iter_r. steps_r. destruct _q; cycle 1.
    { unfold_iter_l. steps_l. force_l (Some false). steps_l.
      steps_r. iApply wsim_nodup. iIntros (? ?).
      iPoseProof ("SIM" $! _ _ _ NODS NODT with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { unfold_iter_l. steps_l. force_l (Some false). steps_l.
      steps_r. by_coind "CIH". iFrame.
    }
    unfold_iter_l. steps_l. force_l (Some true). steps_l.
    steps_r.

    destruct Hcase as [Hcase|[Hcase|Hcase]]; des; subst.
    { rewrite Hcase0 Hcase1 /=.
      call "IST".
      steps_l. steps_r. hss. steps_l. steps_r.
      by_coind "CIH". iFrame.
    }
    { replace (sp_s SchHdr.yield) with (Some (SchAS.yield_spec E q)); cycle 1.
      { erewrite (proj2 Hcase0); et. unfold sp; unseal CRIS; et. }
      rewrite Hcase2.
      forces_l. iSplitL "TID"; iFrame; eauto.
      steps_l.
      call "IST".
      steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss. steps_l. steps_r.
      by_coind "CIH". iFrame.
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
      by_coind "CIH". iFrame.
    }
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g img_s (msk_s: _ → bool) sc_s sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt nths (st_src, k_s tt) (st_tgt, i_t)
    ⊢ wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt nths
      (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; steps_l.
    force_l None; steps_l. iApply "SIM".
  (*SLOW*)Qed.

  (* Lemma wsim_sch_spawn
      (fn : string) (args : SAny.t)
      (src_some : bool) (E : coPset) (q : Qp)
      (r g : rel)
      (img_s img_t : bool)
      (msk_s msk_t : string → bool)
      (scp_s scp_t : list string)
      (sp_s sp_t : string → option fspec)
      (k_s : nat → itree crisE R_s)
      (k_t : nat → itree crisE R_t)
      (my_tid : nat) :
    (src_some = false ∧
     sp_s SchHdr.spawn = None ∧
     sp_t SchHdr.spawn = None ∧
     E = ∅ ∧
     q = 1%Qp (* unused value *)) ∨
    (src_some = true ∧
     ∃ sp_user_s,
       sp_incl (SchAS.sp sp_user_s E q) sp_s ∧ img_s = true ∧
       sp_t SchHdr.spawn = None) ∨
    (src_some = true ∧
    ∃ sp_user_s sp_user_t E_s E_t q_s q_t,
      sp_incl (SchAS.sp sp_user_s E_s q_s) sp_s ∧ img_s = true ∧
      sp_incl (SchAS.sp sp_user_t E_t q_t) sp_t ∧ img_t = true ∧
      (E_s ≡ E_t ∪ E) ∧ (E ## E_t) ∧
      (q_s ≡ q_t + q)%Qp) →
    msk_s SchHdr.spawn →
    msk_t SchHdr.spawn →
    Ist nths st_src st_tgt ∗ (if src_some then tid_user q my_tid else emp) ∗
    (∀ nths st_src st_tgt tid,
      Ist nths st_src st_tgt -∗ (if src_some then tid_user q my_tid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true nths
        (st_src, k_s tid)
        (st_tgt, k_t tid)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt nths
      (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s (Sch.spawn (fn, args)))) >>= k_s)
      (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans sp_t (Sch.spawn (fn, args)))) >>= k_t).
  Proof.
    iIntros (Hcase ??) "[IST [TID KTR]]".
    rewrite /Sch.spawn; steps_l; steps_r.
    destruct Hcase as [[-> [-> [-> [? ?]]]] | Hcase].
    { call "IST"; steps_l; hss; steps_r; hss_r; steps_r.
      iApply ("KTR" with "IST"); iFrame.
    }
    destruct Hcase as [[-> [sp_user_s [[? Hincl] [-> ->]]]] | Hcase].
    { hexploit (Hincl SchHdr.spawn); [|intros ->].
      { rewrite /sp; unseal CRIS; ss. }
      s. force_l (my_tid, _, _). forces_l. iFrame "TID". iSplitL "".
      { iExists _; iSplit; first done. iExists _, _, _.
    } *)
End wsim.

Ltac sch_yield_l :=
  norm_l with do 1 iApply wsim_yield_src.

Ltac sch_resolve :=
  esplits; et; try set_solver.

Ltac sch_yield_rr :=
  norm_r with do 1 iApply wsim_yield_tgt; [left; sch_resolve|et|et|].
Ltac sch_yield_ir :=
  norm_r with do 1 iApply wsim_yield_tgt; [right; left; sch_resolve|et|et|].
Ltac sch_yield_ii :=
  norm_r with do 1 iApply wsim_yield_tgt; [right; right; sch_resolve|et|et|].

Ltac sch_intros :=
  try match goal with [H: nat |- _] => clear H end;
  (do 2 try match goal with [H: List.NoDup (map fst _) |- _] => clear H end);
  (do 2 try match goal with [H: list (key * Any.t) |- _] => clear H end);
  iIntros (?????); iIntrosFresh "IST"; iIntrosFresh "TID".

  (* Lemma wsim_spawn E_s fn vargs args fn_spec *)
  (*     (P : SAny.t → SAny.t → iProp Σ) (Q : SAny.t → SAny.t → SynDepO) *)
  (*     r g img_s img_t (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid : *)
  (*   sp_incl (SchAS.sp E_s sp_user) sp → *)
  (*   sp_user fn = Some fn_spec → *)
  (*   SchAS.fspec_spawnable E_s fn_spec P Q → *)
  (*   msk_s SchHdr.spawn → msk_t SchHdr.spawn → *)
  (*   Ist nths st_src st_tgt ∗ *)
  (*   tid_user my_tid ∗ *)
  (*   P vargs args ∗ *)
  (*   (∀ tid nths st_src st_tgt (NODS: List.NoDup (List.map fst st_src)) (NODT: List.NoDup (List.map fst st_tgt)), *)
  (*       Ist nths st_src st_tgt *)
  (*       -∗ tid_user my_tid *)
  (*       -∗ token_th tid Q *)
  (*       -∗ wsim fl_s fl_t Ist (E_s, E_s) r g R_s R_t RR true true nths *)
  (*           (st_src, k_s tid) (st_tgt, k_t tid)) *)
  (*   ⊢ wsim fl_s fl_t Ist (E_s, E_s) r g R_s R_t RR ps pt nths *)
  (*     (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s (Sch.spawn (fn, args)))) >>= k_s) *)
  (*     (st_tgt, (SB.sandbox img_t msk_t sc_t (SModTr.trans sp_t (Sch.spawn (fn, args)))) >>= k_t). *)
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
  (*   steps_l. steps_r. replace (E_s ∖ E_s ∪ E_s) with E_s by set_solver. *)
  (*   iDestruct "ASM" as (vr) "[% [[%tid [[-> ->] TKN]] TID]]". hss. steps_r. *)
  (*   iApply ("SIM" $! _ nths' _ _ NODS NODT with "IST TID TKN"). *)
  (* Qed. *)

  (* Lemma wsim_join E_s tid (Q : SAny.t → SAny.t → SynDepO) *)
  (*     r g (msk_s msk_t : _ → bool) sc_s sc_t sp sp_user k_s k_t my_tid *)
  (*     (SchInSp : sp_incl (SchAS.sp E_s sp_user) sp) : *)
  (*   msk_s SchHdr.join  → msk_t SchHdr.join → *)
  (*   Ist nths st_src st_tgt ∗ *)
  (*   tid_user my_tid ∗ *)
  (*   token_th tid Q ∗ *)
  (*   (∀ nths st_src st_tgt vret ret (NODS: List.NoDup (List.map fst st_src)) (NODT: List.NoDup (List.map fst st_tgt)), *)
  (*       Ist nths st_src st_tgt *)
  (*       -∗ tid_user my_tid *)
  (*       -∗ interp_cond (Q vret ret) *)
  (*       -∗ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR true true nths *)
  (*           (st_src, k_s vret) (st_tgt, k_t ret)) *)
  (*   ⊢ wsim fl_s fl_t Ist (Some (E_s, E_s)) r g R_s R_t RR ps pt nths *)
  (*     (st_src, (HModTr.sandbox msk_s sc_s (SModTr.trans sp (Sch.join tid))) >>= k_s) *)
  (*     (st_tgt, (HModTr.sandbox msk_t sc_t (PModTr.trans (Sch.join tid))) >>= k_t). *)
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


(* Ltac sch_spawn := *)
(*   norm with (do 1 (iApply wsim_spawn; try solve_sch_sp; try prove_sb_cond)). *)

(* Ltac sch_join := *)
(*   norm with (do 1 (iApply wsim_join; try solve_sch_sp; try prove_sb_cond)). *)

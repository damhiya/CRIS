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
    Ist st_src st_tgt ∗ (if src_some then tid_user q my_tid else emp) ∗
    (∀ st_src st_tgt (NODS: List.NoDup (List.map fst st_src)) (NODT: List.NoDup (List.map fst st_tgt)),
      Ist st_src st_tgt -∗ (if src_some then tid_user q my_tid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
        (st_tgt, k_t tt))
    ⊢ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
    (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans sp_t Sch.yield)) >>= k_t).
  Proof.
    intros Hcase Hmsks Hmskt. iIntros "[IST [TID SIM]]".
    rewrite /Sch.yield; unseal "Sch".
    iStopProof.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind.
    iIntros (g' [pt [ps [st_t st_s]]]). destruct_quant.
    iIntros "[IST [TID SIM]] %Hg #CIH".
    unfold_iter_r. steps_r. destruct _q; cycle 1.
    { unfold_iter_l. steps_l. force_l (Some false). steps_l.
      steps_r. iApply wsim_nodup. iIntros (? ?).
      iPoseProof ("SIM" $! _ _ NODS NODT with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
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
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; steps_l.
    force_l None; steps_l. iApply "SIM".
  (*SLOW*)Qed.
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
  iIntros (????); iIntrosFresh "IST"; iIntrosFresh "TID".


Require Import MSim.

Section MSIM.

  Import SchAS.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  Variable contextual: contextuality.
  Variable fl_src : alist (option string) (Any.t → itree crisE Any.t).
  Variable fl_tgt : alist (option string) (Any.t → itree crisE Any.t).
  Variable Ist : ist_type Σ.

  Lemma msim_flag_src_down r {Rs Rt} RR (ps pt: bool) sti_src sti_tgt fmr
    (SIM: _msim contextual fl_src fl_tgt Ist r Rs Rt RR ps pt sti_src sti_tgt fmr) :
    _msim contextual fl_src fl_tgt Ist r Rs Rt RR true pt sti_src sti_tgt fmr.
  Proof using.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _msim_tarski, SIM. i. econs; ii. subst. ss.
    specialize (IN NODFS NODFT NODS NODT H0). des.
    econs; esplits; eauto.
    depdes IN; try (by econs; eauto).
  Qed.

  Lemma msim_bind r {Rs Rt} RR Qs Qt QQ (ps pt: bool) st_src st_tgt i_src i_tgt fmr k_src k_tgt
    (SIM : _msim contextual fl_src fl_tgt Ist r Qs Qt QQ ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
    (SIMK: forall st_src0 st_tgt0 vret_src vret_tgt fmr0
             (RET: Own fmr0 ⊢ |==> QQ (st_src0, vret_src) (st_tgt0, vret_tgt)),
        _msim contextual fl_src fl_tgt Ist r Rs Rt RR ps pt (st_src, k_src vret_src) (st_tgt, k_tgt vret_tgt) fmr) :
    _msim contextual fl_src fl_tgt Ist r Rs Rt RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt) fmr.
  Proof using.
    remember (st_src, i_src) as sti_src. remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _msim_tarski, SIM. econs; i; apply hsupd_merge.
    econs; esplits; eauto.
    subst; ss. specialize (IN NODFS NODFT NODS NODT H0). des.
    
    (* depdes IN; grind; *)
    (*   try (by rr; i; esplits; eauto with paco arith); *)
    (*   try (by do 2 (econs; esplits; eauto with paco arith); *)
    (*           repeat rewrite <-bind_bind; *)
    (*           eauto 7 using rclo8, msim_bindC). *)
    (* - exploit SIMK; eauto. *)
    (*   i. apply GF in x0. eapply (_msim_flag_mon _ _ _ _ _  _ ps0 pt0) in x0; try by i; clarify. *)
    (*   destruct x0. eapply hsupd_update in IN; eauto. *)
    (*   eapply _msim_mon_auto; eauto using rclo8. *)
    (*   eapply Own_bupd_update; eauto. *)
  Admitted.
  
End MSIM.

Section SREL.

  Import SchAS.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  (* srel (progress_flag) (oneshot_flag) (i_rew) (i_org) *)
  Variant srel_def {R}
    (coself self : bool -> itree crisE R -> itree crisE R -> Prop)
    : bool -> itree crisE R -> itree crisE R -> Prop :=
    | srel_def_eq p itr
        (SRELEQ: True)
      : srel_def coself self p itr itr

    | srel_def_tau p itr_src itr_tgt
        (SRELTAU: True)
        (SELF: coself false itr_src itr_tgt)
      : srel_def coself self p (tau;; itr_src) (tau;; itr_tgt)

    | srel_def_tau_r p itr_src itr_tgt
        (SRELTAUR: True)
        (SELF: self true itr_src itr_tgt)
      : srel_def coself self p itr_src (tau;; itr_tgt)

    | srel_def_choose_diff p (X: Type) ktr_src ktr_tgt
        (SRELCHOOSEDIFF: True)
        (SELF: forall x_src: X, exists x_tgt: X, coself false (ktr_src x_src) (ktr_tgt x_tgt))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose_r p X itr_src ktr_tgt
        (SRELCHOOSER: True)
        (SELF: exists x, self true (itr_src) (ktr_tgt x))
      : srel_def coself self p itr_src (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose p X ktr_src ktr_tgt
        (SRELCHOOSE: True)
        (SELF: forall x, coself false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_take p X ktr_src ktr_tgt
        (SRELTAKE: True)
        (SELF: forall x, coself false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Take X);; ktr_src x) (x <- trigger (Take X);; ktr_tgt x)

    | srel_def_assume p P ktr_src ktr_tgt
        (SRELASSUME: True)
        (SELF: coself false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Assume P);; ktr_src x) (x <- trigger (Assume P);; ktr_tgt x)

    | srel_def_guarantee p P ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: coself false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Guarantee P);; ktr_src x) (x <- trigger (Guarantee P);; ktr_tgt x)

    | srel_def_call p fn args ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: forall x, coself false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Call fn args);; ktr_src x) (x <- trigger (Call fn args);; ktr_tgt x)
  .

  Inductive _srel {R} (srel: bool -> itree crisE R -> itree crisE R -> Prop) p itr_src itr_tgt : Prop :=
  | srel_intro (SELF: @srel_def R srel (@_srel R srel) p itr_src itr_tgt).

  Definition srel {R} := paco3 (@_srel R) bot3.

  Lemma _srel_tarski R srel rel
    (FIX: forall p itr_src itr_tgt (IN: @srel_def R srel rel p itr_src itr_tgt), rel p itr_src itr_tgt) :
    @_srel R srel <3= rel.
  Proof using.
    fix self 4. i.
    destruct PR. apply FIX. i. destruct SELF; des; econs; eauto.
  Qed.

  Lemma srel_def_mon R r r' s s' p itr_src itr_tgt
    (REL: @srel_def R r s p itr_src itr_tgt)
    (LEr: r <3= r')
    (LEs: s <3= s') :
    @srel_def R r' s' p itr_src itr_tgt.
  Proof using.
    ii. destruct REL; econs; eauto.
    { i. specialize (SELF x_src). des. eauto. }
    { des. eauto. }
  Qed.

  Lemma _srel_mon R : monotone3 (@_srel R).
  Proof using.
    ii. eapply _srel_tarski, IN.
    i. econs. eauto using srel_def_mon.
  Qed.

  Hint Resolve _srel_mon : paco.

  (* closure *)
  
  Variable contextual: contextuality.
  Variable fl_src : alist (option string) (Any.t → itree crisE Any.t).
  Variable fl_tgt : alist (option string) (Any.t → itree crisE Any.t).
  Variable Ist : ist_type Σ.

  Variant msim_srelC (r: forall Rs Rt (RR: retr_type Σ Rs Rt), msim_type Σ Rs Rt) :
    forall Rs Rt (RR: retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
    | msim_srelC_intro
        ps pt Rs Rt RR itr_rew itr_org itr_tgt st_src st_tgt fmr
        (SREL: @srel Rs false itr_rew itr_org)
        (SIM: r Rs Rt RR ps pt (st_src, itr_rew) (st_tgt, itr_tgt) fmr)
      : msim_srelC r Rs Rt RR ps pt (st_src, itr_org) (st_tgt, itr_tgt) fmr.

  Lemma msim_srelC_mon r1 r2 (LEr: r1 <8= r2) : msim_srelC r1 <8= msim_srelC r2.
  Proof using. ii; destruct PR; econs; eauto. Qed.

  Hint Resolve msim_srelC_mon : paco.

  Lemma msim_srelC_compatible : compatible8 (_msim contextual fl_src fl_tgt Ist) msim_srelC.
  Proof using.
    econs; eauto using msim_srelC_mon. ii.
    destruct PR.
    remember (st_src, itr_rew) as sti_src.
    remember (st_tgt, itr_tgt) as sti_tgt.
    move SIM before r. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _msim_tarski, SIM. i. econs. ii. subst.
    specialize (IN NODFS NODFT NODS NODT H0); des.
    esplits; eauto.
    depdes IN; try (by econs; esplits; eauto); try (by econs; eauto; econs; eauto);
      punfold SREL; move SREL after H0;
      remember (_: itree crisE Rs) as itr_rew in SREL; remember false as p in SREL; clear Heqp;
      move SREL before H0; revert_until SREL;
      pattern p, itr_rew, itr_org;
      eapply _srel_tarski, SREL; i; depdes IN; subst; try rewrite -> !bind_trigger in Heqitr_rew; ss; 
      try (by subst; econs; eauto; i; eapply K; try eapply NODS0; eauto; pstep; econs; econs; eauto);
      try (by eapply msim_tau_src; eauto; eapply msim_flag_src_down; econs; eauto; i; econs; esplits; eauto);
      try (by des; econs; eauto; eapply msim_flag_src_down; econs; i; eauto; econs; eauto);
      try (by inv Heqitr_rew; pclearbot; eapply msim_tau_src; eauto).
    { depdes Heqitr_rew. econs; eauto. i. specialize (SELF vret). pclearbot. eapply K; try eapply NODS0; eauto. f_equal. eapply func_ext_rev in x; eauto. }
    { depdes Heqitr_rew. admit. }
    { depdes Heqitr_rew. econs; eauto. i. specialize (SELF x0). pclearbot. eapply K; eauto. f_equal. eapply func_ext_rev in x; eauto. }
    { depdes Heqitr_rew. specialize (SELF x0). des. pclearbot. econs; eauto. instantiate (1 := x_tgt).
      eapply K; eauto. f_equal. eapply func_ext_rev in x. eauto. }
    { depdes Heqitr_rew. specialize (SELF x0). des. pclearbot. econs; eauto. instantiate (1 := x0).
      eapply K; eauto. f_equal. eapply func_ext_rev in x. eauto. }
    { depdes Heqitr_rew. econs; eauto. i. pclearbot. eapply K; eauto. f_equal. eapply func_ext_rev in x; eauto. }
    { depdes Heqitr_rew. econs; eauto. i. pclearbot. eapply K; eauto. f_equal. eapply func_ext_rev in x; eauto. }
  Admitted.

  Lemma srel_yy_y img_s msk_s sc_s sp_s:
    srel false
      ((SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield));;;
       (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)))
      (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)).
  Proof.
    set (ysnd := SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) at 2.
    unfold Sch.yield. unseal "Sch".
    pcofix CIH.

    rewrite !unfold_iterC. grind. rewrite SRed.tau SBRed.tau. grind.
    pstep. econs. econs; eauto. left.

    rewrite !SRed.bind !SRed.core !SBRed.bind !SBRed.choose. grind.
    pstep. econs. econs; eauto. i.

    destruct x_src; [destruct b|].
    { exists (Some true). left.

      rewrite !SRed.bind !SRed.call. grind. rewrite !SBRed.tau. grind.
      pstep. econs; econs; eauto. left.

      unfold SModTr.HoareCall. des_ifs.
      { rewrite !SBRed.bind !SBRed.choose. grind.
        pstep; econs; econsr; eauto. i. left.
        
        rewrite !SBRed.bind !SBRed.choose; grind.
        pstep; econs; econsr; eauto; i; left.

        rewrite !SBRed.bind !SBRed.Guarantee; grind.
        pstep; econs; econsr; eauto; i; left.
        
        rewrite !SBRed.call; grind. des_ifs; cycle 1.
        { grind. pstep; econs; econsr; eauto. i; ss. }
        grind. pstep; econs; econsr; eauto; i; left.

        rewrite !SBRed.bind !SBRed.take. grind. des_ifs; cycle 1.
        { grind. pstep; econs; econsr; eauto; i; ss. }
        grind. pstep; econs; econsr; eauto; i; left.

        rewrite !SBRed.bind !SBRed.Assume; grind. des_ifs; cycle 1.
        { grind. pstep; econs; econsr; eauto; i; ss. }
        pstep; econs; econsr; eauto; i.

        rewrite !SBRed.ret. grind. rewrite !SRed.ret !SBRed.ret. grind.
        right; eauto.
      }
      { rewrite !SBRed.bind !SBRed.call; grind. des_ifs; cycle 1.
        { grind. pstep; econs; econsr; eauto. i; ss. }
        grind. pstep; econs; econsr; eauto; i.

        rewrite !SRed.ret !SBRed.ret. grind.
        right; eauto.
      }
    }
    { exists (Some false). right. grind. }
    { exists (Some false). left.
      subst ysnd. unfold Sch.yield. unseal "Sch". rewrite unfold_iterC.
      grind. rewrite SRed.ret SBRed.ret. grind. 
      rewrite unfold_iterC. grind. pstep; econs. econs; eauto.
    }
  Qed.
  
End SREL.

Require Import CRIS SchHeader SchA.
Require Import ITactics.
Require Import MSim WSim.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

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

  Lemma wsim_yield_tgt
      (tid_res : bool)
      (E : coPset)
      (r g : rel)
      (img_s img_t : bool)
      (msk_s msk_t : string → bool)
      (scp_s scp_t : list string)
      (sp_s sp_t : string → option fspec)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (mtid stid : nat) :
    (tid_res = false ∧
     sp_s SchHdr.yield = None ∧
     sp_t SchHdr.yield = None ∧
     E = ∅) ∨
    (tid_res = true ∧
     ∃ sp_user_s,
       sp_incl (SchA.sp sp_user_s E) sp_s ∧ img_s = true ∧
       sp_t SchHdr.yield = None) ∨
    (tid_res = false ∧
    ∃ sp_user_s sp_user_t E_s E_t,
      sp_incl (SchA.sp sp_user_s E_s) sp_s ∧ img_s = true ∧
      sp_incl (SchA.sp sp_user_t E_t) sp_t ∧ img_t = true ∧
      (E_s ≡ E_t ∪ E) ∧ (E ## E_t)) →
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    Ist st_src st_tgt ∗ (if tid_res then Tid mtid stid else emp) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ (if tid_res then Tid mtid stid else emp) -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s sp_s 𝒴)) >>= k_s)
        (st_tgt, k_t tt))
    ⊢ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s sp_s 𝒴)) >>= k_s)
    (st_tgt, (SB.sandbox img_t msk_t scp_t (SModTr.trans img_t sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hcase Hmsks Hmskt. iIntros "[IST [TID SIM]]".
    rewrite /Sch.yield; unseal SCH.
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
    { replace (sp_s SchHdr.yield) with (Some (SchA.yield_spec E)); cycle 1.
      { erewrite (proj2 Hcase0); et. rewrite /SchA.sp; unseal CRIS; et. }
      rewrite Hcase2.
      steps_l. force_l (mtid, stid). forces_l. iSplitL "TID"; iFrame; eauto.
      steps_l.
      call "IST".
      steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss. steps_l. steps_r.
      by_coind CIH. iFrame.
    }
    { replace (sp_s SchHdr.yield) with (Some (SchA.yield_spec E_s)); cycle 1.
      { erewrite (proj2 Hcase0); et. unfold SchA.sp; unseal CRIS; et. }
      replace (sp_t SchHdr.yield) with (Some (SchA.yield_spec E_t)); cycle 1.
      { erewrite (proj2 Hcase2); et. unfold SchA.sp; unseal CRIS; et. }
      steps_r. iDestruct "GRT" as "[[-> TID0] _]". iClear "TID". iRename "TID0" into "TID".
      force_l (_, _). forces_l. iFrame "TID". iSplit; eauto.
      call "IST".
      steps_l. hss. iDestruct "ASM" as "[[-> TID] _]". steps_l.
      steps_r. forces_r. iSplitL "TID"; et.
      steps_r.
      by_coind CIH. iFrame.
      hss. iFrame.
    }
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g img_s (msk_s: _ → bool) scp_s sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans img_s sp_s 𝒴)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield; unseal SCH.
    unfold_iterC_l; steps_l.
    force_l None; steps_l. iApply "SIM".
  (*SLOW*)Qed.
End wsim.

Ltac clear_st :=
  hrepeat do 1 match goal with [st: alist key Any.t |- _] => clear st end.

Ltac clear_emp :=
  hrepeat do 1 match goal with [|- context[environments.Esnoc _ ?H (emp%I)]] => iClear H end.
  
Ltac sch_yield_l :=
  norm_l with do 1 iApply wsim_yield_src.

Ltac sch_auto :=
  hrepeat first [progress iFrame | iSplit; iFrame; et; []].

Ltac sch_intros :=
  clear_st; iIntros (??); iIntrosFresh "IST"; iIntrosFresh "TID"; clear_emp.

Ltac sch_yield_rr :=
  norm_r; iApply wsim_yield_tgt;
  [left; esplits; [refl|..]; et; try set_solver|et|et|sch_auto; [..|try sch_intros]].

Ltac sch_yield_ir :=
  norm_r; iApply wsim_yield_tgt;
  [right; left; esplits; [refl|..]; et; try set_solver|et|et|sch_auto; [..|try sch_intros]].

Ltac sch_yield_ii :=
  norm_r; iApply wsim_yield_tgt;
  [right; right; esplits; [refl|..]; et; try set_solver|et|et|sch_auto; [..|try sch_intros]].

(* Section RealLAT.
  Context `{CrisG: !crisG Γ Σ α β τ _S _I}.
  Context `{SchG: !schG}.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : ist_type Σ).
  Context (R_s R_t : Type).

  Context (r g : rel).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_s st_t : state).

  Local Notation sim Ep r g := (wsim fl_s fl_t Ist Ep r g R_s R_t).

  Lemma wsim_lat_real_both
    fsp_s fsp_t body_s body_t arg_s arg_t k_s k_t
    img_s img_t (msk_s msk_t: _ → bool) scp_s scp_t
    :
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    Ist st_s st_t ∗
    (□ ∀ x_s, ∃ x_t, precondS fsp_s x_s arg_s ==∗ precondS fsp_t x_t arg_t ∗ (precondS fsp_t x_t arg_t ==∗ precondS fsp_s x_s arg_s)) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ 
      sim (∅,∅) r g RR true true
        (st_src, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_none (ret_s <- body_s arg_s;;
                   RealUpdate (λ x, precondS fsp_s x arg_s) (λ x, postcondS fsp_s x ret_s);;;
                   Ret ret_s)) >>= k_s)                                                                                
        (st_tgt, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (ret_t <- body_t arg_t;;
                   RealUpdate (λ x, precondS fsp_t x arg_t) (λ x, postcondS fsp_t x ret_t);;;
                   Ret ret_t)) >>= k_t))
    ⊢
    sim (∅,∅) r g RR ps pt
      (st_s, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_none (lat_real true fsp_s 𝒴 body_s arg_s)) >>= k_s)
      (st_t, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (lat_real true fsp_t 𝒴 body_t arg_t)) >>= k_t).
  Proof using SchG.
    i. iIntros "H". iApply wsim_reset. iStopProof.
    revert st_s. combine_quant st_t.
    eapply wsim_coind. intros g' Hg CIH [st_t st_s].
    iIntros "[IST [#COND SIM]] /=". destruct_quant CIH.

    unfold_lat_real_l. unfold_lat_real_r.
    sch_yield_rr. sch_yield_l.
    steps_r. force_l _q. steps_l.
    destruct _q eqn: E; cycle 1; steps_l; steps_r.
    { iApply wsim_mono_knowledge; cycle 2.
      { eapply eq_ind. iApply ("SIM" with "IST").
        rewrite !SRed.bind !SBRed.bind !bind_bind.
        repeat f_equal; extensionalities.
        - rewrite !SRed.bind !SBRed.bind !bind_bind.
          repeat f_equal; extensionalities.
          rewrite !SRed.ret !SBRed.ret. ired.
          rewrite !SRed.ret !SBRed.ret. ired. et.
        - rewrite !SRed.bind !SBRed.bind !bind_bind.
          repeat f_equal; extensionalities.
          rewrite !SRed.ret !SBRed.ret. ired.
          rewrite !SRed.ret !SBRed.ret. ired. et.
      }
      { et. }
      { i. rewrite Hg. et. }
    }

    simpl_bool; des; subst.
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

  Lemma wsim_lat_real_tgt
    fsp_t body_t x_t arg_t E tid_res q my_tid
    k_s k_t img_s img_t (msk_s msk_t: _ → bool) scp_s scp_t sp_s
    I
    :
    (tid_res = false ∧
     sp_s SchHdr.yield = None ∧
     E = ∅ ∧
     q = 1%Qp (* unused value *)) ∨
    (tid_res = true ∧
     ∃ sp_user_s,
       sp_incl (SchA.sp sp_user_s E q) sp_s ∧ img_s = true) →
    msk_s SchHdr.yield →
    msk_t SchHdr.yield →
    I ∗ Ist st_s st_t ∗ (if tid_res then SchA.tid_user q my_tid else emp) ∗
    (□ (∀ st_src st_tgt,
       I -∗ winv (E, E) -∗ Ist st_src st_tgt -∗ (if tid_res then SchA.tid_user q my_tid else emp) ==∗
       precondS fsp_t x_t arg_t ∗ (precondS fsp_t x_t arg_t ==∗ I ∗ winv (E, E) ∗ Ist st_src st_tgt ∗ (if tid_res then SchA.tid_user q my_tid else emp)))
    ) ∗
    (∀ st_src st_tgt,
     I -∗ Ist st_src st_tgt -∗ (if tid_res then SchA.tid_user q my_tid else emp) -∗
     sim (E,E) r g RR true true
        (st_src, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴) >>= k_s)
        (st_tgt, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (ret_t <- body_t arg_t;;
                   RealUpdate (λ x, precondS fsp_t x arg_t) (λ x, postcondS fsp_t x ret_t);;;
                   Ret ret_t)) >>= k_t))
    ⊢
    sim (E,E) r g RR ps pt
      (st_s, SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s 𝒴) >>= k_s)
      (st_t, SB.sandbox img_t msk_t scp_t (SModTr.trans sp_none (lat_real true fsp_t 𝒴 body_t arg_t)) >>= k_t).
  Proof using.
    i. iIntros "H". iApply wsim_reset. iStopProof.
    revert st_s. combine_quant st_t.
    eapply wsim_coind. intros g' Hg CIH [st_t st_s].
    iIntros "[I [IST [TID [#COND SIM]]]] /=". destruct_quant CIH.

    unfold_lat_real_r.
    iApply wsim_yield_tgt; [|et|et|try (sch_auto; sch_intros)].
    { des; subst; [left|right;left]; et. }
    steps_r. destruct _q eqn: E0; cycle 1; steps_r.
    { iApply wsim_mono_knowledge; cycle 2.
      { eapply eq_ind. iApply ("SIM" with "I IST TID").
        rewrite !SRed.bind !SBRed.bind !bind_bind.
        repeat f_equal; extensionalities.
        rewrite !SRed.bind !SBRed.bind !bind_bind.
        repeat f_equal; extensionalities.
        rewrite !SRed.ret !SBRed.ret. ired.
        rewrite !SRed.ret !SBRed.ret. ired. et.
      }
      { et. }
      { i. rewrite Hg. et. }
    }

    simpl_bool; des_safe; subst.
    ru_r. iIntros (?) "UPD".
    iApply wsim_unfold; iIntros "W".
    iMod ("COND" with "I W IST TID") as "[C R]"; iFrame.
    iMod ("UPD" with "C") as "[PR C]".
    iMod ("R" with "C") as "[I [W [IST TID]]]".
    iApply wsim_fold; iFrame.
    force_r; iFrame. steps_r.
    by_coind CIH. iFrame. et.
  Qed.

End RealLAT.

Ltac peek_auto Hyps :=
  iRevert Hyps;
  let PAT := fresh "_PAT" in
  epose (PAT := ("("++_++")")% string);
  (hrepeat do 1 match goal with
    | |- _ (_ _ ?l _) _ =>
        match l with
        | context[INamed (String ?x ?y)] =>
            let name := fresh "_NAME" in
            set (name := String x y);
            instantiate (1:= (String x y ++ "&" ++ _)%string) in (value of PAT)
        end
    end);
  instantiate (1:= "_") in (value of PAT);
  (hrepeat do 1 match goal with [H:= _ |- _] =>
     match H with PAT => fail 1 | _ => subst H end end);
  iIntros Hyps; iSplitR Hyps;
  [ (hrepeat do 1 match goal with
       | |- _ (_ _ ?l _) _ =>
           match l with
           | context[INamed ?H] =>
               instantiate (1:= (_ ∗ _)%I); iSplitL H; [iApply H|]
           | _ => instantiate (1:= emp%I); et
           end
       end)
  | sch_auto;
    [..
    | iSplit; clear_st; 
      [ iModIntro; iIntros (??) PAT; iIntrosFresh "W";
        iIntrosFresh "IST"; iIntrosFresh "TID"; try unfold_pre_post
      | iIntros (??) PAT; iIntrosFresh "IST"; iIntrosFresh "TID"]];
    clear_emp
  ].

Ltac lat_real_rr Hyps :=
  norm_r; iApply (wsim_lat_real_tgt);
  [left; esplits; [refl|..]; et; try set_solver|et|et|peek_auto Hyps].

Ltac lat_real_ir Hyps :=
  norm_r; iApply (wsim_lat_real_tgt);
  [right; esplits; [refl|..]; et; try set_solver|et|et|peek_auto Hyps].

Section MSIM.

  Import SchA.
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

  Lemma msim_flag_tgt_down r {Rs Rt} RR (ps pt: bool) sti_src sti_tgt fmr
    (SIM: _msim contextual fl_src fl_tgt Ist r Rs Rt RR ps pt sti_src sti_tgt fmr) :
    _msim contextual fl_src fl_tgt Ist r Rs Rt RR ps true sti_src sti_tgt fmr.
  Proof using.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _msim_tarski, SIM. i. econs; ii. subst. ss.
    specialize (IN NODFS NODFT NODS NODT H0). des.
    econs; esplits; eauto.
    depdes IN; try (by econs; eauto).
  Qed.
  
End MSIM.

Section SREL.

  Import SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  (* srel (progress_flag) (oneshot_flag) (i_rew) (i_org) *)
  Variant srel_def 
    (coself : forall R, bool -> itree crisE R -> itree crisE R -> Prop)
    {R}
    (self : bool -> itree crisE R -> itree crisE R -> Prop)
    : bool -> itree crisE R -> itree crisE R -> Prop :=
    | srel_def_ret p r
        (SRELEQ: True)
      : srel_def coself self p (Ret r) (Ret r)

    | srel_def_tau p itr_src itr_tgt
        (SRELTAU: True)
        (SELF: coself R false itr_src itr_tgt)
      : srel_def coself self p (tau;; itr_src) (tau;; itr_tgt)

    | srel_def_tau_r p itr_src itr_tgt
        (SRELTAUR: True)
        (SELF: self true itr_src itr_tgt)
      : srel_def coself self p itr_src (tau;; itr_tgt)

    | srel_def_choose_diff p (X: Type) ktr_src ktr_tgt
        (SRELCHOOSEDIFF: True)
        (SELF: forall x_src: X, exists x_tgt: X, coself R false (ktr_src x_src) (ktr_tgt x_tgt))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose_r p X itr_src ktr_tgt
        (SRELCHOOSER: True)
        (SELF: exists x, self true (itr_src) (ktr_tgt x))
      : srel_def coself self p itr_src (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose p X ktr_src ktr_tgt
        (SRELCHOOSE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_take p X ktr_src ktr_tgt
        (SRELTAKE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Take X);; ktr_src x) (x <- trigger (Take X);; ktr_tgt x)

    | srel_def_io p I O f i ktr_src ktr_tgt
        (SRELIO: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (@IO I O f i);; ktr_src x) (x <- trigger (@IO I O f i);; ktr_tgt x)

    | srel_def_assume p P ktr_src ktr_tgt
        (SRELASSUME: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Assume P);; ktr_src x) (x <- trigger (Assume P);; ktr_tgt x)

    | srel_def_assumeres p r ktr_src ktr_tgt
        (SRELASSUMERES: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (AssumeRes r);; ktr_src x) (x <- trigger (AssumeRes r);; ktr_tgt x)

    | srel_def_guarantee p P ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Guarantee P);; ktr_src x) (x <- trigger (Guarantee P);; ktr_tgt x)

    | srel_def_call p fn args ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Call fn args);; ktr_src x) (x <- trigger (Call fn args);; ktr_tgt x)

    | srel_def_spawn p fn args ktr_src ktr_tgt
        (SRELSPAWN: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Spawn fn args);; ktr_src x) (x <- trigger (Spawn fn args);; ktr_tgt x)

    | srel_def_yield p n ktr_src ktr_tgt
        (SRELYIELD: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Yield n);; ktr_src x) (x <- trigger (Yield n);; ktr_tgt x)

    | srel_def_sput p k v ktr_src ktr_tgt
        (SRELSPUT: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (SPut k v);; ktr_src x) (x <- trigger (SPut k v);; ktr_tgt x)

    | srel_def_sget p k ktr_src ktr_tgt
        (SRELSGET: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (SGet k);; ktr_src x) (x <- trigger (SGet k);; ktr_tgt x)
  .

  Global Arguments srel_def coself {R} self.

  Inductive _srel srel R p itr_src itr_tgt : Prop :=
  | srel_intro (SELF: @srel_def srel R (@_srel srel R) p itr_src itr_tgt).

  Definition srel := paco4 _srel bot4.

  Lemma _srel_tarski srel R rel
    (FIX: forall p itr_src itr_tgt (IN: @srel_def srel R rel p itr_src itr_tgt), rel p itr_src itr_tgt) :
    @_srel srel R <3= rel.
  Proof using.
    fix self 4. i.
    destruct PR. apply FIX. i. destruct SELF; des; econs; eauto.
  Qed.

  Lemma srel_def_mon r r' R s s' p itr_src itr_tgt
    (REL: @srel_def r R s p itr_src itr_tgt)
    (LEr: r <4= r')
    (LEs: s <3= s') :
    @srel_def r' R s' p itr_src itr_tgt.
  Proof using.
    ii. destruct REL; econs; eauto.
    { i. specialize (SELF x_src). des. eauto. }
    { des. eauto. }
  Qed.

  Lemma _srel_mon : monotone4 _srel.
  Proof using.
    ii. eapply _srel_tarski, IN.
    i. econs. eauto using srel_def_mon.
  Qed.

  Hint Resolve _srel_mon : paco.

  (** useful lemmas **)

  Lemma _srel_mon_auto r r' R p i_src i_tgt
    (REL: _srel r R p i_src i_tgt)
    (LEr: r <4= r') :
    _srel r' R p i_src i_tgt.
  Proof using. eapply _srel_mon; eauto. Qed.

  Lemma _srel_flag_mon r R (p p': bool) i_src i_tgt
    (SIM: _srel r R p i_src i_tgt)
    (LES: p -> p') :
    _srel r R p' i_src i_tgt.
  Proof using.
    move SIM before r. revert_until SIM.
    pattern p, i_src, i_tgt.
    eapply _srel_tarski, SIM. i. econs.
    destruct IN; try by des; econs; eauto.
  Qed.

  Hint Constructors srel_def _srel : core.
  Hint Unfold srel : core.
  Hint Resolve _srel_mon : paco.
  Hint Resolve _srel_mon_auto : paco.
  Hint Resolve cpn4_wcompat : paco.

  (** srel closure **)

  Variant srel_flagC
    (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    R p1 i_src i_tgt : Prop :=
  | srel_flagC_intro p0
      (SIM: r R p0 i_src i_tgt)
      (FLAG: p0 = true -> p1 = true).

  Lemma srel_flagC_mon r1 r2 (LE : r1 <4= r2) :
    srel_flagC r1 <4= srel_flagC r2.
  Proof using.
    ii. destruct PR; econs; eauto.
  Qed.

  Hint Resolve srel_flagC_mon: core.

  Lemma srel_flagC_spec : srel_flagC <5= gupaco4 _srel (cpn4 _srel).
  Proof using.
    eapply wrespect4_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _srel_flag_mon, _srel_mon_auto, rclo4.
  Qed.

  Variant srel_eqC
    (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    R (p: bool) : itree crisE R -> itree crisE R -> Prop :=
  | srel_eqC_intro itr
    : srel_eqC r R p itr itr.

  Lemma srel_eqC_mon r1 r2 (LEr: r1 <4= r2) : srel_eqC r1 <4= srel_eqC r2.
  Proof using. ii. destruct PR; econs; eauto. Qed.

  Lemma srel_eqC_compatible : compatible4 _srel srel_eqC.
  Proof using.
    econs; eauto using srel_eqC_mon. i.
    destruct PR. ides itr.
    - econs; econs; eauto.
    - econs; econs; eauto. econs.
    - rewrite <-bind_trigger. depdes e; ss.
      { depdes a; ss; econs; econs; eauto; econs. }
      depdes s; ss.
      { depdes c; ss; econs; econs; eauto; econs. }
      depdes s; ss.
      { depdes p; ss; econs; econs; eauto; econs. }
      { depdes c; ss; econs; econsr; eauto; i; econs. }
  Qed.

  Lemma srel_eqC_spec: srel_eqC <5= gupaco4 _srel (cpn4 _srel).
  Proof using.
    intros. gclo. econs; eauto using srel_eqC_compatible.
    eapply srel_eqC_mon, PR; eauto with paco.
  Qed.

  Variant srel_bindC
      (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop :=
  | srel_bindC_intro
      p Q i_src i_tgt R k_src k_tgt
      (SIM : r Q p i_src i_tgt)
      (SIMK : ∀ vret, r R false (k_src vret) (k_tgt vret)) :
    srel_bindC r R p (i_src >>= k_src) (i_tgt >>= k_tgt).

  Lemma srel_bindC_mon r1 r2 (LEr : r1 <4= r2) : srel_bindC r1 <4= srel_bindC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Lemma srel_bindC_wrespectful : wrespectful4 _srel srel_bindC.
  Proof using.
    econs; eauto using srel_bindC_mon; i.
    destruct PR. apply GF in SIM.
    move SIM before GF. revert_until SIM.
    pattern p, i_src, i_tgt.
    eapply _srel_tarski, SIM. econs. i.
    depdes IN; grind; try (by econs; repeat rewrite <-bind_bind; eauto 7 using rclo4, srel_bindC).
    - exploit SIMK; eauto. i. eapply GF in x0. inv x0. eauto.
      eapply _srel_flag_mon with (p:=false); eauto.
      eapply _srel_mon_auto; eauto using rclo4.
    - econs; eauto. i. specialize (SELF x_src). des. esplits; eauto 7 using rclo4, srel_bindC.
    - econs; eauto. des. esplits; eauto.
  Unshelve. all: eauto.
  Qed.

  Lemma srel_bindC_spec : srel_bindC <5= gupaco4 _srel (cpn4 _srel).
  Proof using. intros. eapply wrespect4_uclo; eauto with paco. apply srel_bindC_wrespectful. Qed.

  (* msim closure *)
  
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
    depdes IN; try (by esplits; eauto; econs; esplits; eauto); try (by esplits; eauto; econs; eauto; econs; eauto);
      punfold SREL; move SREL after H0;
      remember (_: itree crisE Rs) as itr_rew in SREL; remember false as p in SREL; clear Heqp;
      move SREL before H0; revert_until SREL;
      pattern p, itr_rew, itr_org;
      eapply _srel_tarski, SREL; i; depdes IN; subst; try rewrite -> !bind_trigger in Heqitr_rew; ss;
      try (by depdes Heqitr_rew; esplits; eauto; econs; eauto);
      try (by exploit SELF; eauto; i; des; esplits; eauto; eapply msim_tau_src; eauto; eapply msim_flag_src_down; econs; eauto; i; econs; esplits; eauto);
      try (by des; exploit SELF; eauto; i; des; esplits; eauto; econs; eauto; eapply msim_flag_src_down; econs; i; eauto; econs; eauto); try depdes Heqitr_rew;
      try (by esplits; eauto; econs; eauto; intro vret; specialize (SELF vret); pclearbot; eapply K; eauto; f_equal; eapply func_ext_rev; eauto);
      try (by esplits; eauto; econs; eauto; i; specialize (SELF tt); pclearbot; eapply K; eauto; f_equal; eapply func_ext_rev; eauto);
      try (by specialize (SELF x0); des; esplits; eauto; econs; eauto; pclearbot; eapply K; eauto; f_equal; eapply func_ext_rev; eauto);
      try (by pclearbot; esplits; eauto; econs; eauto; i; eapply K; eauto; f_equal; eapply func_ext_rev; eauto).
    { esplits; eauto; econs; eauto; i; specialize (SELF vret). pclearbot. eapply (K _ st_src0 st_tgt0); eauto. f_equal. eapply func_ext_rev; eauto. }
    { esplits; eauto. econs; eauto. eapply K; eauto. ginit. guclo srel_bindC_spec. econs; eauto.
      guclo srel_eqC_spec. econs. i. specialize (SELF vret). pclearbot. eapply (func_ext_rev vret) in x. rewrite x in SELF. gfinal; eauto. }
    { specialize (SELF tt). pclearbot. esplits; eauto; econs; eauto. i. eapply (K st_src0 st_tgt0); eauto. f_equal; eapply func_ext_rev; eauto. }
  Qed.

  Lemma msim_srelC_spec: msim_srelC <9= gupaco8 (_msim contextual fl_src fl_tgt Ist) (cpn8 (_msim contextual fl_src fl_tgt Ist)).
  Proof using.
    intros. gclo. econs; eauto using msim_srelC_compatible.
    eapply msim_srelC_mon, PR; eauto with paco.
  Qed.

  Lemma srel_yy_y {R} (itr: unit -> itree crisE R) img_s msk_s sc_s sp_s:
    srel _ false
      ((SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield));;;
       (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= itr)
      (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield) >>= itr).
  Proof using.
    set (ysnd := SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) at 2.
    unfold Sch.yield. unseal SCH.

    ginit. gcofix CIH.

    rewrite !unfold_iterC. grind. rewrite SRed.tau SBRed.tau. grind.
    gstep. econs. econs; eauto.

    rewrite !SRed.bind !SRed.core !SBRed.bind !SBRed.choose. grind.
    gstep. econs. econs; eauto. i.

    destruct x_src; [destruct b|].
    { exists (Some true).

      rewrite !SRed.bind !SRed.call. grind. rewrite !SBRed.tau. grind.
      gstep. econs; econs; eauto.

      unfold SModTr.HoareCall. des_ifs.
      { rewrite !SBRed.bind !SBRed.choose. grind.
        gstep; econs; econsr; eauto. i.
        
        rewrite !SBRed.bind !SBRed.choose; grind.
        gstep; econs; econsr; eauto; i.

        rewrite !SBRed.bind !SBRed.Guarantee; grind.
        gstep; econs; econsr; eauto; i.
        
        rewrite !SBRed.call; grind. des_ifs; cycle 1.
        { grind. gstep; econs; econsr; eauto. i; ss. }
        grind. gstep; econs; econsr; eauto; i.

        rewrite !SBRed.bind !SBRed.take. grind. des_ifs; cycle 1.
        { grind. gstep; econs; econsr; eauto; i; ss. }
        grind. gstep; econs; econsr; eauto; i.

        rewrite !SBRed.bind !SBRed.Assume; grind. des_ifs; cycle 1.
        { grind. gstep; econs; econsr; eauto; i; ss. }
        gstep; econs; econsr; eauto; i.

        rewrite !SBRed.ret. grind. rewrite !SRed.ret !SBRed.ret. grind.
        gfinal; eauto.
      }
      { rewrite !SBRed.bind !SBRed.call; grind. des_ifs; cycle 1.
        { grind. gstep; econs; econsr; eauto. i; ss. }
        grind. gstep; econs; econsr; eauto; i.

        rewrite !SRed.ret !SBRed.ret. grind.
        gfinal; eauto.
      }
    }
    { exists (Some false). gbase. grind. }
    { exists (Some false).
      subst ysnd. unfold Sch.yield. unseal SCH. rewrite unfold_iterC.
      grind. rewrite SRed.ret SBRed.ret. grind. 
      rewrite unfold_iterC. grind. guclo srel_eqC_spec. econs; eauto.
    }
  Qed.
  
End SREL.

Section ISIM.

  Import SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.
  Variable contextual: contextuality.
  Variable fl_src fl_tgt : alist (option string) (Any.t → itree crisE Any.t).
  Variable Ist : ist_type Σ.

  Lemma isim_yy_y r g ps pt {Rs Rt} RR st_src k_src sti_tgt
    img_s msk_s sc_s sp_s :
    @isim Σ contextual fl_src fl_tgt Ist r g Rs Rt RR ps pt
      (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield));;;
               (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_src) sti_tgt
    ⊢ isim contextual fl_src fl_tgt Ist r g RR ps pt
      (st_src, (SB.sandbox img_s msk_s sc_s (SModTr.trans sp_s Sch.yield)) >>= k_src) sti_tgt.
  Proof using.
    destruct sti_tgt as [st_tgt i_tgt].
    split. intros x wfx SIM.
    Local Transparent isim.
    guclo msim_srelC_spec. econs; eauto using srel_yy_y.
  Qed.

End ISIM.

Section WSIM.
  Import SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !schG}.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Lemma wsim_yy_y E F r g img_s msk_s scp_s sp_s k_s i_t :
    wsim fl_s fl_t Ist (E, F) r g R_s R_t RR ps pt
      (st_src,
        (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield));;;
        (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
      (st_tgt, i_t)
    ⊢ wsim fl_s fl_t Ist (E, F) r g R_s R_t RR ps pt
    (st_src, (SB.sandbox img_s msk_s scp_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
    (st_tgt, i_t).
  Proof using.
    Local Transparent isim.
    iIntros "SIM".
    iApply wsim_unfold; iIntros "W".
    iPoseProof (wsim_fold with "[W SIM]") as "SIM"; iFrame.
    iPoseProof (wsim_isim with "SIM") as "SIM".
    iApply isim_wsim. iIntros "W".
    iPoseProof ("SIM" with "W") as "SIM".
    iStopProof. split. intros x wfx H0.
    guclo msim_srelC_spec. econs; eauto using srel_yy_y.
  Qed.

End WSIM. *)

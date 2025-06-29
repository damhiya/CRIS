Require Import CRIS.
Require Import SchHeader SchI SchA.
Require Import ltac2_lib.


Local Open Scope nat_scope.

Module SchIA. Section SchIA.
  Import SchAS.
  Context `{_crisG: !crisG  Γ Σ α β τ _S _I _T}.
  Context `{_schG: !schG}.

  Context (E_sch : coPset) (sp_global sp_user : string → option fspec).
  Context (SchInSp : sp_incl (SchAS.sp E_sch sp_user) sp_global).
  Context (FunInSp : sp_sub sp_user sp_global).

  Fixpoint ths_wf (nths : nat) (ths_tgt : SchI.thslist) : Prop :=
    match ths_tgt with
    | (tid, _) :: tl => (tid < nths) ∧ (ths_wf nths tl)
    | [] => True
    end.

  Inductive sim_ths (tid : nat) :
    (option (option SAny.t)) → (option (option SAny.t)) →
    fragreeUR → fragreeUR → option (iProp Σ) → Prop :=
  | sim_ths_idle : sim_ths tid None None None None None
  | sim_ths_active Q :
      sim_ths tid
        (Some None)
        (Some None)
        (Some (1%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        (Some ((1/4)%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        None
  | sim_ths_done vrv rv Q :
      sim_ths tid
        (Some (Some vrv))
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        (Some ((3/4)%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        (Some (interp_cond (Q vrv rv)))%I
  | sim_ths_joined vrv rv Q :
      sim_ths tid
        (Some (Some vrv))
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        (Some (1%Qp, to_agree (λ vs s, Some (to_agree (Q vs s)))))
        None.

  (**************************)
  Section AUX.
    Lemma ths_wf_nths_none ths_tgt nths : ths_wf nths ths_tgt → alist_find nths ths_tgt = None.
    Proof using.
      intro WF. induction ths_tgt; ss. destruct a. des. des_ifs; et. ss.
      rewrite eq_rel_dec_correct in Heq. des_ifs; try nia.
    Qed.

    Lemma ths_wf_replace ths_tgt t o nths :
      ths_wf nths ths_tgt → ths_wf nths (alist_replace t o ths_tgt).
    Proof using.
      i. induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct. des_ifs.
      des. split; ss. eauto.
    Qed.

    Lemma wf_ths_src ths_tgt (ths_src_b ths_src_w : threadsF) (ths_cond : gmap nat (iProp Σ))
        (SIM: ∀ tid, ∃ vrv, sim_ths tid vrv (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid)) :
      ✓ ths_src_b ∧ ✓ ths_src_w.
    Proof using. split; intros x; specialize (SIM x); des; inv SIM; ss. Qed.

    Lemma big_sepM_replace (m: gmap nat (iProp Σ)) i (Q: iProp Σ) :
      ([∗ map] P ∈ m, P) ∗ Q ⊢
      [∗ map] P ∈ <[i:=Q]> m, P.
    Proof using.
      iIntros "[M Q]". destruct (m !! i) eqn:L.
      - iApply big_sepM_insert_delete. iFrame. 
        iPoseProof (big_sepM_delete with "M") as "[_ D]"; et.
      - iApply big_sepM_insert; et. iFrame.
    Qed.
  End AUX.

  Section ALIST.
    (* alist lemmas *)
    Lemma alist_replace_find_None {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
        (NONE: alist_find k l = None) :
      (alist_replace k v' l) = l.
    Proof using. induction l; ss. destruct a. des_ifs. f_equal. et. Qed.

    Lemma alist_replace_find_eq_Some {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
        (SOME: alist_find k l = Some v) :
      alist_find k (alist_replace k v' l) = Some v'.
    Proof using.
      induction l; ss. destruct a. des_ifs.
      - rewrite eq_rel_dec_correct in Heq. des_ifs. ss. des_ifs.
        rewrite eq_rel_dec_correct in Heq0. des_ifs.
      - rewrite eq_rel_dec_correct in Heq. des_ifs. apply IHl in SOME. ss.
        rewrite eq_rel_dec_correct. des_ifs.
    Qed.

    Lemma alist_replace_find_eq_None {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      alist_find k (alist_replace k v' l) = None.
    Proof using.
      induction l; ss. destruct a. des_ifs.
      rewrite alist_replace_find_None; et. ss. des_ifs.
    Qed.

    Lemma alist_replace_find_neq_Some {K V} `{Dec K} (k k': K) (v v': V) (l: alist K V) (ov: option V)
      (NEQ: k <> k')
      (SOME: alist_find k' l = ov)
    :
      alist_find k' (alist_replace k v' l) = ov.
    Proof using.
      induction l; ss. destruct a. rewrite eq_rel_dec_correct. 
      rewrite eq_rel_dec_correct in SOME.
      des_ifs; ss; des_ifs; rewrite eq_rel_dec_correct in Heq1; des_ifs; et.
    Qed.

    Lemma alist_remove_find_None {K V} `{Dec K} (k: K) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      alist_remove k l = l.
    Proof using.
      induction l; ss. destruct a; ss. rewrite eq_rel_dec_correct in NONE.
      rewrite eq_rel_dec_correct. des_ifs. f_equal. et.
    Qed.

  End ALIST.

  (**************************)

  Definition Ist: nat → alist key Any.t → alist key Any.t → iProp Σ :=
    fun numths st_src st_tgt =>
      (∃ ths_tgt (ths_src_b ths_src_w: SchA.threadsF) (ths_cond: gmap nat (iProp Σ)) (tid: nat) (_internal: bool),
          ⌜st_tgt = [(SchI.v_ths, ths_tgt↑); (SchI.v_tid, tid↑)]
            ∧ <<THWF: ths_wf numths ths_tgt>>
            ∧ <<SIM: (∀ tid, ∃ vrv, sim_ths tid vrv (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))>>
            ∧ <<NTHS: 0 < numths>>
            ∧ st_src = [(SchA.v_internal, _internal↑)]⌝
          ∗ own base_γ (● ths_src_b : threadsRA)
          ∗ own base_γ (◯ ths_src_w : threadsRA)
          ∗ ([∗ map] tid↦P ∈ ths_cond, P)
          ∗ ((tid_admin (Some tid) ∗ ⌜_internal = false⌝) 
             ∨ (tid_admin None ∗ wsim_ginv (Some (E_sch, E_sch)) ∗ ⌜_internal = true⌝)))%I.

  Local Definition SchA := (SchA.t E_sch sp_global sp_user).
  Local Definition SchAPure := (SchAPure.t E_sch sp_global).
  Local Definition SchAMod := (SchA ★ SchAPure). 
  Local Definition SchIMod := (SchI.t).

  Lemma simF__spawn : HSim.sim_fun open SchAMod SchIMod Ist SchHdr._spawn.
  Proof using FunInSp SchInSp.
    init_simF.

    (* destruct q2 as [userf userm]. *)
    rewrite /SchA.trigger_Yield /SchI.trigger_Yield.
    steps_l. iDestruct "ASM" as "[%va [-> ASM]]"; hss.
    iDestruct "ASM" as "[[-> [-> [% %]]] [pre [token tid]]]"; hss.
    rename q6 into pre. rename q4 into synpost. rename q8 into fvargs. rename q10 into fargs.
    rename q11 into my_tid. rename q12 into pa_tid. rename q2 into userf.
    steps_l. steps_r.

    (* Process yield *)
    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA _]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    
    steps_r; hss.

    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; des; subst.    
    iApply wsim_unfold; iIntros "WI".
    yield "THB THW COND TA tid WI".
    { iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; des; subst.
      iPoseProof (tid_admin_some_user_merge with "[TA tid]") as "TA"; iFrame.
      iExists _, _, _. iSplit; eauto.
      iRight. iFrame. eauto.
    }

    iDestruct "IST" as (??????) "(% & THB & THW & COND & TA)"; subst; hss.
    steps_l. hss.
    iDestruct "TA" as "[[TA %] | [TA [WI _]]]"; hss.
    steps_r. hss.
    
    (* Call the spawnee *)
    inv H. rename x into userfspec. force_l userfspec; iFrame.
    iSplit; first (iPureIntro; apply FunInSp; done).
    steps_l. 

    iPoseProof (tid_admin_none_split my_tid with "TA") as "[TA tid]".

    unfold find_fsp in *. rewrite H1 in H0.
    unfold fspec_spawnable, fspec_weaker in H0.
    specialize (H0 my_tid). des.

    (* Choose the metavariables *)
    force_l x1. steps_l. force_l (fargs↑). steps_l.
    iAssert (wsim_ginv (Some (E_sch, E_sch)) ==∗ precond userfspec x1 fvargs↑ fargs↑)%I with "[pre tid]" as "PRE".
    { iIntros "I". iApply PRE. rewrite /fspec_virtual /fspec_wsim /precond /=. iFrame. eauto. }

    iMod ("PRE" with "WI") as "PRE".
    force_l; iFrame "PRE".
    steps_l.

    call "THB THW COND TA".
    { iFrame. iExists _, _, _. iSplitR; eauto. }

    steps_l. rename q into vret.
    iMod (POST $ vret with "[ASM]") as "I"; eauto.
    rewrite /fspec_wsim /fspec_virtual. do 2 rewrite {1}/postcond.
    iDestruct "I" as "[WI I]".
    iDestruct "I" as (vsret) "[-> [tid [%sret [-> POST]]]]".

    steps_r. hss. steps_r.
    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA ?]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.

    steps_r. hss. steps_r. hss.

    remember ([(_, _)]) as st_s'0.
    remember ([(_, _);_]) as st_t'0.
    iAssert (Ist nths'0 st_s'0 st_t'0) with "[token THB THW COND POST TA]" as "IST".
    { subst. destruct (alist_find my_tid ths_tgt1) eqn:LU; cycle 1; [|destruct o].
      { (* idle case - impossible *)
        dup SIM1. specialize (SIM1 my_tid). rewrite LU in SIM1. inv SIM1.
        iExists _, _, _, _, _, _. iFrame. iSplit; eauto. iPureIntro. esplits; et.
        - clear SIM2. induction ths_tgt1; ss. destruct a. rewrite eq_rel_dec_correct in LU.
          rewrite eq_rel_dec_correct. des_ifs. ss. des; split; et.
        - i. destruct (classic (tid0 = my_tid)).
          + subst. erewrite alist_replace_find_eq_None; et. exact None.
          + erewrite alist_replace_find_neq_Some; et. exact None.
      }
      { (* already done case - impossible *)
        dup SIM1. specialize (SIM1 my_tid). des. rewrite LU in SIM1. inv SIM1.
        { (* done *)
          symmetry in H5. rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H4 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
        { (* done *)
          symmetry in H5. rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H4 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
      }
      { (* active - only possible case *)
        dup SIM1. specialize (SIM1 my_tid). des. rewrite LU in SIM1. inv SIM1.
        rewrite /token_half. unseal "SchA".
        iCombine "token THW" gives %THW. iCombine "token THW" as "THW".

        rewrite auth_frag_valid in THW. ss.
        specialize (THW my_tid). rewrite discrete_fun_lookup_op in THW. rewrite Nat.eqb_refl in THW.
        rewrite -H2 in THW. rewrite// -Some_op Some_valid pair_valid in THW. des; ss.
        apply agree_op_inv in THW0.

        remember (λ vs s: SAny.t, Some (to_agree (synpost vs s)))%I as POSTF.
        iAssert (interp_cond (Q vsret sret))%I with "[POST]" as "POST".
        { subst. apply (inj to_agree) in THW0. specialize (THW0 vsret sret). ss. inv THW0.
          apply (inj to_agree) in H5. unfold interp_cond. rewrite H5. et. }

        assert (((((λ n : nat, if my_tid =? n then Some ((1/2)%Qp, to_agree POSTF) else ε) : threadsF) ⋅ ths_src_w1): threadsF) ≡ ((λ n : nat, if my_tid =? n then Some ((3/4)%Qp, to_agree (λ (vs s: SAny.t), Some (to_agree (Q vs s)))) else ths_src_w1 n): threadsF)).
        { intros y. rewrite discrete_fun_lookup_op. des_ifs. 2:rewrite left_id //.
          rewrite Nat.eqb_eq in Heq; subst. rewrite -H2 -Some_op -pair_op frac_op -THW0 agree_idemp.
          f_equiv. f_equiv. compute_done.
        }
        rewrite H.

        clear SIM SIM0.
        iExists (alist_replace my_tid (Some sret) ths_tgt1), _, _, (<[my_tid:=(interp_cond (Q vsret sret))%I]> ths_cond1), my_tid, false.
        iFrame. iSplitR "POST COND TA".
        - iPureIntro. esplits; et.
          + eapply ths_wf_replace; eauto.
          + i. destruct (classic (tid0 = my_tid)).
            * subst. erewrite alist_replace_find_eq_Some; et. rewrite !lookup_insert. 
              rewrite Nat.eqb_refl. rewrite -H0. eexists; econs 3; et.
            * erewrite alist_replace_find_neq_Some; et. 2:exact None.
              des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
              rewrite !lookup_insert_ne; et.
        - iSplitR "TA".
          + iApply big_sepM_replace; iFrame.
          + iLeft; eauto.
      }
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal "Sch".
    clear THWF THWF0 THWF1 SIM SIM0 SIM1 NTHS NTHS0 NTHS1 Heqst_s'0 Heqst_t'0.
    iApply wsim_reset.
    iStopProof. revert NODS.
    combine_quant NODD.
    combine_quant st_t'0.
    combine_quant st_s'0.
    combine_quant nths'0.
    eapply wsim_coind. i.
    destruct a as [nths1 [st_src1 [st_tgt1 [NODS1 NODD1]]]]. s.
    iIntros "(WI & TU & IST) _ #CIH".
    unfold_iter_l. unfold_iter_r.

    steps_l. force_l my_tid. force_l (tt↑).
    force_l. iSplitL "WI TU". { iFrame. eauto. }

    steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[[-> TU] ->]". hss.
    steps_l.
    steps_r. hss. steps_r.
    by_coind "CIH". iFrame.
    Unshelve. all: eauto. all: apply nat.
  (*SLOW*)Qed.

  Lemma simF_spawn : HSim.sim_fun open SchAMod SchIMod Ist SchHdr.spawn.
  Proof using FunInSp SchInSp.
    init_simF.

    step_l. step_l. destruct q as [[[[farg fvarg] pre] synpost] userf].
    steps_l.
    iDestruct "ASM" as "[%va [-> ASM]]".
    iDestruct "ASM" as "[[-> [-> [% %]]] [PRE tid]]". hss. inv H.
    rename x into userfspec.
    steps_l. force_l q. steps_l.
    force_l. iSplit.
    { iPureIntro. apply SchInSp; ss. rewrite /sp; unseal CRIS; ss. }

    (* spawn _spawn *)
    rename q into my_tid. rename q1 into farg.
    force_l (nths, my_tid, farg, fvarg, pre, synpost, userf).
    force_l ((my_tid, userf, farg)↑).
    steps_l. steps_r.

    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA _]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss. steps_r.

    spawn. steps_r. hss. steps_l.

    iApply wsim_unfold; iIntros "WI".
    
    (* create new token *)
    dup THWF. apply ths_wf_nths_none in THWF. hexploit (SIM nths). i. rewrite THWF in H. des. inv H.

    iCombine "THB THW" as "TH".
    iPoseProof (own_update with "TH") as "TH".
    { apply shot_thread with (Q:=synpost). split; et. apply wf_ths_src in SIM. et. }
    iMod "TH" as "[[[[THB THW] TKNH] TKNQ1] TKNQ0]".

    (* create new tid token *)
    iPoseProof (tid_admin_some_user_merge with "[TA tid]") as "TA"; iFrame.
    iPoseProof (tid_admin_none_split with "TA") as "[TA newtid]". instantiate (1:=nths).
    force_l. iSplitL "PRE TKNH newtid WI".
    { rewrite /token_half. unseal "SchA". iFrame. iExists _. esplits; et. }
    steps_l.

    (* yield *)
    yield "COND THB THW TKNQ1 TA".
    { iCombine "THW TKNQ1" as "THW".
      iExists _, _, _, _, nths, false. iFrame. iSplit; eauto.
      iPureIntro. esplits; et.
      - clear SIM. ss. split; [nia|]. rewrite alist_remove_find_None; et.
        induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct in THWF.
        des; des_ifs; split; [nia|et].
      - i. destruct (classic (tid = nths)).
        + subst. rewrite alist_add_find_eq. 
          rewrite !discrete_fun_lookup_op Nat.eqb_refl -H4 left_id -H5.
          eexists; econs 2; et.
        + rewrite alist_add_find_neq; et.
          rewrite discrete_fun_lookup_op.
          des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite right_id. et.
    }
    
    steps_l. steps_r.
    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA [WI _]]])"; subst; hss.
    iPoseProof (tid_admin_none_split with "TA") as "[TA tid]". instantiate (1:=my_tid).
    force_l (nths ↑). force_l.
    iSplitL "tid TKNQ0 WI"; iFrame; eauto.
    step. iFrame. iSplit; eauto. iExists _, _, _. esplits; eauto.
  (*SLOW*)Qed.

  Lemma simF_yield : HSim.sim_fun open SchAMod SchIMod Ist SchHdr.yield.
  Proof using FunInSp SchInSp.
    init_simF.

    rewrite /SchA.trigger_Yield /SchI.trigger_Yield.

    steps_l.
    iDestruct "ASM" as "[[-> tid] ->]". hss.

    steps_r.
    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA _]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss. steps_r.

    force_l q0. steps_l. hss.

    iPoseProof (tid_admin_some_user_merge with "[TA tid]") as "TA"; iFrame.
    iApply wsim_unfold; iIntros "WI".
    
    yield "THB THW COND TA WI".
    { iExists _, _, _, _, _, _. iSplit; et. s. iFrame. iRight. iFrame. eauto. }

    steps_l. 

    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA [WI _]]])"; subst; hss.
    iPoseProof (tid_admin_none_split with "TA") as "[TA tid]". instantiate (1:=q).

    force_l (tt↑). steps_l. steps_r.
    force_l. iSplitL "tid WI". { iFrame. eauto. }
    step. iFrame. iSplit; eauto. iExists _, _, _. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma simF_join : HSim.sim_fun open SchAMod SchIMod Ist SchHdr.join.
  Proof using FunInSp SchInSp.
    init_simF.

    step_l. step_l.
    destruct q as [[tid postS] my_tid]; s. steps_l.
    iDestruct "ASM" as (vargs) "[-> [[-> ->] [TOK tid]]]". hss. rename q into tid.

    steps_r.
    rewrite !/Sch.yield /ccallU. unseal "Sch".

    iApply wsim_unfold; iIntros "WI".
    iApply wsim_reset. iStopProof.
    revert NODD.
    combine_quant NODS.
    combine_quant st_tgt.
    combine_quant st_src.
    combine_quant nths.
    eapply wsim_coind. intros g' a.
    destruct a as [nths [st_src [st_tgt [NODS NODD]]]]. s.
    iIntros "[IST [TKN [tid WI]]] _ #CIH".

    unfold_iter_l; unfold_iter_r.

    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA _]])"; des; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss. steps_r.
    
    destruct (alist_find tid ths_tgt) eqn:LU; [destruct o|].
    { (* done(O) | joined(X) *)
      hexploit (SIM tid). intro T. des. rewrite LU in T. inv T.
      { (* done(O) *)
        iClear "CIH". steps_r.
        steps_l. force_l true. steps_l. force_l (Some vrv0).
        steps_l.
        iPoseProof (big_sepM_delete with "COND") as "[POST COND]"; et.

        iCombine "THW TKN" gives %WF. iCombine "THW TKN" as "WF".
        rewrite auth_frag_valid in WF. specialize (WF tid). ss.
        rewrite discrete_fun_lookup_op Nat.eqb_refl -H3 -Some_op Some_valid in WF.
        rewrite -pair_op pair_valid frac_op in WF. des.

        apply agree_op_inv in WF0. dup WF0.
        apply (inj to_agree) in WF0.
        iAssert (interp_cond (postS vrv0 t))%I with "[POST]" as "POST".
        { unfold interp_cond. specialize (WF0 vrv0 t). ss. inv WF0. apply (inj to_agree) in H1.
          rewrite -H1. iApply "POST".
        }
        
        force_l. force_l. iSplitL "POST tid WI"; iFrame; et.
        assert (◯ (ths_src_w ⋅ (λ n: nat, if tid =? n then Some ((1/4)%Qp, to_agree (λ (vs s: SAny.t), Some (to_agree (postS vs s)))) else ε) : threadsF) ≡ ◯ ((λ n: nat, if tid =? n then Some (1%Qp, to_agree (λ vs s: SAny.t, Some (to_agree (Q vs s)))) else ths_src_w n) : threadsF)).
        { f_equiv. intros y. rewrite !discrete_fun_lookup_op.
          destruct (decide (tid = y)).
          - subst. rewrite Nat.eqb_refl -WF1 -H3 -Some_op -pair_op frac_op agree_idemp.
            do 2 f_equiv. compute_done.
          - des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst; ss.
        }
        rewrite H.

        step. iSplit; et.
        iExists _, _, _, _, _, _. iFrame. iSplit; eauto. iPureIntro.
        esplits; et. i. destruct (classic (tid = tid0)).
        - subst. rewrite LU -H3 -H2 Nat.eqb_refl lookup_delete. eexists; econs.
        - des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite lookup_delete_ne; et.
      }
      { (* joined(X) *)
        iCombine "THW TKN" gives %WF. exfalso.
        rewrite auth_frag_valid in WF. specialize (WF tid). ss.
        rewrite discrete_fun_lookup_op -H3 Nat.eqb_refl -Some_op -pair_op frac_op in WF.
        rewrite Some_valid pair_valid in WF. des. ss.
      }
    }
    { (* active(O) *)
      steps_l. steps_r.
      force_l false. steps_l. force_l my_tid. force_l (tt↑).
      force_l. iSplitL "tid WI". { iFrame. eauto. }

      call "THB THW COND TA".      
      { iExists _, _, _, _, _, _. iFrame. iSplit; eauto. }

      steps_l. iDestruct "ASM" as  "[[-> tid] ->]".
      steps_l. hss. steps_l.
      steps_r. hss. steps_r.
      rewrite /cgetU.
      by_coind "CIH". iFrame.
    }
    { (* idle(X) *)
      iCombine "THB TKN" gives %WF. exfalso.
      hexploit (SIM tid). intro STHS. des. rewrite LU in STHS. inv STHS.
      apply auth_both_valid_discrete in WF. des.
      apply (discrete_fun_included_spec_1 _ _ tid) in WF.
      ss. rewrite Nat.eqb_refl in WF. rewrite -H0 in WF.
      eapply fragree_incl_false. et.
    }
  Unshelve. all : ss. all: apply nat.
  (*SLOW*)Qed.
Ltac _wforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ (Some (?Ew, ?E)) _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_precond_postcond P'
        end
      | unfold_precond_postcond P; iApply wsim_guarantee_src
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ None _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply wsim_guarantee_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumePrecise _) >>= _) _) ] =>
      iApply wsim_assume_precise_src; iSplit; [|iIntrosFresh "ASM"]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wsim_unwrapN_src
  end.
  Lemma simF_get_tid : HSim.sim_fun open SchAMod SchIMod Ist SchHdr.get_tid.
  Proof using FunInSp SchInSp.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> tid] ->]"; hss.
    steps_r.
    iDestruct "IST" as (??????) "(% & THB & THW & COND & [[TA %]|[TA _]])"; des; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. forces_l. iSplitL "tid"; eauto.
    step. iSplit; eauto. iFrame. iExists _, _, _. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : HSim.t open SchAMod SchIMod SchA.init_cond Ist.
  Proof using FunInSp SchInSp.
    init_sim.
    - rewrite /SchA.init_cond /init_threads /init_tid. unseal "SchA".
      iIntros "[[THB THW] tid]". iExists _, _, _, ∅, 0, false.
      iFrame. rewrite big_sepM_empty. iSplitR; et.
      2:{ rewrite /tid_admin. iSplitR; eauto. iLeft. rewrite /tid_admin. unseal "SchA". eauto. }
      iPureIntro. esplits; et; ss; [split; nia |]. i. 
      rewrite// eq_rel_dec_correct. des_ifs.
      + rewrite lookup_empty. eexists; econs 2.
      + rewrite Nat.eqb_eq in Heq0. subst; ss.
      + rewrite lookup_empty. eexists; econs.
    - ii. iIntros "IST". iDestruct "IST" as (??????) "(% & THB & THW & COND & TA)"; des; subst.
      iExists _, _, _, _, _, _. iFrame. iPureIntro. i. esplits; [et| |et|nia|et].
      clear SIM. induction ths_tgt; ss. destruct a. des. splits; [nia|]. apply IHths_tgt; et. 
    - hss. unfold sub_perm, SchIMod, SchI.t, SchA, SchA.t, SchAPure, SchAPure.t. 
      unseal CRIS. simpl. unfold SchAPure.scopes.
      exists []. ss. 
    - eapply simF__spawn.
    - eapply simF_spawn.
    - eapply simF_yield.
    - eapply simF_join.
    - eapply simF_get_tid.
  Qed.
End SchIA.

Section ctxr.
  Context `{_crisG: !crisG  Γ Σ α β τ _S _I _T}.
  Context `{_schG: !schG}.

  Lemma ctxr (E_sch : coPset) (sp_global sp_user : string → option fspec)
        (SchInGlobal : sp_incl (SchAS.sp E_sch sp_user) sp_global)
        (UserInGlobal : sp_sub sp_user sp_global) :
    ctx_refines
      ((SchA.t E_sch sp_global sp_user) ★ (SchAPure.t E_sch sp_global), SchA.init_cond)
      (SchI.t, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End ctxr.
End SchIA.

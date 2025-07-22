Require Import CRIS.
Require Import SchHeader SchI SchA.
Require Import ltac2_lib.

Local Open Scope nat_scope.

Module SchIA. Section SchIA.
  Import SchAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

  Context (sp: sp_type).
  Context (sp_user : spl_type).
  Context (SchInSp : sp_incl (SchAS.sp sp_user ⊤ 1) sp).
  Context (FunInSp : sp_incl sp_user sp).

  Fixpoint ths_wf (nths : nat) (ths_tgt : SchI.thslist) : Prop :=
    match ths_tgt with
    | (tid, _) :: tl => (tid < nths) ∧ (ths_wf nths tl)
    | [] => True
    end.

  Definition opt_match {V} (ov0 ov1: option V) : Prop :=
    match ov0, ov1 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
    end.

  Fixpoint ths_rel_wf (ths_src ths_tgt : SchI.thslist) : Prop :=
    match ths_src, ths_tgt with
    | (tid_src, rv_src) :: ths_src_tl, (tid_tgt, rv_tgt) :: ths_tgt_tl =>
        tid_src = tid_tgt ∧ opt_match rv_src rv_tgt ∧ ths_rel_wf ths_src_tl ths_tgt_tl
    | [], [] => True
    | _, _ => False
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

    Lemma ths_wf_mon nths nths' ths_tgt
      (WF: ths_wf nths ths_tgt)
      (LE: nths <= nths') :
      ths_wf nths' ths_tgt.
    Proof using.
      induction ths_tgt; ss.
      destruct a. des; split; try nia.
      apply IHths_tgt; eauto.
    Qed.

    Lemma wf_ths_src ths_src ths_tgt (ths_src_b ths_src_w : threadsF) (ths_cond : gmap nat (iProp Σ))
        (SIM: ∀ tid, sim_ths tid (alist_find tid ths_src) (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid)) :
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

    Lemma map_fst_alist_replace_eq {K V} `{Dec K} (k: K) (v: V) (l: alist K V):
      map fst (alist_replace k v l) = map fst l.
    Proof using.
      induction l; ss. destruct a.
      rewrite eq_rel_dec_correct. des_ifs.
      ss. f_equal. eauto.
    Qed.

    Lemma ths_rel_wf_alist_replace (ths_src ths_tgt: thslist) k v w
      (REL: ths_rel_wf ths_src ths_tgt) :
      ths_rel_wf (alist_replace k (Some v) ths_src) (alist_replace k (Some w) ths_tgt).
    Proof using.
      gen ths_tgt. induction ths_src; ss.
      - i; des_ifs.
      - i. destruct a. destruct ths_tgt; ss.
        destruct p; des; subst. rewrite eq_rel_dec_correct. des_ifs.
        ss. split; eauto.
    Qed.

    Lemma ths_rel_wf_alist_find_some_some (ths_src ths_tgt: thslist) k v
      (REL: ths_rel_wf ths_src ths_tgt)
      (TGT: alist_find k ths_tgt = Some (Some v)) :
      ∃ w, alist_find k ths_src = Some (Some w).
    Proof using.
      gen ths_tgt. induction ths_src.
      - i. ss. destruct ths_tgt; ss.
      - i. ss. destruct a. destruct ths_tgt; ss.
        destruct p; des; subst. rewrite eq_rel_dec_correct in TGT.
        destruct (nat_Dec k n0).
        + inv TGT. rewrite eq_rel_dec_correct. des_ifs. destruct o; ss. eexists; eauto.
        + rewrite eq_rel_dec_correct. des_ifs. eauto.
    Qed.

    Lemma ths_rel_wf_alist_find_some_none (ths_src ths_tgt: thslist) k
      (REL: ths_rel_wf ths_src ths_tgt)
      (TGT: alist_find k ths_tgt = Some None) :
       alist_find k ths_src = Some None.
    Proof using.
      gen ths_tgt. induction ths_src.
      - i. ss. destruct ths_tgt; ss.
      - i. ss. destruct a. destruct ths_tgt; ss.
        destruct p; des; subst. rewrite eq_rel_dec_correct in TGT.
        destruct (nat_Dec k n0).
        + inv TGT. rewrite eq_rel_dec_correct. des_ifs. destruct o; ss.
        + rewrite eq_rel_dec_correct. des_ifs. eauto.
    Qed.

    Lemma ths_rel_wf_alist_find_none (ths_src ths_tgt: thslist) k
      (REL: ths_rel_wf ths_src ths_tgt)
      (TGT: alist_find k ths_tgt = None) :
      alist_find k ths_src = None.
    Proof using.
      gen ths_tgt. induction ths_src; ss.
      i. destruct a. destruct ths_tgt; ss.
      destruct p; des; subst. rewrite eq_rel_dec_correct in TGT.
      rewrite eq_rel_dec_correct. des_ifs. eauto.
    Qed.

  End ALIST.

  (**************************)

  Definition Ist: nat → alist key Any.t → alist key Any.t → iProp Σ :=
    fun numths st_src st_tgt =>
      (∃ (ths_src ths_tgt: SchI.thslist) (ths_src_b ths_src_w: SchA.threadsF) (ths_cond: gmap nat (iProp Σ)) (tids: SchI.tidslist) (tid: nat) (intnl: bool),
          ⌜st_tgt = [(SchI.v_ths, ths_tgt↑); (SchI.v_tid, tid↑); (SchI.v_tids, tids↑)]
          ∧ st_src = [(SchA.v_internal, intnl↑); (SchI.v_ths, ths_src↑); (SchI.v_tid, tid↑); (SchI.v_tids, tids↑)]
          ∧ <<THWF: ths_wf (length tids) ths_tgt>>
          ∧ <<THSEQ: ths_rel_wf ths_src ths_tgt>>
          ∧ <<TSWF: length tids <= numths>>
          ∧ <<SIM: (∀ tid, sim_ths tid (alist_find tid ths_src) (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))>>⌝
          (* ∧ <<NTHS: 0 < numths>> *)
          ∗ own base_γ (● ths_src_b : threadsRA)
          ∗ own base_γ (◯ ths_src_w : threadsRA)
          ∗ ([∗ map] tid↦P ∈ ths_cond, P)
          ∗ ((⌜intnl = false⌝ ∗ tid_admin (Some tid)) 
             ∨ (⌜intnl = true⌝ ∗ tid_admin None ∗ winv (⊤, ⊤))))%I.

  Local Definition SchAMod := SchA.t sp sp_user.
  Local Definition SchIMod := SchI.t.

  Lemma simF__spawn : ISim.sim_fun open SchAMod SchIMod SchA.init_cond Ist (Some SchHdr._spawn).
  Proof using FunInSp SchInSp.
    init_simF.

    rewrite /SchA.trigger_Yield /SchI.trigger_Yield /SchA.check_internal /SchI.check_internal.
    steps_l.
    iDestruct "ASM" as "[%[->[%[%[%[[->[->%]] [pre token]]]]]]]"; hss.
    rename q4 into pre, q2 into synpost, q3 into my_tid.
    steps_l. steps_r.

    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA WI]]])"; subst; hss.
    iPoseProof (tid_admin_none_split my_tid with "TA") as ">[TA tid]".

    (* SRC: find fspec in sp *)
    dup H. rewrite /fspec_spawnable /fspec_imply /= in H0. des.    
    assert (SPFN: sp fn = Some fsp).
    { apply FunInSp. eauto. }
    rewrite SPFN.
    specialize (H1 my_tid). des. force_l x0. steps_l. force_l (farg↑).

    (* SRC: guarantee a precondition of user fspec *)
    iPoseProof (PRE with "[WI pre tid]") as ">pre".
    { rewrite /precond /fspec_winv. iFrame. iSplit; eauto. }
    force_l. iSplitL "pre"; iFrame.
    steps_l.

    (* Call the spawnee *)
    call "THB THW COND TA".
    { iFrame. iExists _, _, _, _, _. iSplitR; eauto. }

    steps_l. rename q into vret.
    iMod (POST $ vret with "[ASM]") as "I"; eauto.
    rewrite /fspec_winv /fspec_virtual. do 2 rewrite {1}/postcond.
    iDestruct "I" as "[WI I]".
    iDestruct "I" as (vsret) "[-> [tid [%sret [-> POST]]]]".

    steps_r. hss. steps_r.
    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA _]]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss.

    set (st_s'0 := [_;_;_;_]).
    set (st_t'0 := [_;_;_]).
    iAssert (Ist nths' st_s'0 st_t'0) with "[token THB THW COND POST TA]" as "IST".
    { subst st_s'0 st_t'0. destruct (alist_find my_tid ths_tgt0) eqn:LU; cycle 1; [|destruct o].
      { (* idle case - impossible *)
        dup SIM0. specialize (SIM0 my_tid). rewrite LU in SIM0. inv SIM0.
        iExists _, _, _, _, _, _, _, _. iFrame. iSplit; eauto. iPureIntro. esplits; et.
        - clear SIM1 THSEQ0. gen ths_src0.
          induction ths_tgt0; ss. destruct a. rewrite eq_rel_dec_correct in LU.
          rewrite eq_rel_dec_correct. des_ifs. ss. des; split; eauto.
        - eapply ths_rel_wf_alist_replace; eauto.
        - i. destruct (classic (tid0 = my_tid)).
          + subst. erewrite !alist_replace_find_eq_None, <-H1, <-H3, <-H4; et. econs. all: exact None.
          + erewrite !alist_replace_find_neq_Some; eauto. all: exact None.
      }
      { (* already done case - impossible *)
        dup SIM0. specialize (SIM0 my_tid). des. rewrite LU in SIM0. inv SIM0.
        { (* done *)
          rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
        { (* done *)
          rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
      }
      { (* active - only possible case *)
        dup SIM0. specialize (SIM0 my_tid). des. rewrite LU in SIM0. inv SIM0.
        rewrite /token_half. unseal "SchA".
        iCombine "token THW" gives %THW. iCombine "token THW" as "THW".

        rewrite auth_frag_valid in THW. ss.
        specialize (THW my_tid). rewrite discrete_fun_lookup_op in THW. rewrite Nat.eqb_refl in THW.
        rewrite -H3 in THW. rewrite// -Some_op Some_valid pair_valid in THW. des; ss.
        apply agree_op_inv in THW0.

        remember (λ vs s: SAny.t, Some (to_agree (synpost vs s)))%I as POSTF.
        iAssert (interp_cond (Q q0 sret))%I with "[POST]" as "POST".
        { subst. apply (inj to_agree) in THW0. specialize (THW0 q0 sret). ss. inv THW0.
          apply (inj to_agree) in H7. unfold interp_cond. rewrite H7. et. }

        assert (((((λ n : nat, if my_tid =? n then Some ((1/2)%Qp, to_agree POSTF) else ε) : threadsF) ⋅ ths_src_w0): threadsF) ≡ ((λ n : nat, if my_tid =? n then Some ((3/4)%Qp, to_agree (λ (vs s: SAny.t), Some (to_agree (Q vs s)))) else ths_src_w0 n): threadsF)).
        { intros y. rewrite discrete_fun_lookup_op. des_ifs. 2:rewrite left_id //.
          rewrite Nat.eqb_eq in Heq; subst. rewrite -H3 -Some_op -pair_op frac_op -THW0 agree_idemp.
          f_equiv. f_equiv. compute_done.
        }
        rewrite H5.

        clear SIM.
        iExists _, (alist_replace my_tid (Some sret) ths_tgt0), _, _, (<[my_tid:=(interp_cond (Q q0 sret))%I]> ths_cond0), _, my_tid, false.
        iFrame. iSplitR "POST COND TA".
        - iPureIntro. esplits; et.
          + eapply ths_wf_replace; eauto.
          + eapply ths_rel_wf_alist_replace; eauto.
          + i. destruct (classic (tid0 = my_tid)).
            * subst. erewrite !alist_replace_find_eq_Some; et. rewrite !lookup_insert.
              rewrite Nat.eqb_refl. rewrite -H1. econs 3.
            * erewrite !alist_replace_find_neq_Some; et. 2:exact None.
              des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
              rewrite !lookup_insert_ne; et. exact None.
        - iSplitR "TA".
          + iApply big_sepM_replace; iFrame.
          + iLeft; eauto.
      }
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal "Sch".
    clear THWF THWF0 TSWF TSWF0 THSEQ THSEQ0 SIM SIM0 NTHS.
    clearbody st_t'0 st_s'0.
    iApply wsim_reset.
    iStopProof. revert NODUPFS.
    combine_quant NODUPFT.
    combine_quant st_t'0.
    combine_quant st_s'0.
    combine_quant nths'.
    eapply wsim_coind. i.
    destruct a as [nths1 [st_src1 [st_tgt1 [NODS1 NODT1]]]]. s.
    destruct_quant.
    iIntros "(WI & TU & IST) _ #CIH".
    unfold_iter_l. unfold_iter_r.

    steps_l. force_l my_tid. force_l (tt↑).
    force_l. iSplitL "WI TU". { iFrame. eauto. }

    steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[[-> TU] ->]". hss.
    steps_l.
    steps_r. hss. steps_r.
    by_coind "CIH"; eauto.
    iPoseProof (winv_split_empty with "I") as "[I E]". iFrame.
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open SchAMod SchIMod SchA.init_cond Ist (Some SchHdr.spawn).
  Proof using FunInSp SchInSp.
    init_simF.

    step_l. step_l. destruct q as [[my_tid pre] post].
    steps_l.
    iDestruct "ASM" as "[%va [-> [tid ASM]]]".
    iDestruct "ASM" as (???) "[[-> [-> %]] PRE]"; hss. dup H. inv H0; des.
    rewrite /fspec_imply in H0. specialize (H0 my_tid). des.

    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA WI]]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss. steps_r.

    steps_l; hss. force_l (length q1, pre, post). steps_l.

    (* create new token *)
    dup THWF. apply ths_wf_nths_none in THWF. hexploit (SIM (length q1)). i.
    rewrite THWF in H0. des. inv H0.

    iCombine "THB THW" as "TH".
    iPoseProof (own_update with "TH") as "TH".
    { apply shot_thread with (Q:=post). split; et. apply wf_ths_src in SIM. et. }
    iMod "TH" as "[[[[THB THW] TKNH] TKNQ1] TKNQ0]".

    forces_l. iSplitL "PRE TKNH".
    { rewrite /token_half. unseal "SchA". iFrame. iExists _. iSplit; eauto. }

    steps_l. steps_r. hss. steps_r.
    spawn. steps_r. hss. steps_l. hss.
    force_l ((length q1)↑). forces_l. iSplitL "tid TKNQ0"; iFrame; eauto.
    step. iSplit; eauto. iCombine "THW TKNQ1" as "THW". iFrame.
    iExists _, _, _, _, _. iSplit; eauto. iPureIntro. esplits; eauto.
    { rewrite last_length. econs; [nia|]. rewrite alist_remove_find_None; eauto.
      eapply ths_wf_mon; eauto. }
    { econs; ss. split; eauto. rewrite !alist_remove_find_None; eauto. }
    { rewrite last_length. nia. }
    { i. destruct (tid =? length q1) eqn:EQ.
      { rewrite Nat.eqb_eq in EQ; subst. rewrite discrete_fun_lookup_op Nat.eqb_refl.
        rewrite !alist_add_find_eq -H4 -H5 left_id. econs. }
      { rewrite Nat.eqb_neq in EQ. des_ifs.
        { rewrite Nat.eqb_eq in Heq; subst; ss. }
        { rewrite discrete_fun_lookup_op !alist_add_find_neq; eauto. rewrite Heq right_id; eauto. }
      }
    }
  (*SLOW*)Qed.

  Lemma simF_yield : ISim.sim_fun open SchAMod SchIMod SchA.init_cond Ist (Some SchHdr.yield).
  Proof using FunInSp SchInSp.
    init_simF.

    rewrite /SchA.trigger_Yield /SchI.trigger_Yield /triggerUB.
    rewrite /SchA.check_internal /SchI.check_internal.

    steps_l.
    iDestruct "ASM" as "[[-> tid] ->]". hss. steps_r.
    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA WI]]])"; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_l. hss. steps_r. depdes q1. do 3 (steps_r; hss).

    force_l (exist _ x l). steps_l. hss. des_ifs; cycle 1.
    { steps_l. ss. }

    iPoseProof (tid_admin_some_user_merge with "[TA tid]") as ">TA"; iFrame.
    iApply wsim_unfold; iIntros "WI".
    steps_l; steps_r.
    
    yield "THB THW COND TA WI".
    { do 8 iExists _. iSplit; et. s. iFrame. iRight. iFrame. eauto. }

    steps_l.

    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA WI]]])"; subst; hss.
    iPoseProof (tid_admin_none_split with "TA") as ">[TA tid]". instantiate (1:=q1).

    force_l (tt↑). steps_l. steps_r.
    force_l. iSplitL "tid WI". { iFrame. eauto. }
    step. iFrame. iSplit; eauto. iExists _, _, _, _, _. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma simF_join : ISim.sim_fun open SchAMod SchIMod SchA.init_cond Ist (Some SchHdr.join).
  Proof using FunInSp SchInSp.
    init_simF.

    step_l. step_l.
    destruct q as [[tid postS] my_tid]; s. steps_l.
    iDestruct "ASM" as (vargs) "[-> [[-> ->] [TOK tid]]]". hss. 

    steps_l. steps_r.
    iApply wsim_unfold; iIntros "WI".
    iApply wsim_reset. iStopProof.
    revert NODT.
    combine_quant NODS.
    combine_quant st_tgt.
    combine_quant st_src.
    combine_quant nths.
    eapply wsim_coind. intros g' a.
    destruct a as [nths [st_src [st_tgt [NODS NODT]]]]. s.
    destruct_quant.
    iIntros "[IST [tid [TKN WI]]] _ #CIH".

    unfold_iter_l; unfold_iter_r.

    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA _]]])"; des; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. hss. steps_r. steps_l. hss.
    
    destruct (alist_find tid ths_tgt) eqn:LU; [destruct o|].
    { (* done(O) | joined(X) *)
      hexploit (SIM tid). intro T. des. rewrite LU in T. inv T.
      { (* done(O) *)
        iClear "CIH". steps_r.
        steps_l. force_l ((Some t)↑).
        steps_l.
        iPoseProof (big_sepM_delete with "COND") as "[POST COND]"; et.

        iCombine "THW TKN" gives %WF. iCombine "THW TKN" as "WF".
        rewrite auth_frag_valid in WF. specialize (WF tid). ss.
        rewrite discrete_fun_lookup_op Nat.eqb_refl -H3 -Some_op Some_valid in WF.
        rewrite -pair_op pair_valid frac_op in WF. des.

        apply agree_op_inv in WF0. dup WF0.
        apply (inj to_agree) in WF0.
        iAssert (interp_cond (postS vrv t))%I with "[POST]" as "POST".
        { unfold interp_cond. specialize (WF0 vrv t). ss. inv WF0. apply (inj to_agree) in H5.
          rewrite -H5. iApply "POST".
        }
        
        force_l. iSplitL "POST tid WI"; iFrame; et.
        assert (◯ (ths_src_w ⋅ (λ n: nat, if tid =? n then Some ((1/4)%Qp, to_agree (λ (vs s: SAny.t), Some (to_agree (postS vs s)))) else ε) : threadsF) ≡ ◯ ((λ n: nat, if tid =? n then Some (1%Qp, to_agree (λ vs s: SAny.t, Some (to_agree (Q vs s)))) else ths_src_w n) : threadsF)).
        { f_equiv. intros y. rewrite !discrete_fun_lookup_op.
          destruct (decide (tid = y)).
          - subst. rewrite Nat.eqb_refl -WF1 -H3 -Some_op -pair_op frac_op agree_idemp.
            do 2 f_equiv. compute_done.
          - des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst; ss.
        }
        rewrite H.

        step. iSplit; et.
        iExists _, _, _, _, _, _, _, _. iFrame. iSplit; eauto. iPureIntro.
        esplits; et. i. destruct (classic (tid = tid0)).
        - subst. rewrite LU -H3 -H2 Nat.eqb_refl lookup_delete.
          hexploit ths_rel_wf_alist_find_some_some; eauto; intro LUS.
          des. rewrite LUS. econs.
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
      hexploit ths_rel_wf_alist_find_some_none; eauto; intros LUS.
      rewrite LUS. steps_l. steps_r.
      force_l my_tid. force_l (tt↑).
      force_l. iSplitL "tid WI". { iFrame. eauto. }

      call "THB THW COND TA".
      { do 8 iExists _. iFrame. iSplit; eauto. }

      steps_l. iDestruct "ASM" as  "[[-> tid] ->]".
      steps_l. hss. steps_l.
      steps_r. hss. steps_r.
      rewrite /cgetU.
      iApply wsim_nodup; iIntros "% %".
      by_coind "CIH"; eauto.
      iPoseProof (winv_split_empty with "I") as "[I E]"; iFrame.
    }
    { (* idle(X) *)
      iCombine "THB TKN" gives %WF. exfalso.
      hexploit (SIM tid). intro STHS. des. rewrite LU in STHS. inv STHS.
      apply auth_both_valid_discrete in WF. des.
      apply (discrete_fun_included_spec_1 _ _ tid) in WF.
      ss. rewrite Nat.eqb_refl in WF. rewrite -H in WF.
      eapply fragree_incl_false. et.
    }
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open SchAMod SchIMod SchA.init_cond Ist (Some SchHdr.get_tid).
  Proof using FunInSp SchInSp.
    init_simF.

    steps_l. iDestruct "ASM" as "[[-> tid] ->]"; hss.
    steps_r.
    iDestruct "IST" as (????????) "(% & THB & THW & COND & [[% TA]|[% [TA WI]]])"; des; subst; hss.
    2:{ iExFalso. iApply (tid_admin_none_user with "[TA tid]"); iFrame. }
    iPoseProof (tid_admin_some_user with "[TA tid]") as "%"; iFrame; subst.
    steps_r. forces_l. steps_l; hss. forces_l. iSplitL "tid"; eauto.
    step. iSplit; eauto. iFrame. iExists _, _, _, _, _. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open SchAMod SchIMod SchA.init_cond Ist.
  Proof using FunInSp SchInSp.
    init_sim.
    - ii. iIntros "IST".
      iDestruct "IST" as (????????) "(% & THB & THW & COND & TA)"; des; subst.
      iFrame. iExists _, _, _. iPureIntro. esplits; eauto; nia.
    - split; eauto. rewrite /SchA.init_cond /init_threads /init_tid. unseal "SchA".
      iIntros "[[THB THW] tid]". iExists _, _, _, _, ∅, _, 0, false.
      iFrame. rewrite big_sepM_empty. iSplitR; et.
      2:{ rewrite /tid_admin. iSplitR; eauto. iLeft. rewrite /tid_admin. unseal "SchA". eauto. }
      iPureIntro. esplits; et; ss; [split; nia |]. i. 
      rewrite// eq_rel_dec_correct. des_ifs.
      + rewrite lookup_empty. econs 2.
      + rewrite Nat.eqb_eq in Heq0. subst; ss.
      + rewrite lookup_empty. econs.
    - eapply simF__spawn.
    - eapply simF_spawn.
    - eapply simF_yield.
    - eapply simF_join.
    - eapply simF_get_tid.
  Qed.
End SchIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

  Lemma ctxr sp sp_user
        (SchInGlobal : sp_incl (SchAS.sp sp_user ⊤ 1) sp)
        (UserInGlobal : sp_incl sp_user sp) :
    ctx_refines
      (SchA.t sp sp_user, SchA.init_cond)
      (SchI.t, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End ctxr.
End SchIA.

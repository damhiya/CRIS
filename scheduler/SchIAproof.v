Require Import CRIS.

Require Import SchGInv SchHeader SchI SchA.

Require Import wpsim_tactics ltac2_lib.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module SchIA. Section SchIA.
  Import SchAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.
  Context (u_a u_i : positive) (n : level).

  Context (Spc_global Spc_user : string -> option fspec).
  Context (SchInSpc : spc_incl (spc u_a n Spc_user) Spc_global).
  Context (FunInSpc : spc_sub Spc_user Spc_global).

  Fixpoint ths_wf (nths: nat) (ths_tgt: SchI.thslist): Prop :=
    match ths_tgt with
    | (tid, _) :: tl => (tid < nths) ∧ (ths_wf nths tl)
    | [] => True
    end.

  Inductive sim_ths (tid: nat): 
    (option (option SAny.t)) -> fragreeUR -> fragreeUR -> option (iProp Σ) -> Prop :=
  | sim_ths_idle
    :
      sim_ths tid None None None None

  | sim_ths_active Q
    : 
      sim_ths tid
        (Some None)
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some ((1/4)%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        None

  | sim_ths_done rv Q
    : 
      sim_ths tid 
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some ((3/4)%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some (interp_cond (Q rv)))%I

  | sim_ths_joined rv Q
    :
      sim_ths tid
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        None
  .

  (**************************)

  Section AUX.

    Lemma ths_wf_nths_none ths_tgt nths:
      ths_wf nths ths_tgt -> alist_find nths ths_tgt = None.
    Proof.
      intro WF. induction ths_tgt; ss.
      destruct a. des. des_ifs; et. ss.
      rewrite eq_rel_dec_correct in Heq. des_ifs; try nia.
    Qed.

    Lemma wf_ths_src ths_tgt (ths_src_b ths_src_w: threadsF) (ths_cond: gmap nat (iProp Σ ))
      (SIM: ∀ tid, sim_ths tid (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))
    :
      ✓ ths_src_b ∧ ✓ ths_src_w.
    Proof. split; intros x; specialize (SIM x); inv SIM; ss. Qed.

    Lemma big_sepM_replace (m: gmap nat (iProp Σ)) i (Q: iProp Σ) :
      ([∗ map] P ∈ m, P) ∗ Q
      ⊢ [∗ map] P ∈ <[i:=Q]> m, P.
    Proof.
      iIntros "[M Q]". destruct (m !! i) eqn:L.
      - iApply big_sepM_insert_delete. iFrame. 
        iPoseProof (big_sepM_delete with "M") as "[_ D]"; et.
      - iApply big_sepM_insert; et. iFrame.
    Qed.

  End AUX.

  Section ALIST.

    (* alist lemmas *)
    Lemma alist_replace_find_None {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      (alist_replace k v' l) = l.
    Proof.
      induction l; ss. destruct a. des_ifs. f_equal. et.
    Qed.

    Lemma alist_replace_find_eq_Some {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (SOME: alist_find k l = Some v)
    :
      alist_find k (alist_replace k v' l) = Some v'.
    Proof.
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
    Proof.
      induction l; ss. destruct a. des_ifs.
      rewrite alist_replace_find_None; et. ss. des_ifs.
    Qed.

    Lemma alist_replace_find_neq_Some {K V} `{Dec K} (k k': K) (v v': V) (l: alist K V) (ov: option V)
      (NEQ: k <> k')
      (SOME: alist_find k' l = ov)
    :
      alist_find k' (alist_replace k v' l) = ov.
    Proof.
      induction l; ss. destruct a. rewrite eq_rel_dec_correct. 
      rewrite eq_rel_dec_correct in SOME.
      des_ifs; ss; des_ifs; rewrite eq_rel_dec_correct in Heq1; des_ifs; et.
    Qed.

    Lemma alist_remove_find_None {K V} `{Dec K} (k: K) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      alist_remove k l = l.
    Proof.
      induction l; ss. destruct a; ss. rewrite eq_rel_dec_correct in NONE.
      rewrite eq_rel_dec_correct. des_ifs. f_equal. et.
    Qed.

  End ALIST.

  (**************************)

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    fun numths st_src st_tgt =>
      (∃ ths_tgt (ths_src_b ths_src_w: SchA.threadsF) (ths_cond: gmap nat (iProp Σ)), 
          ⌜st_tgt = [(SchI.v_ths, ths_tgt↑)] 
            ∧ <<THWF: ths_wf numths ths_tgt>>
            ∧ <<SIM: (∀ tid, sim_ths tid (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))>>
            ∧ <<NTHS: 0 < numths>>⌝
          ∗ own base_γ (● ths_src_b : threadsRA)
          ∗ own base_γ (◯ ths_src_w : threadsRA)
          ∗ ([∗ map] tid↦P ∈ ths_cond, P))%I.

  Local Notation SchAMod := (SchA.t u_a n Spc_global Spc_user).
  Local Notation SchIMod := (SchI.t).

  Lemma simF__spawn : HSim.sim_fun open SchAMod SchIMod Ist SchName._spawn.
  Proof.
    init_wpsim u_a u_i n.

    w_steps_l.
    iDestruct "ASM" as "[%va [-> ASM]]"; hss.
    (* destruct q as [[[[[callertid fargs] fvargs] pre] postS] [userf userm]]. *)
    destruct q2 as [userf userm].
    iDestruct "ASM" as "[[-> [-> [% %]]] [pre token]]".
    rename q6 into pre. rename q4 into synpost. rename q8 into fargs. rename q10 into fvargs.
    (* destruct va as [[user userf] userargs]. *)
    w_step_l. hss.

    (* Process yield *)
    w_step_r. w_force_l. iSplitL ""; first done.

    prep_r. yield "IST".
    w_step_l.
    w_step_l; iClear "ASM".
    w_steps_l. w_steps_r.

    (* Call the spawnee *)
    prep. inv H. rename x into userfspec. w_force_l userfspec; iFrame.
    iSplit; first (iPureIntro; apply FunInSpc; done).
    w_steps_l.

    (* Choose the metavariables *)
    do 2 w_force_l.
    prep. iApply wpsim_full_guarantee_src. iSplitL "pre".
    Unshelve.
    3:{ clear H0. unfold find_fsp in userm. rewrite H1 in userm. exact userm. }
    3:{ exact (fvargs↑). }
    { unfold find_fsp in *. revert userm H0. generalize H1.
      rewrite H1. i.
      rewrite (UIP _ _ _ H0 eq_refl). erewrite <-rew_swap; et; ss.
      unfold fspec_spawnable in H2. des.
      iIntros "I"; iApply H2; iFrame.
    }

    w_call "IST"; et.
    w_step_l. rename q into vret.
    remember (existT userf userm) as DT; clear HeqDT.
    revert userm H0. generalize H1. unfold find_fsp. rewrite H1.
    i; ss. rewrite (UIP _ _ _ H0 eq_refl). erewrite <- rew_swap; ss.
    unfold fspec_spawnable in H2; des.
    prep. iApply wpsim_full_assume_src; iSplitL ""; iIntros "I".
    { iPoseProof (H3 $ ret with "[I]") as "H".
      { iExists _; iFrame. }
      { iExact "H". }
    }
    iDestruct "I" as (sret) "[% POST]".

    w_steps_l. w_steps_r. hss. w_steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss.
    w_steps_r. hss.

    remember ([(SchI.v_ths, ((alist_replace my_tid (Some sret) ths_tgt): thslist) ↑)]) as st_tgt1.
    iAssert (Ist nths'0 st_s'0 st_tgt1) with "[token THB THW COND POST]" as "IST".
    { destruct (alist_find my_tid ths_tgt) eqn:LU; cycle 1; [|destruct o].
      { (* idle case - impossible *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        iExists _, _, _, _. iFrame. iPureIntro. esplits; et.
        - clear SIM0. induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct in LU.
          rewrite eq_rel_dec_correct. des_ifs. ss. des; split; et.
        - i. destruct (classic (tid = my_tid)).
          + subst. erewrite alist_replace_find_eq_None; et. 
            rewrite -H0 -H -H4. econs 1; et. exact None.
          + erewrite alist_replace_find_neq_Some; et. exact None.
      }
      { (* already done case - impossible *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        { (* done *)
          symmetry in H6. rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
        { (* joined *) 
          symmetry in H6. rewrite /token_half. unseal "SchA". iCombine "token THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
      }
      { (* active - only possible case *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        rewrite /token_half. unseal "SchA".
        iCombine "token THW" gives %THW. iCombine "token THW" as "THW".

        rewrite auth_frag_valid in THW. ss.
        specialize (THW my_tid). rewrite discrete_fun_lookup_op in THW. rewrite Nat.eqb_refl in THW.
        rewrite -H0 in THW. rewrite// -Some_op Some_valid pair_valid in THW. des; ss.
        apply agree_op_inv in THW0.

        remember (λ s: SAny.t, Some (to_agree (synpost s)))%I as POSTF.
        iAssert (interp_cond (Q sret))%I with "[POST]" as "POST".
        { subst. apply (inj to_agree) in THW0. specialize (THW0 sret). ss. inv THW0.
          apply (inj to_agree) in H7. unfold interp_cond. rewrite H7. et. }

        assert (((((λ n : nat, if my_tid =? n then Some ((1/2)%Qp, to_agree POSTF) else ε) : threadsF) ⋅ ths_src_w): threadsF) ≡ ((λ n : nat, if my_tid =? n then Some ((3/4)%Qp, to_agree (λ s: SAny.t, Some (to_agree (Q s)))) else ths_src_w n): threadsF)).
        { intros y. rewrite discrete_fun_lookup_op. des_ifs. 2:rewrite left_id //.
          rewrite Nat.eqb_eq in Heq; subst. rewrite -H0 -Some_op -pair_op frac_op -THW0 agree_idemp.
          f_equiv. f_equiv. compute_done.
        }
        rewrite H5.

        iExists _, _, _, (<[my_tid:=(interp_cond (Q sret))%I]> ths_cond).
        iFrame. iSplitR "POST COND".
        - iPureIntro. esplits; et.
          + clear SIM0. induction ths_tgt; ss. destruct a; ss.
            rewrite eq_rel_dec_correct in LU. rewrite eq_rel_dec_correct. des_ifs. ss.
            des; split; et.
          + i. destruct (classic (tid = my_tid)).
            * subst. erewrite alist_replace_find_eq_Some; et. rewrite !lookup_insert. 
              rewrite Nat.eqb_refl. rewrite -H. econs 3; et.
            * erewrite alist_replace_find_neq_Some; et. 2:exact None.
              des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
              rewrite !lookup_insert_ne; et.
        - iApply big_sepM_replace; iFrame.
      }
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal "Sch".
    clear THWF SIM NTHS Heqst_tgt1.
    iApply wpsim_reset.
    iStopProof. revert NODUP.
    combine_quant NODS1.
    combine_quant st_tgt1.
    combine_quant st_s'0.
    combine_quant nths'0.
    eapply wpsim_coind. i.
    destruct a as [nths1 [st_src1 [st_tgt1 [NODS1 NODD1]]]]. s.
    iIntros "IST _ #CIH".
    unfold_iter_l. unfold_iter_r.

    w_step_l. w_step_l.
    w_force_l tt. w_force_l (tt↑).
    w_force_l. iSplitL ""; first ss.

    w_call "IST".
    w_steps_l. iDestruct "ASM" as "[-> ->]". hss.
    w_steps_l.
    w_steps_r. hss. w_steps_r.
    by_coind "CIH".
    done.
    Unshelve. all: ss.
  Qed.

  Lemma simF_spawn : HSim.sim_fun open SchAMod SchIMod Ist SchName.spawn.
  Proof.
    init_wpsim u_a u_i n.

    w_step_l. w_step_l.
    destruct q as [[[[farg fvarg] pre] synpost] [userf userm]].
    w_steps_l.
    iDestruct "ASM" as "[%va [-> ASM]]".
    iDestruct "ASM" as "[[-> [-> [% %]]] PRE]". inv H. rename x into userfspec.

    (* spawn _spawn *)
    prep_l. w_force_l (my_tid, farg, fvarg, pre, synpost, existT userf userm).
    w_force_l ((my_tid, userf, farg)↑).
    hss. w_steps_r.
    w_step.
    w_steps_r.

    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss.
    w_steps_r.

    (* create new token *)
    dup THWF. apply ths_wf_nths_none in THWF. hexploit (SIM nths). i. rewrite THWF in H. inv H.

    iCombine "THB THW" as "TH".
    iPoseProof (own_update with "TH") as "TH".
    { apply shot_thread with (Q:=synpost). split; et. apply wf_ths_src in SIM. et. }
    iMod "TH" as "[[[[THB THW] TKNH] TKNQ1] TKNQ0]".

    w_force_l. iSplitL "PRE TKNH".
    { iIntros "W". rewrite /token_half. unseal "SchA". iFrame. iPureIntro. esplits; et. }

    w_force_l. iSplitL ""; first done. 

    (* build IST *)
    rewrite /alist_upd /_alist_upd /=.
    set (st_tgt0 := [(SchI.v_ths, ((alist_add nths None ths_tgt): thslist)↑)]).
    iAssert (Ist (S nths) st_src st_tgt0) with "[COND THB THW TKNQ1]" as "IST".
    { iCombine "THW TKNQ1" as "THW". iExists _, _, _, _. iFrame.
      iPureIntro. esplits; et.
      - clear SIM. ss. split; [nia|]. rewrite alist_remove_find_None; et.
        induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct in THWF.
        des; des_ifs; split; [nia|et].
      - i. destruct (classic (tid = nths)).
        + subst. rewrite alist_add_find_eq. 
          rewrite !discrete_fun_lookup_op Nat.eqb_refl -H3 left_id -H4.
          econs 2; et.
        + rewrite alist_add_find_neq; et.
          rewrite discrete_fun_lookup_op.
          des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite right_id. et.
    }
    yield "IST"; et.

    w_steps_l. iClear "ASM".
    w_steps_r.
    w_force_l (nths ↑).
    w_force_l.
    iSplitL "TKNQ0"; iFrame; eauto.
    w_step. iFrame; easy.
  Qed.

  Lemma simF_yield : HSim.sim_fun open SchAMod SchIMod Ist SchName.yield.
  Proof.
    init_wpsim u_a u_i n.

    w_steps_l.
    iDestruct "ASM" as "[-> ->]". hss.

    w_steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss.
    w_steps_r.

    w_force_l q. w_step_l. w_step_l.
    w_force_l. iSplitL ""; first done.
    
    yield "THB THW COND".
    { iExists _, _, _, _. iSplit; et. iFrame. }

    w_steps_l. iClear "ASM".

    w_force_l (tt↑).
    w_force_l; iSplitL ""; first done.
    w_steps_r.
    w_step. iFrame; easy.
  Qed.

  Lemma simF_join : HSim.sim_fun open SchAMod SchIMod Ist SchName.join.
  Proof.
    init_wpsim u_a u_i n.

    w_step_l. w_step_l.
    destruct q as [tid postS]; s. w_steps_l.
    iDestruct "ASM" as "[[-> TOK] ->]". hss. rename q0 into tid.

    w_step_r.
    rewrite !/Sch.yield /ccallU. unseal "Sch".
    rewrite PModRed.interp_bind. rewrite HModSB.transl_bind. grind.

    iApply wpsim_reset. iStopProof.
    revert NODD.
    combine_quant NODS.
    combine_quant st_tgt.
    combine_quant st_src.
    combine_quant nths.
    eapply wpsim_coind. intros g' a.
    destruct a as [nths [st_src [st_tgt [NODS NODD]]]]. s.
    iIntros "[IST TKN] _ #CIH".

    unfold_iter_l; unfold_iter_r.

    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". des; subst; hss.
    w_steps_r. hss. w_steps_r.
    
    destruct (alist_find tid ths_tgt) eqn:LU; [destruct o|].
    { (* done(O) | joined(X) *)
      hexploit (SIM tid). intro T. rewrite LU in T. inv T.
      { (* done(O) *)
        iClear "CIH". w_step_r. w_step_r.
        w_force_l true. w_steps_l. w_force_l.
        w_steps_l.
        iPoseProof (big_sepM_delete with "COND") as "[POST COND]"; et.

        iCombine "THW TKN" gives %WF. iCombine "THW TKN" as "WF".
        rewrite auth_frag_valid in WF. specialize (WF tid). ss.
        rewrite discrete_fun_lookup_op Nat.eqb_refl -H2 -Some_op Some_valid in WF.
        rewrite -pair_op pair_valid frac_op in WF. des.

        apply agree_op_inv in WF0. dup WF0.
        apply (inj to_agree) in WF0.
        iAssert (interp_cond (postS t))%I with "[POST]" as "POST".
        { unfold interp_cond. specialize (WF0 t). ss. inv WF0. apply (inj to_agree) in H4.
          rewrite -H4. iApply "POST".
        }
        
        w_force_l. w_force_l. iSplitL "POST"; iFrame; et.
        assert (◯ (ths_src_w ⋅ (λ n: nat, if tid =? n then Some ((1/4)%Qp, to_agree (λ s: SAny.t, Some (to_agree (postS s)))) else ε) : threadsF) ≡ ◯ ((λ n: nat, if tid =? n then Some (1%Qp, to_agree (λ s: SAny.t, Some (to_agree (Q s)))) else ths_src_w n) : threadsF)).
        { f_equiv. intros y. rewrite !discrete_fun_lookup_op.
          destruct (decide (tid = y)).
          - subst. rewrite Nat.eqb_refl -WF1 -H2 -Some_op -pair_op frac_op agree_idemp.
            do 2 f_equiv. compute_done.
          - des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst; ss.
        }
        rewrite H0.

        w_step. iSplit; et. iExists _, _, _, _. iFrame. iPureIntro.
        esplits; et. i. destruct (classic (tid = tid0)).
        - subst. rewrite LU -H2 -H Nat.eqb_refl lookup_delete. econs.
        - des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite lookup_delete_ne; et.
      }
      { (* joined(X) *)
        iCombine "THW TKN" gives %WF. exfalso.
        rewrite auth_frag_valid in WF. specialize (WF tid). ss.
        rewrite discrete_fun_lookup_op -H2 Nat.eqb_refl -Some_op -pair_op frac_op in WF.
        rewrite Some_valid pair_valid in WF. des. ss.
      }
    }
    { (* active(O) *)
      set (st_tgt0 := [(SchI.v_ths, ths_tgt↑)]).
      iAssert (Ist nths st_src st_tgt0) with "[THB THW COND]" as "IST".
      { iExists _, _, _, _. iFrame. iPureIntro. esplits; et. }
      w_force_l false. w_steps_l. w_force_l (tt). w_force_l (tt↑).
      w_force_l; iSplitL ""; first done.

      w_call "IST".
      w_steps_l. iDestruct "ASM" as  "[-> ->]".
      w_steps_l. hss; w_steps_l.
      w_steps_r. hss; w_steps_r.
      rewrite /cgetU.
      by_coind "CIH". iFrame.
    }
    { (* idle(X) *)
      iCombine "THB TKN" gives %WF. exfalso.
      hexploit (SIM tid). intro STHS. rewrite LU in STHS. inv STHS.
      apply auth_both_valid_discrete in WF. des.
      apply (discrete_fun_included_spec_1 _ _ tid) in WF.
      ss. rewrite Nat.eqb_refl in WF. rewrite -H in WF.
      eapply fragree_incl_false. et.
    }
  Unshelve. all : ss.
  Qed.

  Lemma sim : HSim.t open SchAMod SchIMod SchA.InitCond Ist.
  Proof.
    init_sim.
    - rewrite /SchA.InitCond /initial_threads. unseal "SchA".
      iIntros "[THB THW]". iExists _, _, _, ∅.
      iFrame. rewrite big_sepM_empty. iSplitL; et.
      iPureIntro. esplits; et; ss; [split; nia |]. i. 
      rewrite// /SchAS.initial_threads_r eq_rel_dec_correct. des_ifs.
      + rewrite lookup_empty. econs 2.
      + rewrite Nat.eqb_eq in Heq0. subst; ss.
      + rewrite lookup_empty. econs.
    - ii. iIntros "IST". iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". des; subst.
      iExists _, _, _, _. iFrame. iPureIntro. i. esplits; [et| |et|nia].
      clear SIM. induction ths_tgt; ss. destruct a. des. splits; [nia|]. apply IHths_tgt; et.
    - eapply simF__spawn; eauto.
    - eapply simF_spawn; eauto.
    - eapply simF_yield; eauto.
    - eapply simF_join; eauto.
  Qed.
  End SchIA.

  Section SchIA.
    Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.
    Lemma wctxr Spc_global Spc_user n
        (SchInGlobal : ∀ u, spc_incl (SchAS.spc u n Spc_user) Spc_global)
        (UserInGlobal : spc_sub Spc_user Spc_global) :
      w_ctx_refines
        (λ u, SchA.t u n Spc_global Spc_user, SchA.InitCond)
        (λ _, SchI.t, emp%I).
    Proof. exists 1%positive; intros u v Huv; eapply main_adequacy, sim; eauto. Qed.
End SchIA. End SchIA.
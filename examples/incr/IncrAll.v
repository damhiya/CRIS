Require Import CRIS Cancel.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import IncrMainHeader IncrMainI IncrMainA IncrMainIAproof.
Require Import SchHeader SchI SchA SchIAproof SchTactics.

Module IncrAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; SchAΓ; memΓ; IncrMainAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Local Definition u : nat := 1.
  Local Definition ginv : iProp Σ := wsim_ginv u ⊤.

  Local Definition spc_user_s : string → option fspec :=
    to_spc (IncrMainAS.spc u ++ MemA.Spc).

  Local Definition smod_src : SMod.t :=
    (IncrMainA.Mod u) ☆ (MemA.Mod) ☆ (SchA.Mod u (spc_user_s u)).

  Local Definition spc_s : univ_id → string → option fspec :=
    λ u, spc_from (smod_src u).

  Local Definition smod_cancel : univ_id → HMod.t :=
    λ u, SModCancel.to_hmod (smod_src u).

  Local Definition mod_src : univ_id → HMod.t :=
    λ u, SMod.to_hmod (ginv u) (spc_s u) (smod_src u).

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Definition mod_tgt : HMod.t := IncrMainI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition SchInSpc : ∀ u, spc_incl (SchAS.spc u (spc_user_s u)) (spc_s u).
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.Spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MainInSpc : ∀ u, spc_incl (IncrMainAS.spc u) (spc_user_s u).
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.Spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MemInSpc : ∀ u, spc_incl MemA.Spc (spc_s u).
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.Spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.

  (* Local Definition ctxr := (IncrIA.wctxr ginv spc_s spc_user_s spc_s SchInSpc MainInSpc MemInSpc).

  Local Definition k := proj1_sig ctxr.
  Local Definition k_prf := proj2_sig ctxr.
  Local Definition u : nat := k.
  Local Definition v : nat := 0.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Definition smod_src : SMod.t := 
    (IncrMainA.Mod u) ☆ (MemA.Mod) ☆ (SchA.Mod u (spc_user_s u)).
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (ginv u) (spc_s u) smod_src.
  Local Definition mod_tgt : HMod.t := IncrMainI.t ★ (MemI.t csl genv) ★ (SchI.t). *)

  Local Definition init_cond : iProp Σ := MemA.InitCond csl genv ∗ SchA.InitCond.
  Local Definition main_fsp : univ_id → fspec := λ u, IncrMainAS.main_spec u.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    ∀ u,
      refines (smod_cancel u, (init_cond ∗ (main_fsp u).(precond) 0 tt tt↑ tt↑)%I) 
              (mod_src u, init_cond).
  Proof. i; eapply cancellation; try by econs. i. iIntros "[_ %POST]". iPureIntro. des; eauto. Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : ∃ k, refines (mod_src k, init_cond) (mod_tgt, emp%I).
  Proof.
    hexploit (IncrIA.wctxr ginv spc_s spc_user_s spc_s); eauto using SchInSpc, MainInSpc, MemInSpc.
    intros [k k_prf]; exists (k + 1).
    eapply ctxr_refines.
    rewrite -[(mod_src (k + 1), _)]hmod_addc_empty_l.
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    rewrite /mod_src /mod_tgt ?add_interp_comm /init_cond.
    rewrite -hmod_add_assoc. rewrite -hmod_add_assoc. rewrite assoc. eapply ctxr_compose_hor.
    { etrans.
      { eapply ctxr_cond_frameR.
        replace (SMod.to_hmod _ _ (IncrMainA.Mod (k + 1))) with (IncrMainA.t (k + 1) (ginv (k + 1)) (spc_s (k + 1))); cycle 1.
        { rewrite /IncrMainA.t; unseal CRIS; ss. }
        replace (SMod.to_hmod _ _ (MemA.Mod)) with (MemA.t (ginv (k + 1)) (spc_s (k + 1))); cycle 1.
        { rewrite /MemA.t; unseal CRIS; ss. }
        eapply (k_prf _ 1); lia.
      }
      { eapply ctxr_frameL. etrans; first eapply ctxr_cond_frameL, MemIA.correct.
        { eauto using MemInSpc. }
        { eapply ctxr_cond_strengthen; eauto. }
      }
    }
    eapply main_adequacy.
    replace (SMod.to_hmod _ _ (SchA.Mod (k + 1) (spc_user_s (k + 1)))) with (SchA.t (k + 1) (spc_s (k + 1)) (spc_user_s (k + 1))); cycle 1.
    { rewrite /SchA.t; unseal CRIS; ss. }
    eapply SchIA.sim; eauto using SchInSpc.
    { rewrite /spc_sub /spc_user_s /spc_s /IncrMainAS.spc /MemA.Spc; unseal CRIS. ii; ss.
      des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
  Qed.

  Lemma cancel_tgt :
    ∃ u,
    refines (smod_cancel u, (init_cond ∗ (main_fsp u).(precond) 0 tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    pose proof src_tgt as [k H]; exists k.
    etrans.
    { eapply cancel_src. }
    { done. }
  Qed.

  Local Definition initial_resource : Σ :=
    (MemA.mem_init_res csl genv) ⋅ SchAS.initial_resource.
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    dfs_unfold; dfs_merge; dfs_to_list; dfs_resolve.
    { rewrite /SchAΣ in x.
      rewrite inG_id_subG_inG in x.
      inv_instances.solve_in_subG_goal.
      rewrite ?/eq_rec_r ?/eq_rec in x; try rewrite -!eq_rect_eq in x; ss; eauto.
    }
    { dfs_split; dfs_simplify.
      { pose proof mem_initial_valid csl genv. eapply cmra_valid_op_l; eauto. }
      { rewrite /SchAS.initial_threads_r; eapply auth_both_valid_discrete; split.
        { exists (λ tid, if (tid =? 0) then Some ((3/4)%Qp, to_agree (λ _ : SAny.t, Some (to_agree (existT 0 ⊤%SRF)))) else None).
          intros i; des_ifs; ss; [rewrite Nat.eqb_eq in Heq|rewrite Nat.eqb_neq in Heq]; clarify; ss.
          { rewrite discrete_fun_lookup_op //= -Some_op -pair_op frac_op; repeat f_equiv; ss.
            { rewrite Qp.quarter_three_quarter; ss. }
            { rr; ii; split; ii; esplits; eauto; try set_solver. }
          }
          { rewrite discrete_fun_lookup_op; des_ifs; rewrite Nat.eqb_eq in Heq0; ss. }
        }
        { ii; des_ifs; ss. }
      }
    }
  Qed.

  Theorem behavioral_refinement :
    ∃ u target_resource, refines_mod
      (HMod.to_mod (smod_cancel u) initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>[u H]; rewrite /refines in H; ss; exists u.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros "[M S]".
      rewrite /init_cond /MemA.InitCond /SchA.InitCond /precond /main_fsp /IncrMainAS.main_spec; ss.
      rewrite /precond /fspec_simple /=.
      admit.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Admitted.
End IncrAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)

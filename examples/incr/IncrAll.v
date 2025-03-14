Require Import CRIS Cancel.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import IncrMainHeader IncrMainI IncrMainA IncrMainIAproof.
Require Import SchHeader SchI SchA SchIAproof SchTactics.

Module IncrAll.
  Import inv_instances.
  Local Definition u : univ_id := 1.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; IncrMainAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Definition IRΓ : Γ :=
    **[ir_invΓ u; ir_memΓ csl genv; SchAS.ir_SchAΓ; *[None]].
  Definition IRΣ : Σ :=
    **[ir_invΣ u; SchAS.ir_SchAΣ; IRΓ].

  Lemma IRΣ_valid : ✓ (IRΣ ⋅ initial_resource_own_admin).
  Proof.
    eapply InitRes.app_valid.
    { rewrite /ir_invΣ. apply InitRes.app_valid.
      { apply InitRes.singleton_some_valid, ir_ownIRA_valid. }
      { intros i; inv_fin i. }
    }
    apply InitRes.app_valid.
    { apply InitRes.app_valid.
      { apply InitRes.singleton_some_valid, SchAS.ir_threadsRA_valid. }
      { intros i; inv_fin i. }
    }
    apply InitRes.app_valid.
    { apply InitRes.app_valid.
      { rewrite /ir_invΓ. apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, ir_ownERA_valid. }
        { apply InitRes.app_valid.
          { apply InitRes.singleton_some_valid, ir_ownDRA_valid. }
          { intros i; inv_fin i. }
        }
      }
      apply InitRes.app_valid.
      { rewrite /ir_memΓ. apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, ir_memRA_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, SchAS.ir_tidRA_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_none_valid. }
        { intros i; inv_fin i. }
      }
      { intros i; inv_fin i. }
    }
    { intros i; inv_fin i. }
  Qed.

  (* source module *)
  Local Definition spc_user_s : string → option fspec :=
    to_spc (IncrMainAS.spc u ++ MemA.spc).
  Local Definition smod_src : SMod.t :=
    (IncrMainA.Mod u) ☆ (MemA.Mod) ☆ (SchA.Mod u spc_user_s).
  Local Definition spc_s : string → option fspec := spc_from smod_src.

  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition mod_tgt : HMod.t := IncrMainI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s.
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MainInSpc : spc_incl (IncrMainAS.spc u) spc_user_s.
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MemInSpc : spc_incl MemA.spc spc_s.
  Proof.
    ii; rewrite /spc_s /SchAS.spc /MemA.spc /IncrMainAS.spc; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.

  Local Definition init_cond : iProp Σ := MemA.init_cond csl genv ∗ SchA.init_cond.
  Local Definition main_fsp : fspec := IncrMainAS.main_spec u.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (smod_cancel, (init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I) 
            (mod_src, init_cond).
  Proof. i; eapply cancellation; try by econs. i. iIntros "[_ [_ %POST]]". iPureIntro. des; eauto. Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    hexploit (IncrIA.wctxr u spc_s spc_user_s spc_s); eauto using SchInSpc, MainInSpc, MemInSpc.
    i; eapply ctxr_refines.
    rewrite -[(mod_src, _)]hmod_addc_empty_l.
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    rewrite /mod_src /mod_tgt ?add_interp_comm /init_cond.
    rewrite -hmod_add_assoc. rewrite -hmod_add_assoc. rewrite assoc. eapply ctxr_compose_hor.
    { etrans.
      { eapply ctxr_cond_frameR.
        replace (SMod.to_hmod _ _ (IncrMainA.Mod u)) with (IncrMainA.t u spc_s); cycle 1.
        { rewrite /IncrMainA.t; unseal CRIS; ss. }
        replace (SMod.to_hmod _ _ MemA.Mod) with (MemA.t u spc_s); cycle 1.
        { rewrite /MemA.t; unseal CRIS; ss. }
        eauto.
      }
      { eapply ctxr_frameL. etrans; first eapply ctxr_cond_frameL, MemIA.wctxr.
        { eauto using MemInSpc. }
        { eapply ctxr_cond_strengthen; eauto. }
      }
    }
    eapply main_adequacy.
    replace (SMod.to_hmod _ _ (SchA.Mod u spc_user_s)) with (SchA.t u spc_s spc_user_s); cycle 1.
    { rewrite /SchA.t; unseal CRIS; ss. }
    eapply SchIA.sim; eauto using SchInSpc.
    { rewrite /spc_sub /spc_user_s /spc_s /IncrMainAS.spc /MemA.spc; unseal CRIS. ii; ss.
      des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
  Qed.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel (IRΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H (IRΣ ⋅ initial_resource_own_admin)).
    { apply IRΣ_valid. }
    { rewrite /IRΣ /InitRes.app.
      try (repeat rewrite ?InitRes.L_distr ?InitRes.R_distr).
      iIntros "[[[I _] [[THS _] [[[E [D _]] [[M _] [[TID _] _]]] _]]] O]".
      iPoseProof (make_wsats u with "[I E D]") as "[U W]".
      { iSplitL "I".
        { solve_index "I". f_equal. }
        iSplitL "E".
        { solve_index "E". f_equal. }
        { solve_index "D". f_equal. }
      }
      iAssert (SchAS.tid_admin None) with "[TID]" as "TID".
      { rewrite /SchAS.tid_admin. unseal "SchA". solve_index "TID". f_equal. }
      iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[H1 H2]".
      { iSplitR "U W O H2"; cycle 1.
        { iPoseProof (make_own_admin with "O") as "$". unfold_pre_post; iFrame. iSplit; eauto. }
        rewrite /init_cond. iSplitL "M".
        { iAssert (mem_init csl genv) with "[M]" as "[$ _]".
          { rewrite /mem_init. solve_index "M". f_equal. }
        }
        iSplitL "THS".
        { rewrite /SchAS.init_threads. unseal "SchA". solve_index "THS". f_equal. }
        { iFrame. }
      }
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End IncrAll.
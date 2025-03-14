Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonMainA.
Require Import CannonIAproof CannonMainIAproof.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; CannonAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].
  Local Definition irΓ : Γ := **[ir_invΓ 1; CannonAS.irΓ].
  Local Definition irΣ : Σ := **[ir_invΣ 1; irΓ].

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    eapply InitRes.app_valid.
    { rewrite /ir_invΣ.
      apply InitRes.app_valid.
      { apply InitRes.singleton_some_valid, ir_ownIRA_valid. }
      { intros i; inv_fin i. }
    }
    eapply InitRes.app_valid.
    { eapply InitRes.app_valid.
      { rewrite /ir_invΓ.
        apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, ir_ownERA_valid. }
        apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, ir_ownDRA_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { rewrite /CannonAS.irΓ. apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, CannonAS.ir_valid. }
        { intros i; inv_fin i. }
      }
      { intros i; inv_fin i. }
    }
    { intros i; inv_fin i. }
  Qed.

  Local Definition smod_src : SMod.t := CannonA.Mod ☆ (MainA.Mod 1).
  Local Definition spc : string → option fspec := spc_from smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod emp spc smod_src.
  Local Definition mod_tgt : HMod.t := CannonI.t ★ (MainI.t 1).

  Local Definition main_fsp : fspec := MainAS.main_spec.
  Local Definition init_cond : iProp Σ := CannonA.init_cond ∗ MainA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I) 
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines. 
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    unfold mod_src, mod_tgt. rewrite add_interp_comm.
    eapply ctxr_compose_hor.
    { replace (SMod.to_hmod _ _ CannonA.Mod) with (CannonA.t spc); cycle 1.
      { unfold CannonA.t. unseal CRIS. ss. }
      eapply CannonIA.ctxr.
    }
    { replace (SMod.to_hmod _ _ (MainA.Mod 1)) with (MainA.t 1 spc); cycle 1.
      { unfold MainA.t. unseal CRIS. ss. }
      eapply CannonMainIA.ctxr.
      i. rewrite /CannonAS.Spc. unseal CRIS. econs; first prove_nodup.
      ii; rewrite -FIND /spc /spc_from /smod_src //=; des_ifs; ss; des_ifs.
    }
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { rewrite /irΣ /InitRes.app.
      try (repeat rewrite ?InitRes.L_distr ?InitRes.R_distr).
      iIntros "[[[I _] [[[E [D _]] [[M _] _]] _]] O]".
      iPoseProof (make_wsats 1 with "[I E D]") as "[U W]".
      { iSplitL "I".
        { solve_index "I". f_equal. }
        iSplitL "E".
        { solve_index "E". f_equal. }
        { solve_index "D". f_equal. }
      }
      iPoseProof (CannonAS.ReadyBall with "[M]") as "[R B]".
      { rewrite /CannonAS.Fired. solve_index "M". f_equal. }
      iSplitL "R".
      { rewrite /init_cond. iFrame. }
      unfold_pre_post. iFrame. iSplit; eauto.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)

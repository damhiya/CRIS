Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonMainA.
Require Import CannonIAproof CannonMainIAproof.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; CannonAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].

  Local Definition smod_src : SMod.t := CannonA.Mod ☆ (MainA.Mod 1).
  Local Definition u : univ_id := 1.
  Local Definition spc : string → option fspec := spc_from smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc smod_src.
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
    { replace (SMod.to_hmod _ _ CannonA.Mod) with (CannonA.t u spc); cycle 1.
      { unfold CannonA.t. unseal CRIS. ss. }
      eapply CannonIA.correct.
    }
    { replace (SMod.to_hmod _ _ (MainA.Mod 1)) with (MainA.t 1 u spc); cycle 1.
      { unfold MainA.t. unseal CRIS. ss. }
      eapply CannonMainIA.correct.
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

  Local Definition initial_resource : Σ := MainAS.init_res ⋅ CannonAS.init_res.
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    dfs_solve.
    apply excl_auth_valid.
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros "I"; rewrite /init_cond /CannonA.init_cond /MainA.init_cond.
      rewrite /precond /= /CannonAS.Ready /CannonAS.Ball
        own.Own_eq own.own_eq /own.Own_def /own.own_def.
      rewrite /initial_resource /MainAS.init_res /CannonAS.init_res. Set Printing Implicit.
      iDestruct "I" as "[I1 I2]"; iFrame. iSplit; iPureIntro; ss.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)

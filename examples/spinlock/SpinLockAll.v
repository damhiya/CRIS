Require Import CRIS.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SpinLockHeader SpinLockI SpinLockA SpinLockIAProof.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA SpinLockMainIAProof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import ElimRel SModCancel Cancellation.

Module SpinLockAll.
  Import inv_instances.
  Local Definition u : univ_id := 1.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Definition irΓ : Γ :=
    **[ir_invΓ u; ir_memΓ csl genv; SchAS.ir_SchAΓ; ir_SpinLockΓ; ir_SpinLockMainAΓ].
  Definition irΣ : Σ :=
    **[ir_invΣ u; SchAS.ir_SchAΣ; irΓ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_ownIRA_valid.
    - apply SchAS.ir_threadsRA_valid.
    - apply ir_ownERA_valid.
    - apply ir_ownDRA_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
  Qed.

  (* building the target module *)
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* building the source module *)
  Local Definition spc_user_s : string → option fspec :=
    to_spc (SpinLockMainAS.spc u ++ MemA.spc ++ SpinLockAS.spc u).
  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod u ☆ MemA.Mod ☆ SchA.Mod u spc_user_s ☆ SpinLockA.Mod u.
  Local Definition spc_s : string → option fspec :=
    spc_from smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition init_cond : iProp Σ := (MemA.init_cond csl genv ∗ SchA.init_cond)%I.

  (* source module after cancellation *)
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  (* Some assumptions on spc inclusion *)
  Lemma SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s.
  Proof.
    rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
    ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Lemma MainInSpc : spc_incl (SpinLockMainAS.spc u) spc_user_s.
  Proof.
    rewrite /spc_user_s /SpinLockMainAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
    ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Lemma MemInSpc : spc_incl (MemA.spc) spc_s.
  Proof.
    rewrite /spc_user_s /MemA.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
    ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Lemma UserInSpc : spc_sub spc_user_s spc_s.
  Proof.
    rewrite /spc_user_s /spc_s /MemA.spc; unseal CRIS.
    ii; ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
    
  (* Refinement between smod_cancel and smod_src *)
  Local Definition main_fsp : fspec := SpinLockMainAS.main_spec u.
  Lemma cancel_src :
    refines (smod_cancel, init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I
            (mod_src,     init_cond).
  Proof. eapply cancellation; try by econs. i. unfold_pre_post. iIntros "[_ [-> ->]]". done. Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond ?add_interp_comm.
    etrans.
    { do 2 eapply ctxr_frameL. eapply ctxr_comm. }
    do 2 rewrite -hmod_add_assoc.
    etrans.
    { eapply ctxr_frameR.
      replace (SMod.to_hmod _ _ (SpinLockMainA.Mod _)) with (SpinLockMainA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      replace (SMod.to_hmod _ _ (MemA.Mod)) with (MemA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      replace (SMod.to_hmod _ _ (SpinLockA.Mod _)) with (SpinLockA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_add_assoc -hmod_addc_empty_l.
      etrans; first eapply ctxr_cond_frameR.
      { eapply SpinLockMainIA.wctxr; eauto.
        { apply SchInSpc. }
        { apply MainInSpc. }
        { apply MemInSpc. }
      }
      rewrite hmod_addc_empty_l. refl.
    }
    rewrite hmod_add_assoc. eapply ctxr_frameL.
    etrans.
    { eapply ctxr_frameR. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      etrans; first eapply ctxr_comm.
      eapply SpinLockIA.wctxr.
      { apply SchInSpc. }
      { apply MemInSpc. }
    }
    rewrite hmod_add_assoc.
    etrans; first eapply ctxr_comm. rewrite -hmod_add_assoc. eapply ctxr_frameR.
    etrans.
    { rewrite hmod_addc_empty_l. eapply ctxr_frameR, ctxr_cond_frameR. eapply MemIA.wctxr.
      apply MemInSpc.
    }
    eapply ctxr_frameL.
    etrans.
    { replace (SMod.to_hmod _ _ (SchA.Mod _ _)) with (SchA.t u spc_s spc_user_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_addc_empty_l.
      eapply SchIA.wctxr.
      { apply SchInSpc. }
      { apply UserInSpc. }
    }
    refl.
  Qed.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ (main_fsp).(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H ((irΣ ⋅ initial_resource_own_admin))).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { iAssert (SchAS.tid_admin None) with "[H22]" as "TID".
        { rewrite /SchAS.tid_admin. unseal "SchA". iFrame. }
        iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[TID1 TID2]".
        { iSplitR "U W H1 TID2"; cycle 1.
          { iPoseProof (make_own_admin with "H1") as "$".
            unfold_pre_post; iFrame. eauto. }
          rewrite /init_cond. iSplitL "H24".
          { iAssert (mem_init csl genv) with "[H24]" as "[$ _]". eauto. }
          iSplitL "H30".
          { rewrite /SchAS.init_threads. unseal "SchA". eauto. }
          { iFrame. }
        }
      }
      all: solve_res.
    }
    { econs; ss; prove_nodup. }
    { exists x; des; eauto. }
  Qed.

End SpinLockAll.

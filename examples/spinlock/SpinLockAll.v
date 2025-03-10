Require Import CRIS.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SpinLockHeader SpinLockI SpinLockA SpinLockIAProof.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA SpinLockMainIAProof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import ElimRel SModCancel Cancellation.

(* From iris Require Import frac_auth numbers. *)
Module SpinLockAll.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.

  Instance τ : TypG.t := λ _, ST.t.
  Instance typG : CtxST.t τ. Proof. econs. econs. instantiate (1:=0); ss. Qed.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].
  Local Instance α : SRFCons.t :=
    λ n,
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].
  Local Instance sub : subG Γ Σ.
  Proof. do 2 apply subG_app_r. apply subG_refl. Defined.
  Local Instance invG : invG α Σ Γ.
  Proof. econs. { econs. exists 0%fin. ss. } { econs. { exists 0%fin. ss. } { exists 1%fin. ss. } } Defined.
  Instance β : SRFIntp.t :=
    λ n,
      match n with
      | 0 => SL.interp
      | _ => inv_interp
      end.
  Local Instance intpG : SRFIntp.inG (@SL.syntax τ Γ) α (@SL.interp τ α Γ Σ _) β.
  Proof. econs; instantiate (1:=0); ss. Qed.

  Local Instance invintpG : SRFIntp.inG inv_syntax α inv_interp β.
  Proof. econs; instantiate (1:=1); ss. Qed.

  Local Instance sinvg : sinvG Σ Γ α β τ.
  Proof. econs; econs; try typeclasses eauto. Qed.

  Local Instance memΓ : memGΓ Γ.
  Proof. econs. exists 2%fin; ss. Defined.

  Local Instance SchAΓ : SchAGΓ Γ.
  Proof. econs. exists 3%fin; ss. Defined.

  Local Instance SpinLockAGΓ : SpinLockAGΓ Γ.
  Proof. econs. exists 4%fin; ss. Defined.

  Local Instance SpinLockMainAGΓ : SpinLockMainAGΓ Γ.
  Proof. econs. exists 5%fin; ss. Defined.

  Local Instance SchAΣ : SchAGΣ Σ.
  Proof. econs. exists 1%fin; ss. Defined.

  (* building the target module *)
  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* building the source module *)
  Local Definition u : univ_id := 1.

  Local Definition spc_user_s : string → option fspec :=
    to_spc (SpinLockMainAS.spc u ++ MemA.Spc ++ SpinLockAS.spc u).

  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod u ☆ MemA.Mod ☆ SchA.Mod u spc_user_s ☆ SpinLockA.Mod u.
  Local Definition spc_s : string → option fspec :=
    spc_from smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition init_cond : iProp Σ := (MemA.InitCond csl genv ∗ SchA.InitCond)%I.

  (* source module after cancellation *)
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.

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
    replace (SMod.to_hmod _ _ (SpinLockMainA.Mod _)) with (SpinLockMainA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }
    replace (SMod.to_hmod _ _ (MemA.Mod)) with (MemA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }
    replace (SMod.to_hmod _ _ (SpinLockA.Mod _)) with (SpinLockA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }

    etrans.
    { do 2 eapply ctxr_frameL. eapply ctxr_comm. }
    do 2 rewrite -hmod_add_assoc.
    etrans.
    { eapply ctxr_frameR.
      rewrite hmod_add_assoc -hmod_addc_empty_l.
      etrans; first eapply ctxr_cond_frameR.
      { eapply SpinLockMainIA.wctxr; eauto.
        { instantiate (1:=spc_user_s).
          rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /MemA.Spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
      }
      rewrite hmod_addc_empty_l. refl.
    }
    rewrite hmod_add_assoc. eapply ctxr_frameL.
    etrans.
    { eapply ctxr_frameR. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      etrans; first eapply ctxr_comm.
      eapply SpinLockIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /spc_s /smod_src /MemA.Spc; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
    }
    rewrite hmod_add_assoc.
    etrans; first eapply ctxr_comm. rewrite -hmod_add_assoc. eapply ctxr_frameR.
    etrans.
    { rewrite hmod_addc_empty_l. eapply ctxr_frameR, ctxr_cond_frameR. eapply MemIA.wctxr.
      rewrite /MemA.Spc; unseal CRIS.
      split; first prove_nodup. ii; ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
    eapply ctxr_frameL.
    etrans.
    { replace (SMod.to_hmod _ _ (SchA.Mod _ _)) with (SchA.t u spc_s spc_user_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_addc_empty_l.
      eapply SchIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src /MemA.Spc; unseal CRIS.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
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

  Import rListNotations.
  Local Definition initial_resource_list : res_list :=
    [ownIRA_resource u; ownERA_resource u; ownDRA_resource u;
     SchAS.tidRA_resource; SchAS.threadsRA_resource; memRA_resource csl genv]%res_list.

  Local Definition initial_resource : Σ := 
    (op_res_list initial_resource_list) ⋅ initial_resource_own_admin.

  Ltac dfs_solve :=
    econs; [repeat (intros [C | C]; [inv C|]; revert C); intros []|].
    
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    apply op_res_list_valid.
    repeat dfs_solve. econs.
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros "H". iPoseProof (big_bang with "H") as "[O H]".
      iDestruct "H" as "[H1 [H2 [H3 [H4 [H5 [H6 _]]]]]]"; iFrame.
      iPoseProof (ownI_initial_gen with "[$]") as "[U W]".
      iPoseProof (SchAS.tid_admin_none_split with "[H4]") as "[H3 H4]".
      { rewrite /SchAS.tid_admin; unseal "SchA"; ss. }
      iFrame. des_ifs. unfold_pre_post. iSplitL.
      { iSplitR "H5".
        { iDestruct "H6" as "[$ $]". }
        { rewrite /SchAS.initial_threads. unseal "SchA". done. }
      }
      iSplit; eauto.
    }
    { econs; ss; prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End SpinLockAll.
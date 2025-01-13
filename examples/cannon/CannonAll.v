Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonASpec CannonMainA CannonMainASpec.
Require Import CannonIAproof CannonMainIAproof.
Require Import ElimRel SModCancel Cancellation.

Module CannonAll. Section CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; CannonAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].

  Local Definition smod_src : SMod.t := CannonA.Mod ☆ (MainA.Mod 1).
  Local Definition ginv : Sk.t → invspec := λ _ _, True%I.
  Local Definition stb : Sk.t → gname → option fspec := stb_global smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod ginv stb smod_src.
  Local Definition mod_tgt : HMod.t := CannonI.t ★ (MainI.t 1).

  Local Definition main_fsp : fspec := MainAS.main_spec.
  Local Definition init_cond : Sk.t → iProp Σ := CannonA.init_cond ∗∗ MainA.init_cond.
  Local Definition skeleton : Sk.t := Sk.add CannonSK.t MainSK.t.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, init_cond ∗∗ (λ _, main_fsp.(precond) 0 tt tt↑ tt↑)) 
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, const(emp)%I).
  Proof.
    eapply ctxr_refines. 
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    unfold mod_src, mod_tgt. rewrite add_interp_comm.
    eapply ctxr_compose_hor.
    { replace (SMod.to_hmod ginv stb CannonA.Mod) with (CannonA.t ginv stb); cycle 1.
      { unfold CannonA.t. unseal "ccr". ss. }
      eapply CannonIA.correct.
    }
    { replace (SMod.to_hmod ginv stb (MainA.Mod 1)) with (MainA.t 1 ginv stb); cycle 1.
      { unfold MainA.t. unseal "ccr". ss. }
      eapply CannonMainIA.correct.
      i. rewrite /CannonAS.Stb. unseal "ccr". econs; first prove_nodup.
      ii; rewrite -FIND /stb /stb_global /smod_src //=; des_ifs; ss; des_ifs.
    }
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, init_cond ∗∗ (λ _, main_fsp.(precond) 0 tt tt↑ tt↑))
            (mod_tgt, const(emp)%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Definition initial_resource : Σ := MainAS.init_res ⋅ CannonAS.init_res.
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    rewrite /initial_resource /MainAS.init_res /CannonAS.init_res -own.iRes_singleton_op.
    apply discrete_fun_singleton_valid, allocs.allocs_frag_valid,
      cmra_transport_valid, excl_auth_valid.
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_modsem
      (HModSem.to_mod ((HMod.modsem mod_cancel) skeleton) initial_resource)
      (HModSem.to_mod ((HMod.modsem mod_tgt) skeleton) target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (REF skeleton initial_resource).
    { rewrite /CannonI.t /MainI.t /skeleton; unseal "ccr"; ss. }
    { rewrite /skeleton /CannonSK.t /MainSK.t; ss; econs; ii; ss; des; ss; prove_nodup. }
    { apply initial_resource_valid. }
    { iIntros "I"; rewrite /init_cond /CannonA.init_cond /MainA.init_cond /HMod.addc.
      rewrite /precond /= /CannonAS.Ready /CannonAS.Ball
        own.Own_eq own.own_eq /own.Own_def /own.own_def.
      iDestruct "I" as "[I1 I2]"; iFrame. iSplit; iPureIntro; ss.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End CannonAll. End CannonAll.
Print Assumptions CannonAll.behavioral_refinement.
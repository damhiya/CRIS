Require Import CRIS.

Require Import MapHeader MapASpec MapMSpec MapI ModSim MapIMproof MapMAproof MemA.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.

  Theorem correct gi (StbMap StbMem : Sk.t → string → option fspec)
      (MapInStbMap : ∀ sk, stb_incl MapAS.Stb (StbMap sk)) :
    ctx_refines
      ((MapAS.t gi StbMap)  ★ (MemA.t gi StbMem), MapAS.InitCond ∗∗ MapMS.InitCond)
      ((MapI.t)             ★ (MemA.t gi StbMem), const(emp%I)).
  Proof.
    etrans; cycle 1.
    { eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= const(to_stb MapMS.Stb)).
      i. split; try refl. unfold MapMS.Stb. unseal CRIS. prove_nodup.
    }
    etrans; cycle 1.
    { eapply ctxr_frameR.
      rewrite -(hmod_addc_empty_l _ MapMS.InitCond).
      eapply ctxr_cond_frameR, main_adequacy, MapMA.sim; eauto.
      intros sk; split; try refl.
      rewrite /MapMS.Stb; unseal CRIS; prove_nodup.
    }
    refl.
  Qed.
End MapIA. End MapIA.
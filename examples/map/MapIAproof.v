Require Import CRIS.

Require Import MapHeader MapA MapM MapI ModSim MapIMproof MapMAproof MemA.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.

  Theorem correct gi (SpcMap SpcMem : string → option fspec)
      (MapInSpcMap : spc_incl MapAS.Spc SpcMap) :
    ctx_refines
      ((MapA.t gi SpcMap)  ★ (MemA.t gi SpcMem), (MapA.InitCond ∗ MapM.InitCond)%I)
      ((MapI.t)            ★ (MemA.t gi SpcMem), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= to_spc MapMS.Spc).
      i. split; try refl. unfold MapMS.Spc. unseal CRIS. prove_nodup.
    }
    etrans; cycle 1.
    { eapply ctxr_frameR.
      rewrite -(hmod_addc_empty_l _ MapM.InitCond).
      eapply ctxr_cond_frameR, main_adequacy, MapMA.sim; eauto.
      split; try refl.
      rewrite /MapMS.Spc; unseal CRIS; prove_nodup.
    }
    refl.
  Qed.
End MapIA. End MapIA.

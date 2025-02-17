Require Import CRIS.

Require Import MapHeader MapA MapM MapI ModSim MapIMproof MapMAproof MemA wpsim.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.
  Context (υ : univ_id) (n : level).
  Context `((υ > 2)%positive).

  Theorem correct gi (SpcMap SpcMem : string → option fspec)
      (MapInSpcMap : spc_incl (MapAS.Spc υ n) SpcMap) :
    ctx_refines
      ((MapA.t υ n gi SpcMap)  ★ (MemA.t gi SpcMem), (MapA.InitCond ∗ MapM.InitCond)%I)
      ((MapI.t)                ★ (MemA.t gi SpcMem), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= to_spc (MapMS.Spc 1%positive n)).
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
  Unshelve. r; lia.
  Qed.
End MapIA. End MapIA.

Module w_MapIA. Section w_MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.
  Context (n : level).
  Theorem correct gi (SpcMap : univ_id → string → option fspec) (SpcMem : string → option fspec)
      (MapInSpcMap : ∀ υ, spc_incl (MapAS.Spc υ n) (SpcMap υ)) :
    w_ctx_refines
      ((λ υ, (MapA.t υ n gi (SpcMap υ)) ★ (MemA.t gi SpcMem)), (MapA.InitCond ∗ MapM.InitCond)%I)
      ((λ _, (MapI.t)                   ★ (MemA.t gi SpcMem)), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIMproof.wctxr.
      instantiate (1:= λ u, to_spc (MapMS.Spc u%positive n)).
      i. split; try refl. unfold MapMS.Spc. unseal CRIS. prove_nodup.
    }
    etrans; cycle 1.
    { eapply w_ctx_refines_frameR.
      rewrite -(hmod_addc_empty_l _ MapM.InitCond).
      etrans; first eapply wctxr.
      {  }
      rewrite -[MapM.InitCond]/(MapM.InitCond ∗ emp)%I.
      instantiate (1:=(emp%I ∗ MapM.InitCond)%I).
      eapply w_ctx_refines_cond_frameR.
      (* rewrite -(hmod_addc_empty_l _ MapM.InitCond). *)
      eapply ctxr_cond_frameR, main_adequacy, MapMA.sim; eauto.
      split; try refl.
      rewrite /MapMS.Spc; unseal CRIS; prove_nodup.
    }
    refl.
  Unshelve. r; lia.
  Qed.
End w_MapIA. End w_MapIA.
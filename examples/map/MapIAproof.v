Require Import CRIS.

Require Import MapHeader MapA MapM MapI ModSim MapIMproof MapMAproof MemA wsim.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.
  Context (n : level).

  Lemma wctxr gi (SpcMap : univ_id → string → option fspec) (SpcMem : string → option fspec)
      (MapInSpcMap : ∀ υ, spc_incl (MapAS.Spc υ n) (SpcMap υ)) :
    w_ctx_refines
      ((λ υ, (MapA.t υ n gi (SpcMap υ)) ★ (MemA.t gi SpcMem)), (MapA.InitCond ∗ MapM.InitCond)%I)
      ((λ _, (MapI.t)                   ★ (MemA.t gi SpcMem)), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIM.wctxr.
      instantiate (1:= λ u, to_spc (MapMS.Spc u%positive n)).
      i. split; try refl. unfold MapMS.Spc. unseal CRIS. prove_nodup.
    }
    eapply w_ctx_refines_frameR.
    eapply w_ctx_refines_cond_strengthen; first (instantiate (1:=(emp ∗ MapM.InitCond)%I)).
    { iIntros "[_ $]". }
    eapply w_ctx_refines_cond_frameR, MapMA.wctxr; eauto.
    split; try refl.
    rewrite /MapMS.Spc; unseal CRIS; prove_nodup.
  Qed.
End MapIA. End MapIA.
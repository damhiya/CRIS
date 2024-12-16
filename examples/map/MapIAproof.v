Require Import Coqlib ITreelib.
Require Import MapHeader MapASpec MapMSpec MapI ModSim MapIMproof MapMAproof MemA.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import IPM sWorld.

Require Import STB.
Require Import ISim SMod HMod.
Require Import MainAdequacy CtxRefine CtxRefineFacts.

Module MapIA. Section MapIA.
  Context `{!Inv.t Σ Γ α β τ, !MapAS.G Γ, !MapMS.G Γ, !memG Γ}.

  Theorem correct gi (StbMap StbMem : Sk.t → gname → option fspec)
      (MapInStbMap : ∀ sk, stb_incl MapAS.Stb (StbMap sk)) :
    ctx_refines
      ((MapAS.t gi StbMap)  ★ (MemA.t gi StbMem), MapAS.InitCond ∗∗ MapMS.InitCond)
      ((MapI.t)             ★ (MemA.t gi StbMem), const(emp%I)).
  Proof.
    etrans; cycle 1.
    { eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= const(to_stb MapMS.Stb)).
      i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup. }
    etrans; cycle 1.
    { eapply ctxr_frameR.
      rewrite -(hmod_addc_empty_l _ MapMS.InitCond).
      eapply ctxr_cond_frameR, main_adequacy, MapMA.sim; eauto.
      intros sk; split; try refl.
      rewrite /MapMS.Stb; unseal "ccr"; prove_nodup.
    }
    refl.
  Qed.
End MapIA. End MapIA.
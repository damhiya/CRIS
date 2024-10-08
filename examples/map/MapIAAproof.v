Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapASpec MapMSpec MapI MapM MapA MapAA ModSim MapIMproof MapMAproof MapAAAproof MemA.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Events Behavior CtxRefine CtxRefineFacts.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import STB.
Require Import ISim SMod HMod Mod ModSimFacts.
Require Import MainAdequacy CtxRefine.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapIA.
Section PROOF.
  Context `{_W: CtxWD.t}.
  Context `{_M: MapMR.t (Γ:=Γ)}.
  Context `{_A: MapAR.t (Γ:=Γ)}.
  Context `{@GRA.inG memRA Γ}.

  Theorem correct gi (StbMap StbMem: Sk.t -> gname -> option fspec)
    (MapInStbMap: forall sk, stb_incl MapAS.Stb (StbMap sk))
    :
    ctx_refines
      ((MapAA.t gi StbMap) ★ (MemA.t gi StbMem), MapA.InitCond ∗∗ MapM.InitCond)
      ((MapI.t)            ★ (MemA.t gi StbMem), const(emp%I)).
  Proof.
    etrans; cycle 1.
    { eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= const(to_stb MapMS.Stb)).
      i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup. }
    etrans; cycle 1.
    { eapply ctxr_frameR.
      rewrite <-(hmod_addc_empty_l MapM.InitCond).
      eapply ctxr_cond_frameR.
      eapply main_adequacy. eapply MapMA.sim; eauto.
      i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup. }
    { eapply ctxr_frameR.
      rewrite <-(hmod_addc_empty_l (_ ∗∗ _)).
      eapply ctxr_cond_frameR.
      eapply main_adequacy. eapply MapAAA.sim; eauto.
    }
  Unshelve. eauto.
  Qed.

End PROOF.
End MapIA.

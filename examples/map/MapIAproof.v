Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapASpec MapMSpec MapI MapM MapA ModSim MapIMproof MapMAproof MemA.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Events Behavior CtxRefine.
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

  Theorem correct (StbMap StbMem: Sk.t -> gname -> option fspec)
    (MapInStbMap: forall sk, stb_incl MapAS.Stb (StbMap sk))
    :
    ctx_refines
      ((MapA.t StbMap) ★ (MemA.t StbMem), MapA.InitCond ∗∗ MapM.InitCond)
      ((MapI.t)        ★ (MemA.t StbMem), const(emp%I)).
  Proof.
    etrans; cycle 1.
    - eapply main_adequacy. eapply MapIM.sim.
      instantiate (1:= const(to_stb MapMS.Stb)).
      i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup.
    - eapply ctxr_frameR.
      rewrite/__ -{2}(hmod_addc_empty_l MapM.InitCond).
      eapply ctxr_cond_frameR.
      eapply main_adequacy. eapply MapMA.sim; eauto.
      i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup.
  Qed.

End PROOF.
End MapIA.

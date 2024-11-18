Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapASpec MapMSpec MapI MapM MapA ModSim MapIMproof MapMAproof MemA.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Events Behavior CtxRefine CtxRefineFacts.
Require Import Relation_Definitions.

(*** TODO : export these in Coqlib or Universe ***)
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

Module MapIA. Section MapIA.
  Context `{!MapAS.G Σ, !MapMS.G Σ, !memG Σ}.

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
      admit.
      (* TODO : extend the definition of hmods *)
      (* rewrite <-(hmod_addc_empty_l MapMS.InitCond). *)
      (* eapply ctxr_cond_frameR. *)
      (* eapply main_adequacy. eapply MapMA.sim; eauto. *)
      (* i. split; try refl. unfold MapMS.Stb. unseal "ccr". prove_nodup. *)
    }
    refl.
  Admitted.
End MapIA. End MapIA.
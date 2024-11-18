(* Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapASpec MapMSpec MapI MapM MapA MapAA ModSim MapIAproof MapAAAproof MemA.
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

Module MapIAA.
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
    { eapply MapIA.correct; eauto. }
    etrans; cycle 1.
    { eapply ctxr_frameR.
      rewrite <-(hmod_addc_empty_l (_ ∗∗ _)).
      eapply ctxr_cond_frameR.
      eapply main_adequacy. eapply MapAAA.sim; eauto.
    }
    eapply ctxr_cond_strengthen.
    i. iIntros "(X & Y)". iFrame.
  Qed.

End PROOF.
End MapIAA. *)

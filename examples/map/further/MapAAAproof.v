Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapAA MapA MapASpec SMod ModSim.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM SMod.
Require Import Events Behavior.
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

Require Import ISim ITactics.
Require Import HMod Mod ModSimFacts.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapAAA.
Section PROOF.
  Context `{_W: CtxWD.t}.
  Context `{_A: MapAR.t (Γ:=Γ)}.

  Import MapAS.
  
  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt => True%I).

  Variable ginvH: Sk.t -> invspec.
  Variable StbH: Sk.t -> gname -> option fspec.
  Hypothesis MapInStbH: forall sk, stb_incl MapAS.Stb (StbH sk).

  Variable ginvL: Sk.t -> invspec.
  Variable StbL: Sk.t -> gname -> option fspec.
  Hypothesis MapInStbL: forall sk, stb_incl MapAS.Stb (StbL sk).

  Local Notation MapAA := (MapAA.t ginvH StbH).
  Local Notation MapA := (MapA.t ginvL StbL).
  
  Lemma simF_init:
    HSim.sim_fun MapAA MapA Ist MapName.init.
  Proof.
    init_simF. 
    steps_l. step_r. forces_r. iFrame.
    steps_r. forces_l. steps_l. forces_l. iFrame.
    step. eauto.
  Qed.

  Lemma simF_get:
    HSim.sim_fun MapAA MapA Ist MapName.get.
  Proof.
    init_simF.
    steps_l. step_r. force_r (_,_). forces_r. iFrame.
    steps_r. forces_l. steps_l. forces_l. iFrame.
    step. eauto.
  Qed.

  Lemma simF_set:
    HSim.sim_fun MapAA MapA Ist MapName.set.
  Proof.
    init_simF.
    steps_l. step_r. force_r (_,_,_). forces_r. iFrame.
    steps_r. forces_l. steps_l. forces_l. iFrame.
    step. eauto.
  Qed.

  Lemma simF_set_by_user:
    HSim.sim_fun MapAA MapA Ist MapName.set_by_user.
  Proof.
    init_simF.
    steps_l. step_r. force_r (_,_). forces_r. iFrame.
    
    steps_r. step.
    
    steps_r. steps_l.
    iDestruct "GRT" as "((% & PT) & %)". subst. hss.    
    rewrite G0 in G2. hss.
    
    force_l (_,_,_). forces_l. iFrame. iSplit; eauto.
    
    call ""; eauto.

    steps_l. forces_r. iFrame.
    steps_r. hss. forces_l. iFrame.

    step. eauto.
  Qed.
  
  Theorem sim: HSim.t MapAA MapA MapAA.InitCond Ist.
  Proof.
    init_sim.
    - eauto.
    - apply simF_init.
    - apply simF_get.
    - apply simF_set.
    - apply simF_set_by_user.
  Qed.

End PROOF.
End MapAAA.

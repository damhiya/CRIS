Require Import Coqlib ITreelib sflib.
Require Import Events.
Require Import Behavior.

Require Import Skeleton.
Require Import PCM IPM STB.
Require Import Any.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import ISimCore.
Require Import Events Mod SMod HMod PMod.
Require Import SubPerm.
Require Import LAuto.
Require Import ISim.

From stdpp Require Import coPset gmap.

Require Export ITacticsCore.

(***
 Module-level tactics
 ***)

Ltac init_sim :=
  first [eapply mod_sim_reflR | econs; [econs|]];
  [i; s; repeat unfold_hmod; s
  |eauto
  |try prove_sub_perm
  |try prove_sub_perm
  |unfold_hmod; s; i; des; subst; ss
  |repeat unfold_hmod; ss; eauto].

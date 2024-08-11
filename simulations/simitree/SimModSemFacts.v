Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import Behavior CtxRefine.
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
Require Import Any.

Require Import Events Mod.
Require Import SimGlobal SimGlobalFacts.
Require Import Red IRed.
Require Import SimModSem.
Require Export SimModSemFacts0.

Section ADEQUACY.

  Theorem adequacy_local md_src md_tgt
          (SIM: ModR.sim md_src md_tgt)
    :
    <<CR: (ctx_refines md_tgt md_src)>>.
  Proof.
    ii. apply sim_ctx_mod with (ctx:=ctx) in SIM.
    pose (Mod.add md_src ctx) as mds.
    pose (Mod.add md_tgt ctx) as mdt.
    fold mds. fold mdt in PR.
    apply adequacy_mod with (md_src := mds) in PR; et.
  Qed.

  Corollary adequacy_local_list
            mds_src mds_tgt
            (FORALL: List.Forall2 ModR.sim mds_src mds_tgt)
    :
      <<CR: ctx_refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    r. induction FORALL; ss.

    destruct l eqn: L, l' eqn: L'.
    - apply adequacy_local; et.
    - etrans.
      + instantiate (1:= Mod.add x (Mod.add_list [])). apply refines_add.
        * apply adequacy_local. apply H.
        * apply IHFORALL.
      + s. ii.
        pose proof ModFacts.add_comm as COMM. 
        pose proof ModFacts.add_assoc_rev as ASSOC'.
        apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR.
        apply PR.
    - etrans.
      + apply adequacy_local. apply H.
      + etrans.
        * instantiate (1:= Mod.add x (Mod.add_list [])). s. ii.
          pose proof ModFacts.add_comm as COMM. 
          pose proof ModFacts.add_assoc as ASSOC.
          apply COMM. apply COMM in PR. apply ASSOC. apply ModFacts.add_empty_rev_r. apply PR.
        * apply refines_add; et. apply adequacy_local.
          econs; et. ii. rr. apply ModSemR.self_sim.
    - apply refines_add; et. apply adequacy_local. apply H.
  Qed.
          

  Theorem adequacy_local_singleton md_src md_tgt
          (SIM: ModR.sim md_src md_tgt)
    :
      <<CR: (ctx_refines_list [md_tgt] [md_src])>>
  .
  Proof.
    eapply adequacy_local_list. econs; ss.
  Qed.

End ADEQUACY.

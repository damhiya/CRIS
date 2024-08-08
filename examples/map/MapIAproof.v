Require Import Translate MapHeader MapI MapM MapA SimModSem MapIMproof MapMAproof.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Behavior.
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
Require Import Mem1.

Require Import SimModSemFacts ISim HMod Mod HModAdequacy.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.




Set Implicit Arguments.

Local Open Scope nat_scope.

Section PROOF.
  Context `{_M: MapRA.t}.
  Context `{@GRA.inG memRA Γ}.

  Theorem correct: refines2 [HMod.to_mod (HMod.add MapI.Map (HMem (fun _ => false)))] [HMod.to_mod (HMod.add (MapA.HMap (fun _ => to_stb (MemStb ++ MapStb))) (HMem (fun _ => false)))].
  Proof.
    etrans.
    {
      eapply adequacy_local2, adequacy_hmod, MapIMproof.sim. i.
      instantiate (1:= (fun _ => to_stb (MemStb ++ MapStbM))).
      ss. stb_tac. eauto.
    }
    {
      eapply adequacy_local2, adequacy_hmod, sim_ctx_hmod, MapMAproof.sim.
      { i. stb_tac. auto. }
      { i. stb_tac. auto. }
    }
  Qed.
End PROOF.

  (* 
    Reorganize the definitions of 'refines': 
    - refines src tgt (Type: mod.t)
    - refines' src tgt ctx (Type: hmod.t) := refines (to_mod (add src ctx)) (to_mod (add tgt ctx))
    - Do we still need refines2? (getting modules as a list)
      Something like Fixpoint add_list hd::tl := add hd (add_list tl) might be enough.
      ( 
        refines2 [src0; src1; ... ; ctx0; ctx1; ...] [tgt0; tgt1; ... ; ctx0; ctx1; ... ] 
    
        =>

        Let src := add_list [src0; src1; ... ]
        Let tgt := add_list [tgt0; tgt1; ... ]
        Let ctx := add_list [ctx0; ctx1; ... ]

        refines' src tgt ctx 
       
      )
  *)


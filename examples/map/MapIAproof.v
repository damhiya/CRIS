Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapASpec MapMSpec MapI MapM MapA ModSim MapIMproof MapMAproof.
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
Require Import HModAdequacy HModAlgebra CtxRefineFacts.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.




Set Implicit Arguments.

Local Open Scope nat_scope.

Section PROOF.
  Context `{_W: CtxWD.t}.
  Context `{_M: MapMR.t (Γ:=Γ)}.
  Context `{_A: MapAR.t (Γ:=Γ)}.
  Context `{@GRA.inG memRA Γ}.

  Let HMapM := MapM.t (fun _ => to_stb (MapMS.Stb ++ MemStb)).

  Let MapM_initial_cond := 
    SModSem.initial_cond MapM.Sem.

  Theorem correct:
    ctx_refines
      ((HMod.add (MapA.t MapM_initial_cond (fun _ => to_stb (MapAS.Stb ++ MemStb))) (HMem (fun _ => false))))
      ((HMod.add MapI.t (HMem (fun _ => false)))).
  Proof.
(*    
    etrans.
    {
      eapply adequacy_ctx.
      instantiate (2:= (HMod.add HMapM (HMem (λ _ : string, false)))). 
      eapply sim_ctx_hmod. eapply MapMA.sim. 
      (* stb_tac not working *)
      { 
        i. unfold to_stb, stb_incl. i.
        rewrite alist_find_app_o. des_ifs.
      }
      { 
        i. unfold to_stb, stb_incl. i.
        rewrite alist_find_app_o. des_ifs.
      }
    }
    {
      eapply adequacy_ctx. eapply MapIM.sim.
      i. unfold to_stb, stb_incl. i.
      rewrite alist_find_app_o. des_ifs.
    }
*)
  Admitted.
  
End PROOF.

Require Import Coqlib ITreelib sflib.
Require Import RingHeader CellHeader RingASpec CellASpec RingA CtrlI CellA CellI CtrlIAproof CellIAproof.
Require Import Skeleton.
Require Import PCM IPM.
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
Require Import ISim SMod HMod Mod ModSimFacts.
Require Import MainAdequacy CtxRefine.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module RingIA.
Section PROOF.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.

  Definition CellIG start len :=
    HMod.addL (List.map CellI.t (seq start len)).

  Theorem correct max_size GI (StbR StbC: Sk.t -> gname -> option fspec)
    :
    ctx_refines
      ((RingA.t max_size GI StbR) ★ (CtrlIA.CellG GI StbC 0 max_size),
       (RingA.InitCond max_size) ∗∗ (fun sk => [∗ list] i↦x ∈ seq 0 max_size, CellA.InitCond i sk))%I
      ((CtrlI.t max_size)         ★ (CellIG 0 max_size),
       const(emp%I)).
  Proof.
    etrans.
    - eapply ctxr_cond_frameR.
      eapply main_adequacy.
      apply CtrlIA.sim.
    - rewrite hmod_addc_empty_l.
      eapply ctxr_frameL.
      induction max_size; i.
      + eapply ctxr_cond_strengthen. eauto.
      + unfold CellIG, CtrlIA.CellG.
        rewrite/__ !seq_S !map_app !hmod_addL_app.
        etrans; [|etrans]; [|apply ctxr_compose_hor|]; cycle 3.
        * eapply ctxr_cond_strengthen.
          i. do 2 instantiate (1:=const(emp%I)). eauto.
        * eapply ctxr_cond_strengthen.
          i. unfold HMod.addc. rewrite/__ {1}big_sepL_app.
          iIntros "(H1 & H2)". iSplitL "H1"; eauto.
        * etrans; cycle 1. { apply IHmax_size. }
          eapply ctxr_cond_strengthen.
          i. unfold HMod.addc. eauto.
        * s. rewrite !hmod_add_empty_r.
          etrans; cycle 1.
          { eapply main_adequacy. eapply CellIA.sim. }
          eapply ctxr_cond_strengthen.
          i. rewrite/__ Nat.add_0_r seq_length. iIntros "(H &_)". eauto.
  Qed.

End PROOF.
End RingIA.

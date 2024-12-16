Require Import Coqlib ITreelib sflib.
Require Import CannonHeader CannonI CannonA CannonASpec SMod ModSim.
Require Import ImpPrelude.
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

Require Import ISim HMod PMod Events ITactics.
Require Import Mod ModSimFacts.

Require Import MainAdequacy CtxRefine.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CannonIA.
Section SIMMODSEM.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ _ st_src st_tgt =>
      ((⌜st_src = [(CannonA.v_lv, 1%Z↑)] /\ st_tgt = [(CannonI.v_lv, 1%Z↑)]⌝
        ∗
        (Ready ∨ Fired)))%I.

  Variable ginv: Sk.t -> invspec.
  Variable StbCannon: Sk.t -> gname -> option fspec.
  
  Local Notation CannonAMod := (CannonA.t ginv StbCannon).
  Local Notation CannonIMod := (CannonI.t).
  
  (*************)

  Lemma simF_fire:
    HSim.sim_fun CannonAMod CannonIMod Ist CannonName.fire.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.
    unfold Ist. iDestruct "IST" as "[[% %] [R | F]]". des; subst.

    (* already fired *)
    2:{
      iExFalso. iCombine "B F" as "Boom".
      iApply (FiredBall with "Boom").
    }

    steps_r. force_r. iSplitR.
    { iPureIntro. rewrite Any.upcast_downcast. et. }
    steps_r. unfold CannonI.div. des_ifs. force_r. iSplitR; et.
    step. steps_l. force_l. force_l. instantiate (1:=(1%Z)↑). iSplitR; et.
    steps_r. ss.
  Qed.

  Theorem sim:
    HSim.t CannonAMod CannonIMod CannonA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "IC". unfold Ist, CannonA.InitCond. iSplitR; et.
    - eapply simF_fire.
  Qed.

End SIMMODSEM.

Section PROOF.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.

  Theorem correct gi StbCannon
    :
    ctx_refines
      (CannonA.t gi StbCannon, CannonA.InitCond)
      (CannonI.t, const(emp%I)).
  Proof.
    eapply main_adequacy.
    apply sim.
  Qed.
End PROOF.
End CannonIA.
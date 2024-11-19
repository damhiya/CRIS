(* Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM IFacts.
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
Require Import SMod2HMod Mod ModSimFacts.

Require Import CellioHeader CellioA MainHeader MainA MainI FooASpec.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MainIM.
Section SIMMODSEM.
  Context `{_M: CellioRA.t}.
  
  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ _ st_src st_tgt => emp%I.

  Variable ginv: Sk.t -> invspec.
  Variable Stb: Sk.t -> gname -> option fspec.
  Hypothesis FooInStbMap: forall sk, stb_incl FooAS.Stb (Stb sk).  

  Local Notation CellioA := (CellioA.t ginv Stb).
  Local Notation MainA := (MainA.t ginv Stb).
  Local Notation IstFull := (IstProd (IstSB MainA Ist) IstEq).

  (**********)

  Lemma simF_main:
    HSim.sim_fun (MainA ★ CellioA) (MainI.t ★ CellioA) IstFull MainName.main.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst.

    inline_r.
    step_r. forces_r. iSplitL ""; eauto.
    forces_r. steps_r. forces_r. iSplitL "ASM'"; eauto.

    steps_r. step.

    steps_l. steps_r. iDestruct "GRT'" as "%". subst. hss.
    steps_r. forces_l.
    iSplitL ""; eauto.

    call "IST"; eauto.

    steps_l. iDestruct "ASM" as "%". subst. hss.
    steps_r. hss. steps_r. inline_r.
    step_r. forces_r. iSplitL ""; eauto.
    forces_r. steps_r. forces_r.
    iSplitL "GRT"; eauto.

    steps_r. iDestruct "GRT'" as "%". subst. hss.
    steps_r. step.

    steps_l. forces_l.
    iSplitL ""; eauto.

    steps_r. step. iFrame. eauto.

  Unshelve. all:eauto.
  Qed.

  Theorem sim:
    HSim.t (MainA ★ CellioA) (MainI.t ★ CellioA) (const emp%I) IstFull.
  Proof.
    init_sim.
    - iIntros "_". repeat iExists []. iSplit; eauto.
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    - eapply simF_main; eauto.
  Qed.

End SIMMODSEM.
End MainIM. *)

Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod PMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import RingHeader.
Require Import CellHeader.
Require Import ITactics.

Set Implicit Arguments.

Module CellI.
Section CELL_I.
  Context `{Σ: GRA.t}.  

  Variable idx : nat.

  Definition scopes := [CellName.mn idx].
  Definition v_cv := (CellName.mn idx) ↯ "cv".

  Definition get: unit -> itree pmodE Z :=
    fun _ =>
      cv <- cgetU v_cv;;
      Ret cv
  .

  Definition set: Z -> itree pmodE unit :=
    fun x =>
      cput v_cv x
  .

  Definition fnsems :=
    [(CellName.get idx, (scopes, cfunU get));
     (CellName.set idx, (scopes, cfunU set))].

  Program Definition Sem: PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_cv,tt↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  
  Definition Mod: PMod.t := {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := CellSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End CELL_I.
End CellI.

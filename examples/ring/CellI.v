Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
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

  Definition get: unit -> itree hmodE Z :=
    fun _ =>
      cv <- trigger (SGet (CellName.mk idx "cv")) ;; cv <- cv↓?;;
      Ret cv
  .

  Definition set: Z -> itree hmodE unit :=
    fun x =>
      trigger (SPut (CellName.mk idx "cv") x↑);;; Ret tt.

  Definition fnsems :=
    [(CellName.get idx, ([CellName.mk idx "cv"], cfunU get));
     (CellName.set idx, ([CellName.mk idx "cv"], cfunU set))].

  Program Definition Sem: HModSem.t := {|
    HModSem.fnsems := fnsems;
    HModSem.initial_st := [(CellName.mk idx "cv",tt↑)];
    HModSem.initial_cond := emp;
  |}
  .
  Next Obligation. prove_scope. Qed.
  
  Definition Mod: HMod.t := {|
    HMod.get_modsem := fun _ => Sem;
    HMod.sk := CellSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" Mod.

End CELL_I.
End CellI.

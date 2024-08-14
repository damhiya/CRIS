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

Set Implicit Arguments.

Module CellI.
Section CELL_I.
  Context `{Σ: GRA.t}.  

  Variable idx : nat.

  Definition init: unit -> itree hmodE unit :=
    fun _ =>
      trigger (sPut (0: Z)↑)
  .

  Definition get: unit -> itree hmodE Z :=
    fun _ =>
      st <- trigger sGet;; x <- st↓?;;
      Ret x
  .

  Definition set: Z -> itree hmodE unit :=
    fun x =>
      trigger (sPut x↑).

  Definition fnsems :=
    [(CellName.init idx, cfunU init);
     (CellName.get idx, cfunU get);
     (CellName.set idx, cfunU set)].

  Definition Sem: HModSem.t := {|
    HModSem.fnsems := fnsems;
    HModSem.initial_st := tt↑;
    HModSem.initial_cond := emp;
  |}
  .

  Definition Mod: HMod.t := {|
    HMod.get_modsem := fun _ => Sem;
    HMod.sk := CellSK.t;
  |}
  .

  Definition _t := Mod.
  Definition t := _t.

  Lemma unfold: t = _t.
  Proof. eauto. Qed.

  Global Opaque t.

End CELL_I.
End CellI.

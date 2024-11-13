Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod PMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import RingHeader.
Require Import MainHeader CellioHeader FooHeader.
Require Import ITactics.

Set Implicit Arguments.

Module MainI.
Section MainI.
  Context `{Σ: GRA.t}.  

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree pmodE Any.t :=
    fun _ =>
      ccallU (Y:=unit) CellioName.set tt;;;
      ccallU (Y:=unit) FooName.foo tt;;;
      x <- ccallU (Y:=Z) CellioName.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑
  .
  
  Definition fnsems :=
    [(MainName.main, (scopes, main))].

  Program Definition Sem: PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition Mod: PMod.t := {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := MainSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End MainI.
End MainI.

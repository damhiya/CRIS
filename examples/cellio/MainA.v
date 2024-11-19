(* Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import CellioA CellioHeader MainHeader FooHeader.

Set Implicit Arguments.

Module MainA.
Section MainA.
  Context `{_W: CellioRA.t}.  

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree hmodE Any.t :=
    fun _ =>
      trigger (Assume (CellioR.cell 0));;;
      i <- trigger (@IO _ Z "Input" tt);;
      ccallU (Y:=unit) FooName.foo tt;;;
      trigger (@IO _ unit "Print" i);;;
      Ret tt↑
  .
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(MainName.main, (scopes, mk_specbody fspec_trivial main))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := CellioSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => emp%I.

  Variable GI: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GI GlobalStb Mod).

End MainA.
End MainA. *)

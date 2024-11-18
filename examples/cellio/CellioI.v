(* Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod PMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import RingHeader.
Require Import CellioHeader.
Require Import ITactics.

Set Implicit Arguments.

Module CellioI.
Section CellioI.
  Context `{Σ: GRA.t}.  

  Definition scopes := [CellioName.mn].
  Definition v_cv := (CellioName.mn) ↯ "cv".

  Definition set: Any.t -> itree pmodE Any.t :=
    fun _ =>
      i <- trigger (@IO _ Z "Input" tt);;
      cput v_cv i;;;
      Ret tt↑
  .
  
  Definition get: Any.t -> itree pmodE Any.t :=
    fun _ =>
      i <- cgetU v_cv;;
      Ret (i:Z)↑
  .

  Definition fnsems :=
    [(CellioName.set, (scopes, set));
     (CellioName.get, (scopes, get))].

  Program Definition Sem: PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_cv, (0%Z)↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition Mod: PMod.t := {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := CellioSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End CellioI.
End CellioI. *)

Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM STB sProp sWorld.
Require Import IPM ITactics.
Require Import RingHeader CellHeader CellASpec.

Set Implicit Arguments.

Module CellA. Section CellA.
  Context `{!Inv.t Σ Γ α β τ, !CellAS.G Γ}.
  Notation iProp := (iProp Σ).

  Variable idx : nat.

  Definition scopes := [CellName.mn idx].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellName.get idx, ([], mk_specbody (CellAS.get_spec idx) fbody_trivial));
     (CellName.set idx, ([], mk_specbody (CellAS.set_spec idx) fbody_trivial))].
 
  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := CellSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    λ _, (∃ v, CellAS.cell idx v ∗ CellAS.auth idx v)%I.

  Variable ginv : Sk.t -> invspec.
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End CellA. End CellA.

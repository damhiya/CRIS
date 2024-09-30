Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod PMod.
Require Import Skeleton.
Require Import MapHeader.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import CannonHeader.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Module CannonI.
Section I.
  Local Open Scope string_scope.
  Context `{_W: CtxWD.t}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv". (* local variable *)

  Definition div (n m: Z): option Z :=
    if Z_zerop m then None else Some (Z.div n m).

  Definition fire: list val -> itree pmodE Z :=
    fun _ =>
      powder <- cgetU v_lv;;
      r <- (div 1 powder)?;;
      _ <- trigger (@IO _ void "print" [r]↑);;
      cput v_lv (powder - 1)%Z;;;
      Ret r
  .

  Definition fnsems :=
    [(CannonName.fire, (scopes, cfunU fire))].
  
  Program Definition Sem: PModSem.t :=
  {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_lv, 1%Z↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: PMod.t := 
  {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := CannonSK.t;
  |}.

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End I.

End CannonI.
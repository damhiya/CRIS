Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import CannonHeader CannonASpec.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.

Module CannonA.
Section A.
  Context `{_W: CtxWD.t}.
  Context `{_A: CannonAR.t (Γ:=Γ)}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv".

  Definition fire: list val -> itree smodE Z :=
    fun _ =>
      let r := 1%Z in
      _ <- trigger (@IO _ void "print" [r]↑);;
      Ret r
  .

  Definition fnsems :=
    [(CannonName.fire, (scopes, mk_specbody CannonAS.fire_spec (cfunU fire)))].

  Program Definition Sem: SModSem.t :=
  {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_lv, 1%Z↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: SMod.t :=
  {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := CannonSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp :=
    fun _ => (OwnM CannonAS.Ready)%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End A.
End CannonA.
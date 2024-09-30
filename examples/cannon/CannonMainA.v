Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import CannonHeader CannonMainASpec CannonMainI CannonASpec CannonHeader.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.

Module MainA.
Section A.
  Context `{_W: CtxWD.t}.
  Context `{_A: MainAR.t (Γ:=Γ)}.

  Variable num_fire: nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n: nat): itree smodE unit :=
  match n with
  | 0 =>
    Ret tt
  | S n' =>
    `r: Z <- ccallU CannonName.fire ([]: list val);;
    _ <- trigger (@IO _ void "print" [r]↑);;
    main_repeat n'
  end.

  Definition main: list val -> itree smodE unit :=
    fun _ =>
      main_repeat num_fire
  .

  Definition fnsems :=
    [(MainName.main, (scopes, mk_specbody CannonMainAS.main_spec (cfunU main)))].

  Program Definition Sem: SModSem.t :=
  {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: SMod.t :=
  {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := MainSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp :=
    fun _ => (OwnM CannonAS.Ready)%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End A.
End MainA.
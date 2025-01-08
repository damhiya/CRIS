Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.

Set Implicit Arguments.

Module MainI.
Section I.
  Local Open Scope string_scope.
  Context `{Σ: GRA}.

  Variable num_fire: nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n: nat): itree pmodE unit :=
    match n with
    | 0 =>
      Ret tt
    | S n' =>
      'r: Z <- ccallU CannonName.fire ([]: list val);;
      trigger (@IO _ void "print" [r]↑);;;
      main_repeat n'
    end.

  Definition main: list val -> itree pmodE unit :=
    fun _ =>
      main_repeat num_fire
  .

  Definition fnsems :=
    [(MainName.main, (scopes, cfunU main))].
  
  Program Definition Sem: PModSem.t :=
  {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: PMod.t := 
  {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := MainSK.t;
  |}.

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End I.

End MainI.
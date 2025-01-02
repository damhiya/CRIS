Require Import CRIS.

Require Import MainHeader CellioHeader FooHeader.

Set Implicit Arguments.

Module MainI.
Section MainI.
  Context `{Σ: GRA.t}.

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree pmodE Any.t :=
    λ _,
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
    PMod.modsem := λ _, Sem;
    PMod.sk := MainSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End MainI. End MainI.

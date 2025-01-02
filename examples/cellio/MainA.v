Require Import CRIS.

Require Import CellioA CellioHeader MainHeader FooHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!Inv.t Σ Γ α β τ, !G Γ, !CellioA.G Γ}.
  Notation iProp := (iProp Σ).

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      trigger (Assume (CellioA.cell 0));;;
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
    λ _, emp%I.

  Variable GI: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GI GlobalStb Mod).

End MainA. End MainA.

Require Import CRIS.
Require Import CellioA CellioHeader MainHeader FooHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      trigger (Assume (cell 0));;;
      'i: Z <- trigger (IO "Input" tt);;
      '_: unit <- ccallU FooName.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
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

  Definition InitCond : Sk.t -> iProp Σ :=
    λ _, emp%I.

  Variable GI: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> string -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GI GlobalStb Mod).

End MainA. End MainA.

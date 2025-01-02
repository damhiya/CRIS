Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainASpec CannonMainI CannonASpec CannonHeader.

Set Implicit Arguments.

Module MainA.
Section A.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Variable num_fire: nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n: nat): itree hmodE unit :=
  match n with
  | 0 =>
    Ret tt
  | S n' =>
    'r: Z <- ccallU CannonName.fire ([]: list val);;
    _ <- trigger (@IO _ void "print" [r]↑);;
    main_repeat n'
  end.

  Definition main: list val -> itree hmodE unit :=
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
    fun _ => Ready%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End A.
End MainA.
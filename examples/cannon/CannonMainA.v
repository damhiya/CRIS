Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainASpec CannonMainI CannonASpec CannonHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree hmodE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonName.fire ([] : list val);;
      _ <- trigger (@IO _ void "print" [r]↑);;
      main_repeat n'
    end.

  Definition main : list val → itree hmodE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems :=
    [(MainName.main, (scopes, mk_specbody MainAS.main_spec (cfunU main)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := MainSK.t;
  |}.

  Definition init_cond : Sk.t → iProp Σ := λ _, True%I.

  Variable ginv : Sk.t → invspec.
  Variable GlobalStb : Sk.t → gname → option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).
End MainA. End MainA.
Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonASpec.

Set Implicit Arguments.

Module CannonA.
Section A.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv".

  Definition fire: list val -> itree hmodE Z :=
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
    fun _ => Ready%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End A.
End CannonA.
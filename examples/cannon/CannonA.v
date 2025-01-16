Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonASpec.

Set Implicit Arguments.

Module CannonA. Section CannonA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv".

  Definition fire : list val → itree hmodE Z :=
    λ _,
      let r := 1%Z in
      _ <- trigger (@IO _ void "print" [r]↑);;
      Ret r.

  Definition fnsems :=
    [(CannonName.fire, (scopes, mk_specbody CannonAS.fire_spec (cfunU fire)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_lv, 1%Z↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := CannonSK.t;
  |}.

  Definition init_cond : Sk.t → iProp Σ :=
    λ _, Ready.

  Variable ginv : Sk.t → invspec.
  Variable GlobalStb : Sk.t → string → option fspec.
  Definition t := Seal.sealing CRIS (SMod.to_hmod ginv GlobalStb Mod).
End CannonA. End CannonA.
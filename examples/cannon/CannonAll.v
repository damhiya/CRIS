Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonIAproof CannonMainIAproof.
Require Import CannonA CannonASpec CannonMainA CannonMainASpec .
Require Import Cancellation.

Set Implicit Arguments.

Module CannonAll.
Section C.
  Variable num_fire: nat.
  Definition Γ : HRA := ##[invΓ; CannonAS.GΓ].
  Local Existing Instance Γ.

  Definition τ : Typ.t :=
    fun _ => ST.t.
  Local Existing Instance τ.

  Definition α : SRFCons.t :=
    fun n => 
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.
  Local Existing Instance α.

  Definition Σ : GRA := ##[invΣ; Γ].
  Local Existing Instance  Σ.

  Local Instance subG_GΓ : subG Γ Σ.
  Proof. Admitted. 

  Local Instance invGS_GΓ: invGS Σ Γ.
  Proof. Admitted.

  Definition β : SRFIntp.t :=
    fun n => 
      match n with
      | 0 => SL.t
      | _ => (@inv_interp α Γ Σ subG_GΓ _) 
      end.

  Local Instance sinvGS_: sinvGS Σ Γ α β τ.
  Proof. Admitted.

  Local Instance asdf: CannonAS.GS Γ.
  Proof. Admitted.

  Definition Mod := (@CannonA.Mod Σ Γ α β τ sinvGS_ _) ☆ (@MainA.Mod Σ Γ α β τ sinvGS_ _ num_fire).


End C.
End CannonAll.
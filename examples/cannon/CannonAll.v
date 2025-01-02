Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonIAproof CannonMainIAproof.
Require Import CannonA CannonMainA.
Require Import Cancellation.

Set Implicit Arguments.

Module CannonAll.
Section C.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Check CannonA.t.

  Check (cancellation).



End C.
End CannonAll.
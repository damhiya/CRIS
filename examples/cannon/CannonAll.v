Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonIAproof CannonMainIAproof.
Require Import CannonA CannonASpec CannonMainA CannonMainASpec .
(* Require Import Cancellation. *)

Set Implicit Arguments.

Module CannonAll. Section CannonAll.
  Variable num_fire: nat.
  Import inv_instances.
  Instance Γ : HRA := ##[invΓ; CannonAΓ].
  Instance Σ : GRA := ##[invΣ; Γ].
  
  (* Set Typeclasses Debug Verbosity 2. *)
  Set Typeclasses Depth 10.
  (* Instance test : invG Σ Γ. eauto. apply _. *)
  Definition Mod := (CannonA.Mod) ☆ (MainA.Mod num_fire).
End CannonAll. End CannonAll.
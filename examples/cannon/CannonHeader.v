Require Import CRIS.
Require Import ImpPrelude.

Module CannonName.

Definition fire := "Cannon.fire".

End CannonName.

Module MainName.
  Definition main := "CRIS_init".
  (* Definition main := "Main.main". *)
End MainName.

(* Module CannonGEnv.
  Definition t : GEnv.t := [(CannonName.fire, Gfun↑)].
End CannonGEnv.

Module MainGEnv.
  Definition t : GEnv.t := [(MainName.main, Gfun↑)].
End MainGEnv. *)
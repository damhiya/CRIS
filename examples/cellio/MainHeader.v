(* Require Import Coqlib ITreelib sflib HexString.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module MainName.

  Definition mn := "Main".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition main := fn "main".

End MainName.

Module MainSK.
  Definition t : Sk.t := [].
End MainSK. *)

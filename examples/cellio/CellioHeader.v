(* Require Import Coqlib ITreelib sflib HexString.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module CellioName.

  Definition mn := "Cellio".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition set := fn "set".
  Definition get := fn "get".

End CellioName.

Module CellioSK.
  Definition t : Sk.t := [].
End CellioSK. *)

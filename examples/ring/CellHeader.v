Require Import Coqlib ITreelib sflib HexString.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module CellName.

  Definition mk (idx: nat) (method: string) :=
    "Cell" +:+ HexString.of_nat idx +:+ "." +:+ method.
  
  Definition get idx := mk idx "get".
  Definition set idx := mk idx "set".

End CellName.

Module CellSK.
  Definition t : Sk.t := [].
End CellSK.

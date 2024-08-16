Require Import Coqlib ITreelib sflib.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module CellName.
  
Definition init (idx: nat) := "Cell.init:" +:+ IModL.nat_to_string idx.
Definition get (idx: nat) := "Cell.get:" +:+ IModL.nat_to_string idx.
Definition set (idx: nat) := "Cell.set:" +:+ IModL.nat_to_string idx.

End CellName.

Module CellSK.
  Definition t : Sk.t := [].
End CellSK.

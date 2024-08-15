Require Import Coqlib ITreelib sflib.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module CellName.
  
Definition init (idx: nat) := "Cell" +:+ IModL.nat_to_string idx +:+ ".init:".
Definition get  (idx: nat) := "Cell" +:+ IModL.nat_to_string idx +:+ ".get:".
Definition set  (idx: nat) := "Cell" +:+ IModL.nat_to_string idx +:+ ".set:".

End CellName.

Module CellSK.
  Definition t : Sk.t := [].
End CellSK.

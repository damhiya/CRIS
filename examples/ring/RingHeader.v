Require Import Coqlib ITreelib sflib.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module RingName.
  
Definition init := "Ring.init".
Definition get_size := "Ring.get_size".
Definition enqueue := "Ring.enqueue".
Definition dequeue := "Ring.dequeue".

End RingName.

Module RingSK.
  Definition t : Sk.t := [].
End RingSK.

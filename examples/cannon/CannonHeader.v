Require Import Coqlib ITreelib sflib.
Require Import Events Any IPM ImpPrelude Skeleton.

Module CannonName.

Definition fire := "Cannon.fire".

End CannonName.

Module MainName.
  Definition main := "Main.main".
End MainName.

Module CannonSK.
  Definition t : Sk.t := [(CannonName.fire, Gfun↑)].
End CannonSK.

Module MainSK.
  Definition t : Sk.t := [(MainName.main, Gfun↑)].
End MainSK.
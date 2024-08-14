Require Import Coqlib ITreelib sflib.
Require Import Events Any IPM ImpPrelude.

Module MapName.
  
Definition init := "Map.init".
Definition get := "Map.get".
Definition set := "Map.set".
Definition set_by_user := "Map.set_by_user".

End MapName.

Module MapSK.
  Definition t :=
    [(MapName.init, Gfun↑);
     (MapName.get, Gfun↑);
     (MapName.set, Gfun↑);
     (MapName.set_by_user, Gfun↑)].
End MapSK.

Notation pget := (p0 <- trigger sGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
Notation pput p0 := (trigger (sPut p0↑)) (only parsing).

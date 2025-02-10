Require Import CRIS.
Require Export ImpPrelude.

Module MemName.
  Definition alloc := "MemAtom.alloc".
  Definition free  := "MemAtom.free".
  Definition load  := "MemAtom.load".
  Definition store := "MemAtom.store".
  Definition cmp   := "MemAtom.cmp".
  Definition cas := "MemAtom.cas".
End MemName.

Module MemGEnv.
  Definition t: GEnv.t :=
    [(MemName.alloc, Gfun↑);
     (MemName.free,  Gfun↑);
     (MemName.load, Gfun↑);
     (MemName.store, Gfun↑);
     (MemName.cmp, Gfun↑);
     (MemName.cas, Gfun↑)].
End MemGEnv.
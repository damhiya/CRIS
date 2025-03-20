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

Definition faa {E : Type → Type} `{callE -< E, coreE -< E} : list val → itree E val :=
  λ l,
  'v_raw : val <- ccallU MemName.load l;;
  'v : Z <- (pargs [Tint] [v_raw])?;;
  'r : val <- ccallU MemName.store (l ++ [Vint (v + 1)%Z]);;
  Ret r.
Require Import CRIS.

Require Export ImpPrelude.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.

Module APCHdr.  
  Definition apc := "APC.apc".

  Definition exports : gset string :=
    {[ apc ]}.
End APCHdr.

Require Import CRIS.

From Ordinal Require Export Ordinal Arithmetic Inaccessible.

Module APC.
  Definition apc := "APC.apc".
  Definition apc_t := cftyp Ord.t ().

  Definition exports : gset string :=
    {[ apc ]}.
End APC.

Require Import CRIS.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.

Module APC.
  Definition apc := fnsig "APC.apc" (fntyp Ord.t ()).
  Definition exports : gset string := {[ fn_name apc ]}.
End APC.

Require Import CRIS.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.

Module APC.
  Definition apc := mk_fnsig "APC.apc" Ord.t ().
  Definition exports : gset string := {[ fn_name apc ]}.
End APC.

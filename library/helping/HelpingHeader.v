From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader.

Module Helping. Section Helping.
  Context `{Σ : GRA}.
  Context (mn : string).

  Definition run  := "★" +:+ mn.
  Definition help := "☆" +:+ mn.

  Definition exports : gset string := {[run; help]}.
End Helping. End Helping.

Variant help_state : Type :=
| Pend (N : option namespace) (arg : SAny.t)
| InProgress
| Done (ret : SAny.t).

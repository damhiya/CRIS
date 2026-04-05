Require Import CRIS.
Require Import SchHeader.

Module Helping. Section Helping.
  Context `{Σ : GRA}.
  Context (mn : string).

  Definition run  := "★" +:+ mn.
  Definition help := "☆" +:+ mn.
  Definition yield := "∘" +:+ mn.

  Definition exports : gset string := {[run; help]}.
End Helping. End Helping.

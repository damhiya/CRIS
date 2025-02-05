(** * Module index typeclass, for composing modules and their simulation proofs *)
From stdpp Require Import numbers.

Class mod_level : Type := mod_level_mk {
  mod_level_elem : positive
}.
Global Coercion mod_level_elem : mod_level >-> positive.
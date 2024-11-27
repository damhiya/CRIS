(** * Module index typeclass, for composing modules and their simulation proofs *)
From stdpp Require Import numbers.

Class mod_index : Type := mod_index_mk {
  mod_index_elem : positive
}.
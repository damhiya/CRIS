(** * Main module *)

(** The main definitions to construct programs with are
    gathered here.

    Theorems can be accessed via [ITree.ITreeFacts],
    and some standard effects via [ITree.Events].
 *)

From ITreeS Require Export
  CategoryOps
  Basics
  Sum
  ITreeDefinition
  Subevent
  Eqit
  EqAxiom
  EqitFacts
  Interp
  State
  TranslateFacts
  InterpFacts
  StateFacts
  .

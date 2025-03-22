Require Export Program Permutation Orders String HexString ZArith.

Require Export Axioms Any AList Red IRed SubPerm.
Require Export sflib Coqlib ITreelib.
Require Export SAT own invariants sProp syn_invariants.
Require Export Events Behavior.

(* TODO: Move *)
Section CONTEXT.
  Variant contextuality : Type := 
  | open 
  | closed.
  
End CONTEXT.
Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader.
Require Import CellHeader.

Set Implicit Arguments.

Module CellI. Section CellI.
  Context `{Σ : GRA}.

  Variable idx : nat.

  Definition scopes := [CellName.mn idx].
  Definition v_cv := (CellName.mn idx) ↯ "cv".

  Definition get : unit -> itree pmodE Z :=
    λ _,
      cv <- cgetU v_cv;;
      Ret cv.

  Definition set : Z -> itree pmodE unit :=
    λ x,
      cput v_cv x;;;
      Ret ().

  Definition fnsems :=
    [(CellName.get idx, (scopes, cfunU get));
     (CellName.set idx, (scopes, cfunU set))].

  Program Definition Sem : PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_cv,tt↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition Mod : PMod.t := {|
    PMod.modsem := λ _, Sem;
    PMod.sk := CellSK.t;
  |}
  .

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).

End CellI. End CellI.

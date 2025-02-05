Require Import CRIS.
Require Import CellioA CellioHeader MainHeader FooHeader InputHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition scopes := [MainName.mn].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      trigger (Assume (cell 0));;;
      (* 'i: Z <- trigger (IO "Input" tt);; *)
      'i: Z <- ccallU InputName.input tt;;
      '_: unit <- ccallU FooName.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑
  .
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(MainName.main, (scopes, mk_specbody fspec_trivial main))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition InitRes : Σ := ε.

  (* Definition Spc : alist string fspec :=
    Seal.sealing CRIS [(MainName.main, fspec_trivial)].

  Lemma Spc_nodup: List.NoDup (List.map fst Spc).
  Proof. unfold Spc. unseal CRIS. prove_nodup. Qed. *)

  Definition t ginv Spc := Seal.sealing CRIS (SMod.to_hmod ginv Spc Mod).

End MainA. End MainA.

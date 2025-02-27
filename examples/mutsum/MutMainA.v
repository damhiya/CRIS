Require Import CRIS.
Require Import MutHeader MutMainHeader.

Set Implicit Arguments.

Module MutMainA. Section MutMainA.
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition scopes := ["MutMain"].

  Definition main_spec: fspec :=
    fspec_simple (fun (_: unit) =>
      ((λ varg, (⌜varg = tt↑⌝)%I),
       (λ vret, (⌜vret = (Vint 55)↑⌝)%I))).

  Definition Spc: alist string fspec :=
    Seal.sealing CRIS [(MutMainName.main, main_spec)].

  Lemma Spc_nodup: List.NoDup (List.map fst Spc).
  Proof. unfold Spc. unseal CRIS. prove_nodup. Qed.

  Definition fnsems :=
    [(MutMainName.main, (scopes, mk_specbody main_spec fbody_trivial))].

  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp := emp%I.

  Definition t Spc := Seal.sealing CRIS (SMod.to_hmod emp Spc Mod).
End MutMainA. End MutMainA.

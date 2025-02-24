Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutGA. Section MutGA.
  Import MutAUX.
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition scopes := ["MutG"].

  Definition g_spec: fspec :=
    fspec_simple (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpcG: alist string fspec :=
    Seal.sealing CRIS [(MutName.mutg, g_spec)].

  Lemma SpcG_nodup: List.NoDup (List.map fst SpcG).
  Proof. unfold SpcG. unseal CRIS. prove_nodup. Qed.

  Definition fnsems :=
    [(MutName.mutg, (scopes, mk_specbody g_spec fbody_trivial))].

  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp := emp%I.

  Definition t Stb := Seal.sealing CRIS (SMod.to_hmod ginv_emp Stb Mod).
End MutGA. End MutGA.

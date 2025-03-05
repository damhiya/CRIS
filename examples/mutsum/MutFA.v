Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutFA. Section MutFA.
  Import MutAUX.
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition scopes := ["MutF"].

  Definition f_spec: fspec :=
    fspec_apc (λ n: nat, n)%ord
      (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpcF: alist string fspec :=
    Seal.sealing CRIS [(MutName.mutf, f_spec)].

  Lemma SpcF_nodup: List.NoDup (List.map fst SpcF).
  Proof. unfold SpcF. unseal CRIS. prove_nodup. Qed.

  Definition fnsems :=
    [(MutName.mutf, (scopes, mk_specbody f_spec pure_body))].

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
End MutFA. End MutFA.

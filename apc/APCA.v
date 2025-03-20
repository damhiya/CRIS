Require Import CRIS.

Require Import APCHeader APC.

Set Implicit Arguments.

Module APCA. Section APCA.
  Import APC.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition scopes := ["APC"].

  Definition apc_body SpcPure : Ord.t → itree hmodE () :=
    λ dep_ord, APC dep_ord SpcPure.

  Definition apc_spec : fspec :=
    mk_fspec (λ (o: Ord.t) varg arg, ⌜varg = o↑ ∧ arg = varg⌝)%I
             (λ _ _ _, True)%I.

  Definition Spc : alist string fspec :=
    Seal.sealing CRIS
      [(APCHdr.apc, apc_spec)].
  
  Lemma Spc_nodup : List.NoDup (List.map fst Spc).
  Proof. unfold Spc. unseal CRIS. prove_nodup. Qed.

  Definition fnsems SpcPure :=
    [(APCHdr.apc, (scopes, mk_specbody apc_spec (cfunN (apc_body SpcPure))))].

  Program Definition Mod SpcPure : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems SpcPure;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition t u SpcPure Spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) Spc (Mod SpcPure)).
End APCA. End APCA.

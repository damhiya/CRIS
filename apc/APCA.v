Require Import CRIS.

Require Import APCHeader APC.

Set Implicit Arguments.

Module APCA. Section APCA.
  Import APC.
  Context `{_crisG: !crisG  Γ Σ α β τ _S _I _T}.

  Definition scopes := ["APC"].

  Definition apc_body SpPure : Ord.t → itree hmodE () :=
    λ dep_ord, APC dep_ord SpPure.

  Definition apc_spec : fspec :=
    mk_fspec (λ (o: Ord.t) varg arg, ⌜varg = o↑ ∧ arg = varg⌝)%I
             (λ _ _ _, True)%I.

  Definition Sp : alist string fspec :=
    Seal.sealing CRIS
      [(APCHdr.apc, apc_spec)].
  
  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof using. unfold Sp. unseal CRIS. prove_nodup. Qed.

  Definition fnsems SpPure :=
    [(APCHdr.apc, (wmask_all, scopes, mk_specbody apc_spec (cfunN (apc_body SpPure))))].

  Program Definition Mod SpPure : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems SpPure;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition t SpPure Sp := Seal.sealing CRIS (SMod.to_hmod Sp (Mod SpPure)).
End APCA. End APCA.

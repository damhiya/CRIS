Require Import CRIS.

Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module APCC. Section APCC.
  Context `{!sinvG Γ Σ α β τ}.

  Definition scopes := ["APC"].

  Definition Sp : alist string fspec :=
    Seal.sealing CRIS
      [(APCHdr.apc, APCA.apc_spec)].
  
  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof using. unfold Sp. unseal CRIS. prove_nodup. Qed.

  Definition fnsems :=
    [(APCHdr.apc, (scopes, mk_specbody APCA.apc_spec fbody_trivial))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).
End APCC. End APCC.

Require Import CRIS.

Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module APCC. Section APCC.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition scopes := ["APC"].

  Definition Spc : alist string fspec :=
    Seal.sealing CRIS
      [(APCHdr.apc, APCA.apc_spec)].
  
  Lemma Spc_nodup : List.NoDup (List.map fst Spc).
  Proof using. unfold Spc. unseal CRIS. prove_nodup. Qed.

  Definition fnsems :=
    [(APCHdr.apc, (scopes, mk_specbody APCA.apc_spec fbody_trivial))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u Spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) Spc Mod).
End APCC. End APCC.

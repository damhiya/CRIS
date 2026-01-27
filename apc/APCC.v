Require Import CRIS.

Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module APCC. Section APCC.
  Context `{Σ: GRA}.

  Definition scopes := ["APC"].

  Definition Sp : spl_type :=
    Seal.sealing CRIS
      [(Some APCHdr.apc, Some (APCA.apc_spec: fspec_rel))].

  
  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof using. unfold Sp. unseal CRIS. prove_nodup. Qed.

  Definition fnsems : fnsems_type :=
    [(Some APCHdr.apc, (true, wmask_all, scopes, (Some (APCA.apc_spec: fspec_rel), fbody_trivial)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_mod Sp smod).
End APCC. End APCC.

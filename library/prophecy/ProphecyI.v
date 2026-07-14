From CRIS.common Require Import CRIS.
From CRIS.prophecy Require Import ProphecyHeader.

Module ProphecyI. Section ProphecyI.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).

  Definition scopes : list string := [].

  Definition new : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition resolve : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition close : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.

  Definition mask : emask := msk_real (msk_scp scopes msk_true).

  Definition fnsems : fnsemmap :=
    {[fid (Prophecy.new mn) # (mask, (None, new));
      fid (Prophecy.resolve mn) # (mask, (None, new));
      fid (Prophecy.close mn) # (mask, (None, close))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.

  Lemma real: Mod.real_mod t.
  Proof. real_mod_solver. Qed.

End ProphecyI. End ProphecyI.

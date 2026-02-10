Require Import CRIS.
Require Import ProphecyHeader.

Module ProphecyI. Section ProphecyI.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.
  Context (mn : string).

  Definition scopes : list string := [].

  Definition new : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition resolve : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition close : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[Some (ProphecyName.new mn) := Some (msk_real (msk_scp scopes msk_true), (None, new));
      Some (ProphecyName.resolve mn) := Some (msk_real (msk_scp scopes msk_true), (None, new));
      Some (ProphecyName.close mn) := Some (msk_real (msk_scp scopes msk_true), (None, close))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End ProphecyI. End ProphecyI.
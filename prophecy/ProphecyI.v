Require Import CRIS.
Require Import ProphecyHeader.

Module ProphecyI. Section ProphecyI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : gmultiset string := ∅.

  Definition new : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition resolve : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition close : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.

  Definition fnsems : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some ProphecyName.new := Some (msk_real (msk_scp scopes msk_true), (None, new));
      Some ProphecyName.resolve := Some (msk_real (msk_scp scopes msk_true), (None, new));
      Some ProphecyName.close := Some (msk_real (msk_scp scopes msk_true), (None, close))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try done.
  Next Obligation. rewrite ?omap_insert /= omap_empty. mod_tac scope_solver. Qed.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End ProphecyI. End ProphecyI.

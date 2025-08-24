Require Import CRIS.
Require Import ProphecyHeader.

Module ProphecyI.
  Section ProphecyI.

  Context `{Σ : GRA}.

  Definition scopes := ["Prophecy"].

  Definition new : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition resolve : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  Definition close : Any.t → itree crisE Any.t :=
    λ _, Ret tt↑.
  
  Definition fnsems : fnsems_type :=
    [(Some ProphecyName.new, (false, wmask_all, scopes, (None, new)));
     (Some ProphecyName.resolve,  (false, wmask_all, scopes, (None, resolve)));
     (Some ProphecyName.close, (false, wmask_all, scopes, (None, close)))
    ].
  
  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).

  End ProphecyI.

End ProphecyI.

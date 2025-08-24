Require Import CRIS.
Require Export ProphecyHeader ProphecyRA.
Require Import Ensembles.

Set Implicit Arguments.

Module ProphecyA.

  Section ProphecyA.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_prophG: !prophG}.

  Definition scopes := ["Prophecy"].

  Definition new_spec : fspec :=
    fspec_simple
      (λ '(id, P),
        ((λ varg, ⌜varg = id↑⌝ ∗ free_id (.=id))%I,
        (λ vret, ∃ (p : P.(Prophecy.Pro)), ⌜vret = tt↑⌝ ∗ has_proph id (existT P (p, nil))))%I).

  Definition resolve_spec : fspec :=
    fspec_simple
      (λ '(id, existT Proph (p, obs_seq, obs)),
        ((λ varg,
          ⌜varg = (id, obs↑↑)↑⌝
          ∗ has_proph id (existT Proph (p, obs_seq))),
        (λ vret,
          ⌜vret = tt↑ /\ Proph.(Prophecy.consistent) (obs :: obs_seq) p⌝
          ∗ has_proph id (existT Proph (p, obs :: obs_seq))))%I
      ).

  Definition close_spec: fspec :=
    fspec_simple
      (λ '(id, existT Proph (p, obs_seq)),
        ((λ varg, ⌜varg = id↑⌝ ∗ has_proph id (existT Proph (p, obs_seq))),
        (λ vret, ⌜vret = tt↑⌝ ∗ free_id (.=id)))
      )%I.

  Definition sp : spl_type :=
    Seal.sealing CRIS
      [(Some ProphecyName.new, Some new_spec);
       (Some ProphecyName.resolve, Some resolve_spec);
       (Some ProphecyName.close, Some close_spec)
      ].
  
  Definition fnsems : fnsems_type :=
    [(Some ProphecyName.new, (true, wmask_all, scopes, (Some new_spec, fbody_trivial)));
     (Some ProphecyName.resolve, (true, wmask_all, scopes, (Some resolve_spec, fbody_trivial)));
     (Some ProphecyName.close, (true, wmask_all, scopes, (Some close_spec, fbody_trivial)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition initial_cond : iProp Σ := (has_proph_auth (Full_set _) (λ _, dummy_prophinst)) ∗ (free_id_auth (Full_set _)).

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp Mod).

  End ProphecyA.

End ProphecyA.

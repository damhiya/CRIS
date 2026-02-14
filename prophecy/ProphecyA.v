Require Import CRIS.
Require Export ProphecyHeader ProphecyRA.
Require Import Ensembles.

Module ProphecyA. Section ProphecyA.
  Context `{!crisG Γ Σ α β τ _S _I, _PROPH: !prophGS}.
  Context (mn : string).

  Definition scopes : list string := [].

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

  Definition fnsems : fnsemmap :=
    {[fid (ProphecyName.new mn) #
        (msk_scp scopes msk_true, (fsp_some new_spec, fbody_trivial));
      fid (ProphecyName.resolve mn) #
        (msk_scp scopes msk_true, (fsp_some resolve_spec, fbody_trivial));
      fid (ProphecyName.close mn) #
        (msk_scp scopes msk_true, (fsp_some close_spec, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try mod_tac.

  Definition initial_cond : iProp Σ :=
    (has_proph_auth (Full_set _) (λ _, dummy_prophinst)) ∗ (free_id_auth (Full_set _)).

  Definition t sp := SMod.to_mod sp Mod.
End ProphecyA. End ProphecyA.

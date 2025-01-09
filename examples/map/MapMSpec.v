Require Import CRIS.

Require Import MapHeader MapM.

Set Implicit Arguments.

Module MapMS. Section MapMS.
  (* Resource algebra for MapI ⊆ MapM *)
  Class GpreΓ (Γ : HRA) := {
    #[global] map_inG :: inG (exclR unitO) Γ;
  }.
  Class GS (Γ : HRA) := {
    #[global] preΓ :: GpreΓ Γ;
    map_name : positive;
  }.
  Definition GΓ : HRA := #[exclR unitO].
  Global Instance subG_GΓ {Γ} : subG GΓ Γ → GpreΓ Γ.
  Proof. solve_inG. Qed.

  Import MapM.
  Context `{!sinvG Σ Γ α β τ, !GS Γ}.

  Definition pending : iProp Σ := own map_name (Excl ()).
  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    rewrite /pending; unseal "MapMS".
    iIntros "P1 P2"; iCombine "P1 P2" as "P" gives %CONT; ss.
  Qed. 

  Definition init_spec : fspec :=
    fspec_simple
      (λ (sz : nat),
        (λ varg, ⌜varg = [Vint sz]↑ ∧ (8 * sz < modulus_64)%Z⌝ ∗ pending,
          λ vret, emp))%I.

  Definition get_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
          λ vret, emp))%I.

  Definition set_spec : fspec :=
    fspec_simple
      (λ '(k, v),
        (λ varg, ⌜varg = ([Vint k; Vint v])↑⌝,
          λ vret, emp))%I.

  Definition set_by_user_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
          λ vret, emp))%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr"
      [(MapName.init, init_spec);
       (MapName.get, get_spec);
       (MapName.set, set_spec);
       (MapName.set_by_user, set_by_user_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof. by rewrite /Stb; unseal "ccr"; prove_nodup. Qed.

  Definition fnsems :=
    [(MapName.init, (scopes, mk_specbody MapMS.init_spec (cfunU init)));
     (MapName.get, (scopes, mk_specbody MapMS.get_spec (cfunU get)));
     (MapName.set, (scopes, mk_specbody MapMS.set_spec (cfunU set)));
     (MapName.set_by_user, (scopes, mk_specbody MapMS.set_by_user_spec (cfunU set_by_user)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_size, 0%Z↑);
                           (v_map,  (λ (_ : Z), 0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := MapSK.t;
  |}.

  Definition InitCond : Sk.t → iProp Σ :=
    λ _, emp%I.

  Variable ginv : Sk.t → invspec.
  Variable GlobalStb : Sk.t → gname → option (fspec).
  Definition t := Seal.sealing "ccr" (@SMod.to_hmod Σ ginv GlobalStb Mod).
End MapMS. End MapMS.

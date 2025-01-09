Require Import CRIS.

Require Import MapHeader MapA MapMSpec.

Set Implicit Arguments.

(* Resource algebra for MapM ⊆ MapA *)
Local Definition RA : ucmra :=
  prodUR (optionUR (exclR unitO)) (authUR (Z -d> optionUR (exclR ZO))).
Class MapAGΓ (Γ : HRA) := {
  #[global] RA_inG :: inG RA Γ;
}.
Definition MapAΓ : HRA := #[RA].

Module MapAS. Section MapAS.
  Context `{!sinvG Σ Γ α β τ, !MapMGΓ Γ, !MapAGΓ Γ}.
  Import MapA.

  Definition pending : iProp Σ := own 1%positive (Some (Excl ()), ε).

  Local Definition initial_fun : Z -d> optionUR (exclR ZO) := λ z, Some (Excl 0%Z).
  Definition initial_map : iProp Σ := own 1%positive (ε, ● initial_fun ⋅ ◯ initial_fun).

  Definition auth_allocated (f : Z → Z) : iProp Σ :=
    own 1%positive (ε, ● ((λ k, Some (Excl (f k))) : Z -d> optionUR (exclR ZO))).
  Definition auth_unallocated (sz : Z) : iProp Σ :=
    own 1%positive
      (ε,
      ◯ ((λ k,
        if (Z_gt_le_dec 0 k)
        then Some (Excl 0%Z)
        else if (Z_gt_le_dec sz k) then ε else Some (Excl 0%Z)) : Z -d> optionUR (exclR ZO)))%Z.
  Definition points_to (k v : Z) : iProp Σ :=
    own 1%positive (ε, ◯ (discrete_fun_singleton k (Some (Excl v)))).
  Definition initial_points_tos (sz : nat) : iProp Σ :=
    ([∗ list] i↦v ∈ (repeat (0 : Z) sz), points_to i%Z v)%I.

  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE.
    rewrite -pair_op pair_valid in FALSE; des; ss.
  Qed.
  Lemma initialize (sz : nat) :
    initial_map ==∗ auth_allocated (λ _ : Z, 0%Z) ∗ auth_unallocated sz ∗ initial_points_tos sz.
  Proof.
    induction sz; ss.
    { rewrite /initial_map /initial_fun /auth_allocated /auth_unallocated /initial_points_tos; unseal "MapAS".
      iIntros "[I1 I2]"; iSplitL "I1"; first iModIntro; iFrame.
      iSplitL; last iModIntro; ss; iApply (own_update with "I2").
      apply prod_update; ss.
      rewrite cmra_update_proper; try reflexivity.
      f_equiv. ii; des_ifs; lia.
    }
    { iIntros "I"; iMod (IHsz with "I") as "[I1 [I2 I3]]".
      rewrite /initial_map /initial_fun /auth_allocated /auth_unallocated /initial_points_tos; unseal "MapAS".
      replace (S sz) with (sz + 1); last by lia.
      rewrite repeat_app big_opL_app repeat_length; ss.
      iSplitL "I1"; first by iModIntro; iFrame.
      iMod (own_update with "I2") as "[I1 I2]"; cycle 1.
      { iModIntro; iFrame. }
      rewrite -pair_op -auth_frag_op right_id; apply prod_update; ss.
      rewrite cmra_update_proper; try reflexivity.
      f_equiv; ii; rewrite discrete_fun_lookup_op; des_ifs; ss; try lia;
        try by rewrite discrete_fun_lookup_singleton_ne; ss; lia.
      assert (x = sz + 0) by lia; subst.
      rewrite discrete_fun_lookup_singleton; ss.
    }
  Qed.
  Lemma initial_map_points_to k v : initial_map -∗ points_to k v -∗ False.
  Proof.
    rewrite /initial_map /points_to /initial_fun; unseal "MapAS".
    iIntros "[I1 I2] PT"; iCombine "I2" "PT" as "I" gives %FALSE.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in FALSE.
    destruct FALSE as [_ FALSE]. specialize (FALSE k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in FALSE.
  Qed.
  Lemma auth_unallocated_points_to sz k v : auth_unallocated sz -∗ points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
    rewrite /auth_unallocated /points_to; unseal "MapAS".
    iIntros "I PT"; iCombine "I" "PT" as "I" gives %wf.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in wf.
    destruct wf as [_ wf]. specialize (wf k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in wf.
    des_ifs; ss. iPureIntro; lia.
  Qed.
  Lemma auth_allocated_get f k v : auth_allocated f -∗ points_to k v -∗ ⌜f k = v⌝.
  Proof.
    rewrite /auth_allocated /points_to; unseal "MapAS".
    iIntros "A P"; iCombine "A" "P" as "A" gives %wf.
    rewrite -pair_op pair_valid auth_both_valid_discrete /= in wf; des.
    apply (discrete_fun_included_spec_1 _ _ k) in wf0; ss; rewrite discrete_fun_lookup_singleton in wf0.
    rewrite Excl_included in wf0; inv wf0; ss.
  Qed.
  Lemma auth_allocated_set f k v w :
    auth_allocated f -∗ points_to k w ==∗ auth_allocated (<[k := v]> f) ∗ points_to k v.
  Proof.
    rewrite /auth_allocated /points_to; unseal "MapAS".
    iIntros "AU PT"; iCombine "AU" "PT" as "AU".
    iMod (own_update with "AU") as "[AU PT]"; last by iModIntro; iSplitL "AU"; iFrame.
    apply prod_update, auth_update, discrete_fun_local_update; intros x; ss.
    destruct (decide (k = x)); subst.
    { rewrite ?discrete_fun_lookup_singleton fn_lookup_insert.
      apply option_local_update, exclusive_local_update; ss.
    }
    { rewrite ?discrete_fun_lookup_singleton_ne; ss.
      apply local_update_discrete; intros [z|] wf Hz; ss; rewrite ?left_id.
      { rewrite left_id in Hz; rewrite -Hz fn_lookup_insert_ne //=. }
      { inv Hz. }
    }
  Qed.

  Definition init_spec : fspec :=
    fspec_simple
      (λ sz : nat,
        (λ varg, ⌜varg = [Vint sz]↑ ∧ (8 * (Z.of_nat sz) < modulus_64)%Z⌝ ∗ pending,
          λ vret, ⌜vret = Vundef↑⌝ ∗ initial_points_tos sz))%I.

  Definition get_spec: fspec :=
    fspec_simple
      (λ '(k, v),
        (λ varg, ⌜varg = [Vint k]↑⌝ ∗ points_to k v,
          λ vret, ⌜vret = (Vint v)↑⌝ ∗ points_to k v))%I.

  Definition set_spec: fspec :=
    fspec_simple
      (λ '(k, w, v),
        (λ varg, ⌜varg = [Vint k; Vint v]↑⌝ ∗ points_to k w,
          λ vret, ⌜vret = Vundef↑⌝ ∗ points_to k v))%I.

  Definition set_by_user_spec: fspec :=
    fspec_simple
      (λ '(k, w),
        (λ varg, ⌜varg = [Vint k]↑⌝ ∗ points_to k w,
          λ vret, ⌜vret = Vundef↑⌝ ∗ ∃ v, points_to k v))%I.
  
  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr"
      [(MapName.init, init_spec);
       (MapName.get, get_spec);
       (MapName.set, set_spec);
       (MapName.set_by_user, set_by_user_spec)].
  
  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof. unfold Stb. unseal "ccr". prove_nodup. Qed.

  Definition fnsems :=
    [(MapName.init, (scopes, mk_specbody MapAS.init_spec fbody_trivial));
     (MapName.get, (scopes, mk_specbody MapAS.get_spec (cfunN get)));
     (MapName.set, (scopes, mk_specbody MapAS.set_spec (cfunN set)));
     (MapName.set_by_user, (scopes, mk_specbody MapAS.set_by_user_spec (cfunN set_by_user)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_map, (λ _ : Z, 0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := MapSK.t;
  |}.

  Definition InitCond : Sk.t → iProp Σ :=
    (λ _, initial_map ∗ MapMS.pending)%I.

  Variable ginv : Sk.t → invspec.
  Variable GlobalStb : Sk.t → gname → option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).
End MapAS. End MapAS.
Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader.

Set Implicit Arguments.

Module CellAS. Section CellAS.
  Variable idx : nat.
 
  Definition pendingRA : ucmra := (nat -d> optionUR (exclR unitO)).
  Definition cellRA : ucmra := (nat -d> optionUR (exclR ZO)).

  Definition RA : ucmra := prodUR pendingRA (authUR cellRA).

  Class G (Γ : HRA.t) := { #[local] RA_inG :: GRA.inG RA Γ }.
  Context `{!sinvGS Σ Γ α β τ, !G Γ}.

  Notation iProp := (iProp Σ).

  Definition pending_r : RA :=
    ((fun n => if Nat.eq_dec n idx then Excl' tt else ε) : pendingRA, ε).

  Definition pending : iProp :=
    Seal.sealing "CellAS"
      (OwnM pending_r).
 
  Definition cellraw_r (v : Z) : cellRA :=
    (fun n => if Nat.eq_dec n idx then Excl' v else ε).
 
  Definition cell_r (v : Z) : RA :=
    (ε, ◯ (cellraw_r v)).
  Definition cell (v : Z) : iProp :=
    Seal.sealing "CellAS"
      (OwnM (cell_r v)).

  Definition auth_r (v : Z) : RA :=
    (ε, ● (cellraw_r v)).
  Definition auth (v : Z) : iProp :=
    Seal.sealing "CellAS"
      (OwnM (auth_r v)).

  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    rewrite /pending /pending_r; unseal "CellAS".
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE; rewrite -pair_op pair_valid in FALSE; des; ss.
    rr in FALSE; specialize (FALSE idx); des_ifs.
  Qed.

  Lemma cell_unique v v':
    cell v -∗ cell v' -∗ False.
  Proof.
    rewrite /cell /auth /cell_r /cellraw_r; unseal "CellAS".
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE; rewrite -pair_op pair_valid in FALSE; des; ss.
    rewrite -auth_frag_op in FALSE0; apply auth_frag_valid_1 in FALSE0.
    rr in FALSE0; specialize (FALSE0 idx); des_ifs.
  Qed.

  Lemma cell_auth_get v v':
    cell v' -∗ auth v -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth /cell_r; unseal "CellAS"; rewrite /auth_r /cellraw_r.
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    rewrite -pair_op pair_valid auth_both_valid_discrete /= in wf; des.
    apply (discrete_fun_included_spec_1 _ _ idx) in wf0; ss;
    des_ifs.
    by rewrite Excl_included in wf0.
  Qed.

  Lemma cell_auth_set v v':
    cell v -∗ auth v -∗ |==> cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth /cell_r; unseal "CellAS"; rewrite /auth_r /cellraw_r.
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (OwnM_Upd with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU"). 
    rewrite comm; apply prod_update, auth_update, discrete_fun_local_update; intros x; ss.
    destruct (decide (idx = x)); subst; des_ifs.
    apply option_local_update, exclusive_local_update; ss.
  Qed.

  Definition get_spec : fspec :=
    fspec_simple (fun v: Z =>
     ((fun arg => ⌜arg = tt↑⌝ ∗ cell v),
      (fun ret => ⌜ret = v↑⌝ ∗ cell v)))%I.

  Definition set_spec : fspec :=
    fspec_simple (fun '(v0,v) =>
     ((fun arg => ⌜arg = v↑⌝ ∗ (pending ∨ cell v0)),
      (fun ret => ⌜ret = tt↑⌝ ∗ cell v)))%I.

  Definition Stb : alist gname fspec :=
    Seal.sealing "ccr" [(CellName.get idx, get_spec);
                        (CellName.set idx, set_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.
  
End CellAS. End CellAS.

Global Hint Unfold CellAS.Stb : stb.


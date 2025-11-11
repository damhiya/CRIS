(* Resource Algebra for concurrent events *)
Require Import Common.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Export proofmode.

Section concG.
  Class concG `{!crisG Γ Σ α β τ _S _I} := {
    inG_tid :: inG (excl_authUR natO) Γ; (* TID *)
    inG_yield :: inG (nat -d> optionUR (exclR unitO)) Γ (* YIELD *)
  }.
  Definition concΓ : HRA := #[excl_authUR natO; nat -d> optionUR (exclR unitO)].
  Definition concΣ : GRA := #[excl_authUR natO; nat -d> optionUR (exclR unitO)].
  Global Instance subG_concG `{!crisG Γ Σ α β τ _S _I} : subG concΓ Γ → concG.
  Proof using. solve_inG. Defined.
End concG.
Hint Unfold inG_tid inG_yield subG_concG : GRA_index.

Section preds.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* Token for current tid *)
  Definition TidToken (tid : nat) : iProp Σ :=
    Seal.sealing "Conc" own base_γ (◯E tid).
  Arguments TidToken : simpl never.

  Definition TidTokenAuth (tid : nat) : iProp Σ :=
    Seal.sealing "Conc" own base_γ (●E tid).
  Arguments TidTokenAuth : simpl never.

  Lemma TidToken_agree tid0 tid1 : TidToken tid0 -∗ TidTokenAuth tid1 -∗ ⌜tid0 = tid1⌝.
  Proof.
    rewrite /TidToken /TidTokenAuth; unseal "Conc".
    by iIntros "T1 T2"; iCombine "T1 T2" gives %WF%excl_auth_agree_L.
  Qed.

  Lemma TidToken_both tid0 tid1 : TidToken tid0 -∗ TidToken tid1 -∗ False.
  Proof.
    rewrite /TidToken /TidTokenAuth; unseal "Conc".
    by iIntros "T1 T2"; iCombine "T1 T2" gives %WF%excl_auth_frag_op_valid.
  Qed.

  Lemma TidToken_upd tid0 tid1 ntid : TidTokenAuth tid0 ∗ TidToken tid1 ⊢ |==> TidTokenAuth ntid ∗ TidToken ntid.
  Proof.
    rewrite /TidTokenAuth /TidToken. unseal "Conc".
    rewrite -!own_op.
    eapply own_update.
    eapply excl_auth_update.
  Qed.

  Definition YieldToken (tid : nat) : iProp Σ :=
    Seal.sealing "Conc" own base_γ
      ((λ x, if (decide (x = tid)) then Some (Excl ()) else None) : nat -d> optionUR (exclR unitO)).
  Arguments YieldToken : simpl never.

  Definition YieldTokenAuth (nths: nat) : iProp Σ :=
    Seal.sealing "Conc" own base_γ
      ((λ x, if (decide (x < nths)) then None else Some (Excl ())) : nat -d> optionUR (exclR unitO)).

  Lemma YieldToken_both tid0 tid1 : YieldToken tid0 -∗ YieldToken tid1 -∗ ⌜tid0 ≠ tid1⌝.
  Proof.
    rewrite /YieldToken; unseal "Conc".
    iIntros "T1 T2"; iCombine "T1 T2" gives %WF; hexploit (WF tid1).
    rewrite discrete_fun_lookup_op; des_ifs.
  Qed.

  Lemma YieldToken_gen nths : YieldTokenAuth nths ⊢ YieldTokenAuth (S nths) ∗ YieldToken nths.
  Proof.
    rewrite /YieldTokenAuth /YieldToken. unseal "Conc".
    iIntros "T". rewrite -own_op.
    set (a:=_: nat -d> optionUR (exclR unitO)).
    set (b:=_: nat -d> optionUR (exclR unitO)) at 2.
    assert (EQ: a ≡ b).
    { subst a b. intros x. rewrite discrete_fun_lookup_op. des_ifs; nia. }
    rewrite EQ. iFrame.
  Qed.

  Definition ir_tidRA : DRA_mk (excl_authUR natO) := (●E 0 ⋅ ◯E 0).
  Lemma ir_tidRA_valid : ✓ ir_tidRA.
  Proof using. rewrite /ir_tidRA. eapply excl_auth_valid. Qed.

  Definition ir_yieldRA : DRA_mk (nat -d> optionUR (exclR unitO)) := 
    (* (λ x, if (decide (x < 1)) then None else Some (Excl ())). *)
    const (Some (Excl ())).

  Lemma ir_yieldRA_valid : ✓ ir_yieldRA.
  Proof using. rewrite /ir_yieldRA. ii. destruct x; ss. Qed.

  Lemma make_sys_init :
    own base_γ ir_tidRA -∗ own base_γ ir_yieldRA -∗
    TidToken 0 ∗ YieldToken 0 ∗ TidTokenAuth 0 ∗ YieldTokenAuth 1.
  Proof.
    iIntros "T Y".
    rewrite /ir_tidRA /ir_yieldRA /TidToken /YieldToken /TidTokenAuth /YieldTokenAuth.
    unseal "Conc". iDestruct "T" as "[$ $]".
    rewrite -own_op own_proper; first done.
    intros x; rewrite discrete_fun_lookup_op; ss; repeat case_decide; eauto; try lia.
  Qed.
  Definition ir_concΓ : concΓ := *[Some ir_tidRA; Some ir_yieldRA].
End preds.

Notation "'TID' tid" := (TidToken tid) (at level 20, tid at level 1, format "TID  tid").
Notation "'YIELD' tid" := (YieldToken tid) (at level 20, tid at level 1, format "YIELD  tid").
Notation "'TIDAUTH' tid" := (TidTokenAuth tid) (at level 20, tid at level 1, format "TIDAUTH  tid").
Notation "'YIELDAUTH' tid" := (YieldTokenAuth tid) (at level 20, tid at level 1, format "YIELDAUTH  tid").

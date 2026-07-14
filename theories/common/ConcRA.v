(* Resource Algebra for concurrent events *)
From CRIS.common Require Import Common.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Export proofmode.

Class concGpreS `{!cris_coreG Γ Σ α β τ _S _I} := {
  inG_tid :: inG (excl_authUR natO) Γ; (* TID *)
  inG_yield :: inG (nat -d> optionUR (exclR unitO)) Γ (* YIELD *)
}.
Class concGS `{!cris_coreG Γ Σ α β τ _S _I} := {
  concGS_concGpreS : concGpreS;
  tid_name : gname;
  yield_name : gname;
}.
Definition concΓ : HRA := #[excl_authUR natO; nat -d> optionUR (exclR unitO)].
Definition concΣ : GRA := #[excl_authUR natO; nat -d> optionUR (exclR unitO)].
Global Instance subG_concG `{!cris_coreG Γ Σ α β τ _S _I} : subG concΓ Γ → concGpreS.
Proof using. solve_inG. Defined.

Class crisG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t) (_S : subG Γ Σ) (_I : invGS Γ Σ α) := {
  cris_core : cris_coreG Γ Σ α β τ _S _I;
  cris_conc : concGS;
}.
Global Instance crisG_core `{!crisG Γ Σ α β τ _S _I} : cris_coreG Γ Σ α β τ _S _I.
Proof using. apply crisG0. Defined.
Global Instance crisG_conc `{!crisG Γ Σ α β τ _S _I} : concGS.
Proof using. apply crisG0. Defined.

Local Existing Instances concGS_concGpreS inG_tid inG_yield.

Section preds.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* Token for current tid *)
  Definition TidToken (tid : nat) : iProp Σ := own tid_name (◯E tid).
  Arguments TidToken : simpl never.

  Definition TidTokenAuth (tid : nat) : iProp Σ := own tid_name (●E tid).
  Arguments TidTokenAuth : simpl never.

  Lemma TidToken_agree tid0 tid1 : TidToken tid0 -∗ TidTokenAuth tid1 -∗ ⌜tid0 = tid1⌝.
  Proof.
    rewrite /TidToken /TidTokenAuth.
    by iIntros "T1 T2"; iCombine "T1 T2" gives %WF%excl_auth_agree_L.
  Qed.

  Lemma TidToken_both tid0 tid1 : TidToken tid0 -∗ TidToken tid1 -∗ False.
  Proof.
    rewrite /TidToken /TidTokenAuth.
    by iIntros "T1 T2"; iCombine "T1 T2" gives %WF%excl_auth_frag_op_valid.
  Qed.

  Lemma TidToken_upd tid0 tid1 ntid : TidTokenAuth tid0 ∗ TidToken tid1 ⊢ |==> TidTokenAuth ntid ∗ TidToken ntid.
  Proof.
    rewrite /TidTokenAuth /TidToken.
    rewrite -!own_op.
    eapply own_update.
    eapply excl_auth_update.
  Qed.

  Definition YieldToken (tid : nat) : iProp Σ :=
    own yield_name
      ((λ x, if (decide (x = tid)) then Some (Excl ()) else None) : nat -d> optionUR (exclR unitO)).
  Arguments YieldToken : simpl never.

  Definition YieldTokenAuth (nths: nat) : iProp Σ :=
    own yield_name
      ((λ x, if (decide (x < nths)) then None else Some (Excl ())) : nat -d> optionUR (exclR unitO)).

  Lemma YieldToken_both tid0 tid1 : YieldToken tid0 -∗ YieldToken tid1 -∗ ⌜tid0 ≠ tid1⌝.
  Proof.
    rewrite /YieldToken.
    iIntros "T1 T2"; iCombine "T1 T2" gives %WF; hexploit (WF tid1).
    rewrite discrete_fun_lookup_op; des_ifs.
  Qed.

  Lemma YieldToken_gen nths : YieldTokenAuth nths ⊢ YieldTokenAuth (S nths) ∗ YieldToken nths.
  Proof.
    rewrite /YieldTokenAuth /YieldToken.
    iIntros "T". rewrite -own_op.
    set (a:=_: nat -d> optionUR (exclR unitO)).
    set (b:=_: nat -d> optionUR (exclR unitO)) at 2.
    assert (EQ: a ≡ b).
    { subst a b. intros x. rewrite discrete_fun_lookup_op. des_ifs; nia. }
    rewrite EQ. iFrame.
  Qed.
End preds.

Notation "'TID' tid" := (TidToken tid) (at level 20, tid at level 1, format "TID  tid").
Notation "'YIELD' tid" := (YieldToken tid) (at level 20, tid at level 1, format "YIELD  tid").
Notation "'TIDAUTH' tid" := (TidTokenAuth tid) (at level 20, tid at level 1, format "TIDAUTH  tid").
Notation "'YIELDAUTH' tid" := (YieldTokenAuth tid) (at level 20, tid at level 1, format "YIELDAUTH  tid").

Lemma cris_alloc `{!invGpreS Γ Σ inv_instances.α, Hsub: !subG Γ Σ, Hconc: !subG concΓ Γ} :
  ⊢ o=> ∃ (Hinv : invGS Γ Σ inv_instances.α) (β : @GATIntp.t (iProp Σ) inv_instances.α) τ
          (Hcris : @crisG Γ Σ inv_instances.α β τ Hsub Hinv),
    @winv _ _ inv_instances.α _ _ _ (⊤, ⊤) ∗
    @TidToken _ _ inv_instances.α _ _ _ _ _ 0 ∗
    @YieldToken _ _ inv_instances.α _ _ _ _ _ 0 ∗
    @TidTokenAuth _ _ inv_instances.α _ _ _ _ _ 0 ∗
    @YieldTokenAuth _ _ inv_instances.α _ _ _ _ _ 1.
Proof.
  iMod inv_instances.winv_alloc as "[% [% [% [% ?]]]]".
  iMod (own_alloc (●E 0 ⋅ ◯E 0)) as "[% E]"; eauto using excl_auth_valid.
  iMod (own_alloc 
    (((λ x, if (decide (x = 0)) then Some (Excl ()) else None) : nat -d> optionUR (excl unitR)) ⋅
      λ x, if (decide (x < 1)) then None else Some (Excl ()))) as "[%γy Y]".
  { ii; rewrite discrete_fun_lookup_op; des_ifs. }
  iExists _, _, _, (Build_crisG _ _ inv_instances.α _ _ _ _ _ (Build_concGS _ _ inv_instances.α _ _ _ _ _ _ γ γy)).
  instantiate (1:= @in_subG _ _ _ (@inG_yield _ _ inv_instances.α _ _ _ _ _ _) _).
  instantiate (1:= @in_subG _ _ _ (@inG_tid _ _ inv_instances.α _ _ _ _ _ _) _).

  rewrite !own_op; iDestruct "E" as "[$ $]".
  iDestruct "Y" as "[$ $]". done.
Qed.

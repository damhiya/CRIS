(** This library provides assertions that represent "unique tokens".
The [token γ] assertion provides ownership of the token named [γ],
and the key lemma [token_exclusive] proves only one token exists. *)
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From CRIS Require Export own.
From iris.prelude Require Import options.

(** The CMRA we need. *)
Class tokenG Σ := TokenG {
  #[local] token_inG :: inG (exclR unitO) Σ;
}.
Global Hint Mode tokenG - : typeclass_instances.

Definition tokenΣ :=
  #[ (exclR unitO) ].

Global Instance subG_tokenΣ Σ : subG tokenΣ Σ → tokenG Σ.
Proof. solve_inG. Qed.

Local Definition token_def `{!tokenG Σ} (γ : gname) : iProp Σ :=
  own γ (Excl ()).
Local Definition token_aux : seal (@token_def). Proof. by eexists. Qed.
Definition token := token_aux.(unseal).
Local Definition token_unseal :
  @token = @token_def := token_aux.(seal_eq).
Global Arguments token {Σ _} γ.

Local Ltac unseal := rewrite ?token_unseal /token_def.

Section lemmas.
  Context `{!tokenG Σ}.

  Global Instance token_timeless γ : Timeless (token γ).
  Proof. unseal. apply _. Qed.

  (* Lemma token_alloc_strong (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token γ.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed. *)
  Lemma token_alloc :
    ⊢ o=> ∃ γ, token γ.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma token_exclusive γ :
    token γ -∗ token γ -∗ False.
  Proof.
    unseal. iIntros "Htok1 Htok2".
    iCombine "Htok1 Htok2" gives %[].
  Qed.
  Global Instance token_combine_gives γ :
    CombineSepGives (token γ) (token γ) ⌜False⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (token_exclusive with "H1 H2") as %[].
  Qed.

End lemmas.

From CRIS Require Import sProp.

Global Instance subG_tokenΓ {Γ : HRA} :
  subG tokenΣ Γ → tokenG Γ.
Proof. solve_inG. Qed.

Global Instance subHG_token {Γ Σ}:
  subHG Γ Σ → tokenG Γ → tokenG Σ.
Proof. intros ? []. constructor. apply: in_subG. Defined.

(* FIXME: Ideally automatic, but unification of HRA and gFunctors is problematic? *)
Local Instance inGΓ_token {Γ : HRA} :
  tokenG Γ → inG (exclR unitO) Γ.
Proof. intros [Hin]. exact Hin. Defined.

Section syn_tokens.
  Context `{!subHG Γ Σ, !STτ.t τ, !SL.synG Γ τ α, semG0 : !SL.semG Γ τ α Σ β}.
  Context `{TG: !tokenG Γ}.

  Definition syn_token {n} γ : GTerm.t n :=
    sown γ (Excl ()).

  Global Instance token_red n γ :
    SLRed n (syn_token γ) (token γ).
  Proof using semG0. rewrite token_unseal. solve_sl_red. by destruct TG. Qed.
End syn_tokens.

Require Import CRIS.
From iris.algebra Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import fractional.
From iris.prelude Require Import options.

Notation savedPropR :=
  (discrete_funR (λ n, optionUR (dfrac_agreeR (leibnizO (GTerm.t n))))).

Class savedPropG (Σ : GRA) (α : GAT.t) := SavedPropG {
  saved_prop_inG : inG savedPropR Σ;
}.
Local Existing Instance saved_prop_inG.

Definition savedPropΣ (α : GAT.t) : GRA :=
  #[ savedPropR ].

Global Instance subG_savedPropΓ (Σ : GRA) α :
  subG (savedPropΣ α) Σ → savedPropG Σ α.
Proof. solve_inG. Qed.

Section saved_prop.
  Context {Σ : GRA}.
  Context `{!savedPropG Σ α}.

  Definition saved_prop_own
      (γ : gname) (dq : dfrac) {n} (x : GTerm.t n) : iProp Σ := own γ (discrete_fun_singleton n (Some (to_dfrac_agree dq x))).
  Global Typeclasses Opaque saved_prop_own.
  Global Instance: Params (@saved_prop_own) 2 := {}.

  Global Instance saved_prop_own_persistent γ n (x : GTerm.t n) : Persistent (saved_prop_own γ DfracDiscarded x).
  Proof. rewrite /saved_prop_own. apply _. Qed.

  Lemma saved_prop_alloc {n} (x : GTerm.t n) dq :
    ✓ dq →
    ⊢ o=> ∃ γ, saved_prop_own γ dq x.
  Proof. intros ?. by apply own_alloc, discrete_fun_singleton_valid, Some_valid. Qed.

  Lemma saved_prop_valid_2 γ dq1 dq2 {n} (P Q : GTerm.t n) :
    saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ⌜ ✓ (dq1 ⋅ dq2) ∧ P = Q ⌝.
  Proof.
    iIntros "Hx Hy". rewrite /saved_prop_own.
    iCombine "Hx Hy" gives %Hv.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid -Some_op Some_valid in Hv.
    apply dfrac_agree_op_valid_L in Hv. done.
  Qed.

  Lemma saved_prop_update {n} (y : GTerm.t n) γ (x : GTerm.t n) :
    saved_prop_own γ (DfracOwn 1) x ==∗ saved_prop_own γ (DfracOwn 1) y.
  Proof.
    iApply own_update. apply discrete_fun_singleton_update, option_update, cmra_update_exclusive. done.
  Qed.

  (** Make an element read-only. *)
  Lemma saved_prop_persist γ dq {n} (v : GTerm.t n) :
    saved_prop_own γ dq v ==∗ saved_prop_own γ DfracDiscarded v.
  Proof.
    iApply own_update. apply discrete_fun_singleton_update, option_update, dfrac_agree_persist.
  Qed.
End saved_prop.

Section syn_saved_prop_def.
  (* Define syntactic elements. In syntax, we omit the [GTerm.t] stuff *)
  Variant saved_prop_ops : Type :=
  | _saved_prop_own (γ : gname) (dq : dfrac)
  .

  (* Define extra arity for [GTerm.t] *)
  Local Definition saved_prop_arity (op : saved_prop_ops) (sProp : Type) : Type :=
    match op with
    | _saved_prop_own _ _ => fin 1 (* need 1 [GTerm.t] so [fin 1] *)
    end.

  Global Instance saved_prop_syntax : SAT.t := {
    ops := saved_prop_ops;
    arity := saved_prop_arity;
  }.

  (* [saved_prop] interpretations *)
  Local Definition saved_prop_interp_aux `{!savedPropG Σ α} n (op : saved_prop_ops) :
      (saved_prop_arity op (GTerm.t_prev n) → GTerm.t n) →
      (saved_prop_arity op (GTerm.t_prev n) → iProp Σ) →
      iProp Σ
    :=
    match op with
    | _saved_prop_own γ dq => λ syn _,
      (* Here, we "fill in" the missing [GTerm.t] from the provided generator functions. *)
      saved_prop_own γ dq (syn 0%fin)
    end.

  Global Instance saved_prop_interp `{!savedPropG Σ α} :
      @SATIntp.t (@iPropI Σ) α _ :=
    saved_prop_interp_aux.
End syn_saved_prop_def.

Class syn_saved_propG (Σ : GRA) (α : GAT.t) (β : GATIntp.t)
  `{!savedPropG Σ α} := {
  #[local] syn_saved_prop_inG_syntax :: GAT.inG saved_prop_syntax α;
  #[local] syn_saved_prop_inG_interp :: GATIntp.inG saved_prop_syntax α saved_prop_interp β;
}.

Section syn_saved_prop.
  Context `{!subHG Γ Σ, !STτ.t τ, !SL.G Γ Σ α β τ}.
  Context `{!savedPropG Σ α, !syn_saved_propG Σ α β}.

  (* Now defined the actual syntactic definition. Here, we "send" the [GTerm.t] missing in the base
    syntactic definition to the interpertation function. *)
  Definition syn_saved_prop_own {n} γ dq (p : GTerm.t n) : GTerm.t n :=
    ⟨ _saved_prop_own γ dq, λ _, p ⟩.

  Global Instance saved_prop_own_red n γ dq p :
    SLRed n (syn_saved_prop_own γ dq p) (saved_prop_own γ dq p).
  Proof. solve_sl_red. Qed.
End syn_saved_prop.

Global Opaque syn_saved_prop_own.

Notation savedPredR A :=
  (discrete_funR (λ n, optionUR (dfrac_agreeR (leibnizO (A → GTerm.t n))))).

Class savedPredG (Σ : GRA) (A : Type) (α : GAT.t) := SavedPredG {
  saved_pred_inG : inG (savedPredR A) Σ
}.
Local Existing Instance saved_pred_inG.

Definition savedPredΣ (A : Type) (α : GAT.t) : GRA :=
  #[ savedPredR A ].

Global Instance subG_savedPredΣ (Σ : HRA) A α :
  subG (savedPredΣ A α) Σ → savedPredG Σ A α.
Proof. solve_inG. Qed.

Section saved_pred.
  Context `{!savedPredG Σ A α}.

  Definition saved_pred_own
    (γ : gname) (dq : dfrac) {n} (x : A → GTerm.t n) : iProp Σ :=
      own γ (discrete_fun_singleton n (Some (to_dfrac_agree dq (x : leibnizO _)))).
  Global Typeclasses Opaque saved_pred_own.
  Global Instance: Params (@saved_pred_own) 3 := {}.

  Global Instance saved_pred_own_persistent γ {n} (x : A → GTerm.t n) :
    Persistent (saved_pred_own γ DfracDiscarded x).
  Proof. rewrite /saved_pred_own. apply _. Qed.

  Lemma saved_pred_alloc dq {n} (x : A → GTerm.t n) :
    ✓ dq →
    ⊢ o=> ∃ γ, saved_pred_own γ dq x.
  Proof. intros ?. by apply own_alloc, discrete_fun_singleton_valid, Some_valid. Qed.

  Lemma saved_pred_valid_2 γ {n} dq1 dq2 (P Q : A → GTerm.t n) :
    saved_pred_own γ dq1 P -∗ saved_pred_own γ dq2 Q -∗ ⌜ ✓ (dq1 ⋅ dq2) ∧ P = Q ⌝.
  Proof.
    iIntros "Hx Hy". rewrite /saved_pred_own.
    iCombine "Hx Hy" gives %Hv.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid Some_valid in Hv.
    apply dfrac_agree_op_valid_L in Hv. done.
  Qed.

  Lemma saved_pred_update {n} (y : A → GTerm.t n) γ (x : A → GTerm.t n) :
    saved_pred_own γ (DfracOwn 1) x ==∗ saved_pred_own γ (DfracOwn 1) y.
  Proof.
    iApply own_update.
    apply discrete_fun_singleton_update, option_update, cmra_update_exclusive.
    done.
  Qed.

  (** Make an element read-only. *)
  Lemma saved_pred_persist {n} γ dq (v : A → GTerm.t n) :
    saved_pred_own γ dq v ==∗ saved_pred_own γ DfracDiscarded v.
  Proof.
    iApply own_update.
    apply discrete_fun_singleton_update, option_update, dfrac_agree_persist.
  Qed.
End saved_pred.

Section syn_saved_pred_def.
  Variant saved_pred_ops : Type :=
  | _saved_pred_own (γ : gname) (dq : dfrac)
  .

  Local Definition saved_pred_arity (A : Type) (op : saved_pred_ops) (sProp : Type) : Type :=
    match op with
    | _saved_pred_own _ _ => A
    end.

  Global Instance saved_pred_syntax {A : Type} : SAT.t := {
    ops := saved_pred_ops;
    arity := saved_pred_arity A;
  }.

  (* [saved_pred] interpretations *)
  Local Definition saved_pred_interp_aux `{!savedPredG Σ A α}
    n (op : saved_pred_ops) :
    (saved_pred_arity A op (GTerm.t_prev n) → GTerm.t n) →
    (saved_pred_arity A op (GTerm.t_prev n) → iProp Σ) →
    iProp Σ :=
    match op with
    | _saved_pred_own γ dq => λ syn _, saved_pred_own γ dq syn
    end.

  Global Instance saved_pred_interp {A : Type} `{!savedPredG Σ A α} :
    @SATIntp.t (@iPropI Σ) α saved_pred_syntax :=
    saved_pred_interp_aux.
End syn_saved_pred_def.

Class syn_saved_predG (Σ : GRA) (A : Type) (α : GAT.t) (β : GATIntp.t)
  `{!savedPredG Σ A α} := {
  #[local] syn_saved_pred_inG_syntax :: GAT.inG saved_pred_syntax α;
  #[local] syn_saved_pred_inG_interp :: GATIntp.inG saved_pred_syntax α saved_pred_interp β;
}.

Section syn_saved_pred.
  Context `{!subHG Γ Σ, !STτ.t τ, !SL.G Γ Σ α β τ}.
  Context `{!savedPredG Σ A α, !syn_saved_predG Σ A α β}.

  Definition syn_saved_pred_own {n} γ dq (p : A → GTerm.t n) : GTerm.t n :=
    ⟨ _saved_pred_own γ dq : saved_pred_syntax.(SAT.ops), p ⟩.

  Global Instance saved_pred_own_red n γ dq p :
    SLRed n (syn_saved_pred_own γ dq p) (saved_pred_own γ dq p).
  Proof. solve_sl_red. Qed.
End syn_saved_pred.

Global Opaque syn_saved_pred_own.

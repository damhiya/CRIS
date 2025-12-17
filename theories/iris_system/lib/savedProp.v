Require Import CRIS.
From stdpp Require Import gmap.
From iris.algebra Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import fractional.
From iris.prelude Require Import options.

Class savedPropG (Σ : GRA) (α : GAT.t) := SavedPropG {
  saved_prop_inG : inG (discrete_funR (λ n, optionUR (dfrac_agreeR (leibnizO (GTerm.t n))))) Σ
}.
Local Existing Instance saved_prop_inG.

Definition savedPropΣ (α : GAT.t) : GRA :=
  #[ dfrac_agreeR (discrete_funR (λ n, optionUR (dfrac_agreeR (leibnizO (GTerm.t n))))) ].

(* FIXME: Doesn't solve for some stupid reason. *)
(* Global Instance subG_savedPropΓ (Σ : GRA) α :
  subG (savedPropΣ α) Σ → savedPropG Σ α.
Proof. solve_inG. Qed. *)

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
  (* Syntactic invariants *)

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

Class syn_saved_propG (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    `{!savedPropG Σ α} := {
  #[local] syn_saved_prop_inG_syntax :: GAT.inG saved_prop_syntax α;
  #[global] syn_saved_prop_inG_interp :: GATIntp.inG saved_prop_syntax α saved_prop_interp β;
}.

Section syn_wsat.
  Context `{!subHG Γ Σ, !STτ.t τ, !SL.G Γ Σ α β τ}.
  Context `{!savedPropG Σ α, !syn_saved_propG Σ α β τ}.

  (* Now defined the actual syntactic definition. Here, we "send" the [GTerm.t] missing in the base
    syntactic definition to the interpertation function. *)
  Definition syn_saved_prop_own {n} γ dq (p : GTerm.t n) : GTerm.t n :=
    ⟨ _saved_prop_own γ dq, λ _, p ⟩.

  Global Instance saved_prop_own_red n γ dq p :
    SLRed n (syn_saved_prop_own γ dq p) (saved_prop_own γ dq p).
  Proof. solve_sl_red. Qed.
End syn_wsat.

Class savedPredG (Γ : HRA) (α : GAT.t) (n : level) (A : Type) := SavedPredG {
  saved_pred_inG : inG (dfrac_agreeR (leibnizO (A → GTerm.t n))) Γ
}.
Local Existing Instance saved_pred_inG.

Definition savedPredΓ (α : GAT.t) (n : level) (A : Type) : HRA :=
  #[ dfrac_agreeR (leibnizO (A -> GTerm.t n)) ].

Global Instance subG_savedPredΓ (Γ : HRA) α n A :
  subG (savedPredΓ α n A) Γ → savedPredG Γ α n A.
Proof. solve_inG. Qed.

Section saved_pred.
  Context {Γ : HRA} {Σ : GRA} `{!subG Γ Σ}.
  Context `{!savedPredG Γ α n A}.

  Definition saved_pred_own
      (γ : gname) (dq : dfrac) (x : A → GTerm.t n) : iProp Σ := own γ (to_dfrac_agree dq (x : leibnizO _)).
  Global Typeclasses Opaque saved_pred_own.
  Global Instance: Params (@saved_pred_own) 2 := {}.

  Global Instance saved_pred_own_persistent γ x : Persistent (saved_pred_own γ DfracDiscarded x).
  Proof. rewrite /saved_pred_own. apply _. Qed.

  Lemma saved_pred_alloc x dq Ew E `{!crisG Γ Σ α β τ _S _I} :
    ✓ dq →
    ⊢ =|0,Ew|={E}=> ∃ γ, saved_pred_own γ dq x.
  Proof. intros ?. by apply own_alloc. Qed.

  Lemma saved_pred_valid_2 γ dq1 dq2 P Q :
    saved_pred_own γ dq1 P -∗ saved_pred_own γ dq2 Q -∗ ⌜ ✓ (dq1 ⋅ dq2) ∧ P = Q ⌝.
  Proof.
    iIntros "Hx Hy". rewrite /saved_pred_own.
    iCombine "Hx Hy" gives "%Hv".
    apply dfrac_agree_op_valid_L in Hv. done.
  Qed.

  Lemma saved_pred_update y γ x :
    saved_pred_own γ (DfracOwn 1) x ==∗ saved_pred_own γ (DfracOwn 1) y.
  Proof.
    iApply own_update. apply cmra_update_exclusive. done.
  Qed.

  (** Make an element read-only. *)
  Lemma saved_pred_persist γ dq v :
    saved_pred_own γ dq v ==∗ saved_pred_own γ DfracDiscarded v.
  Proof.
    iApply own_update. apply dfrac_agree_persist.
  Qed.
End saved_pred.

Global Instance subG_savedPredΓΣ {Γ : HRA} {Σ : GRA} (α : GAT.t) (n : level) (A : Type) :
  subG Γ Σ → savedPredG Γ α n A → savedPredG Σ α n A.
Proof. intros ? []. constructor. apply _. Defined.

Section syn_saved_pred.
  Context `{!crisG Γ Σ α β τ _S _I, !savedPredG Γ α n A}.

  Definition syn_saved_pred_own (γ : gname) (dq : dfrac) (x : A → GTerm.t n) : GTerm.t n :=
    <own> γ (to_dfrac_agree dq (x : leibnizO _)).

  Global Instance saved_pred_own_red γ dq x :
    SLRed (n:=n) (syn_saved_pred_own γ dq x) (saved_pred_own γ dq x).
  Proof. rewrite /saved_pred_own. apply _. Qed.
End syn_saved_pred.

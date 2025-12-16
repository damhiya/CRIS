From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op coPset.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.
Require Export Coqlib own SAT sProp invariants.

Local Notation level := nat.

(* Syntactic invariants *)
Variant inv_ops : Type :=
| _ownI (i : positive)
| _ownI_reserve (X : coPset)
| _ownD (i : positive)
| _wsat_auth (X : coPset)
.

Local Definition inv_arity (op : inv_ops) (sProp : Type) : Type :=
  match op with
  | _ownI i => fin 1
  | _ownI_reserve X => fin 0
  | _ownD i => fin 1
  | _wsat_auth X => fin 0
  end.

Global Instance inv_syntax : SAT.t := {
  ops := inv_ops;
  arity := inv_arity;
}.

(* Invariant interpretations *)
Local Definition inv_interp_aux `{!invG Γ Σ α, !subG Γ Σ} n (op : inv_ops) :
    (inv_arity op (GTerm.t_prev n) → GTerm.t n) →
    (inv_arity op (GTerm.t_prev n) → iProp Σ) →
    iProp Σ :=
  match op with
  | _ownI i => λ syn _, ownI i (syn 0%fin)
  | _ownI_reserve X => λ _ _, ownI_reserve n X
  | _ownD i => λ syn _, ownD i (syn 0%fin)
  | _wsat_auth X => λ _ _, wsat_auth n X
  end.

Global Instance inv_interp `{!invG Γ Σ α, !subG Γ Σ} :
    @SATIntp.t (iPropI Σ) α _ :=
  inv_interp_aux.

Class syn_invG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    `{!invG Γ Σ α, !subG Γ Σ} := {
  #[global] syn_invG_syntax :: GAT.inG inv_syntax α;
  #[global] syn_invG_interp :: GATIntp.inG inv_syntax α inv_interp β;
}.

Section syn_inv.
  Context `{Σ : GRA, Γ : HRA}.
  Context `{!invG Γ Σ α, !subG Γ Σ, !STτ.t τ, !SL.G Γ Σ α β τ, !syn_invG Γ Σ α β τ}.
  Local Existing Instances invG_I invG_E.

  Local Definition syn_ownI {n} i (p : GTerm.t n) : GTerm.t n :=
    ⟨ _ownI i, λ _, p ⟩.
  Local Definition syn_ownI_reserve {n} X : GTerm.t n :=
    ⟨ _ownI_reserve X, λ e, match e with end⟩.
  Local Definition syn_ownD {n} i (p : GTerm.t n) : GTerm.t n :=
    ⟨ _ownD i, λ _, p ⟩.
  Local Definition syn_wsat_auth n X : GTerm.t n :=
    ⟨ _wsat_auth X, λ e, match e with end ⟩.

  Local Definition syn_ownE {n} (E : coPset) : GTerm.t n :=
    sown enabled_name (CoPset E).

  Local Definition syn_inv_satall {n} (I : gmap positive (GTerm.t n)) : GTerm.t n :=
    [∗ map] i ↦ p ∈ I, syn_ownI i p ∗ ((p ∗ syn_ownD i p) ∨ syn_ownE {[i]}).
  Local Definition syn_wsat n X : GTerm.t (S n) :=
    ∃ I : τ{ST.gmapT Φ}%SAT, let dom := gset_to_coPset (dom I) in
      ⌜dom ⊆ X⌝ ∗ (⤉ syn_inv_satall I) ∗ (⤉ syn_ownI_reserve (X ∖ dom)).

  Local Fixpoint syn_wsatl n X : GTerm.t n :=
    match n with
    | O => emp
    | S n' => ⤉ syn_wsatl n' X ∗ syn_wsat n' X
    end.
  Local Definition syn_wsats n (E : coPset) : GTerm.t n :=
    syn_wsat_auth n E ∗ syn_wsatl n E.

  (* Interface for the user *)
  Definition syn_inv {n : level} (N : namespace) (p : GTerm.t n) : GTerm.t n :=
    ∃ i : τ{⇣positive}%SAT, ⌜i ∈ (↑N : coPset)⌝ ∧ syn_ownI i p.

  Definition syn_fupd {n} (Ew E1 E2 : coPset) (P : GTerm.t n) : GTerm.t n :=
    syn_wsatl n Ew ∗ syn_ownE E1 o==∗
      (syn_wsatl n Ew ∗ syn_ownE E2∗ P).
End syn_inv.

Class crisG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    (SUBG: subG Γ Σ) (INVG: invG Γ Σ α) := crisG_mk {
  #[global] cris_typG :: STτ.t τ;
  #[global] cris_SLG :: SL.G Γ Σ α β τ;
  #[global] cris_syn_invG :: syn_invG Γ Σ α β τ;
}.

Section reduction.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Instance ownI_red n i (p : GTerm.t n) :
    SLRed n (syn_ownI i p) (ownI i p).
  Proof using. solve_sl_red. Qed.
  Local Instance ownI_reserve_red {n} X :
    SLRed n (syn_ownI_reserve X) (ownI_reserve n X).
  Proof using. solve_sl_red. Qed.
  Local Instance ownD_red {n} i (p : GTerm.t n) :
    SLRed n (syn_ownD i p) (ownD i p).
  Proof using. solve_sl_red. Qed.
  Local Instance wsat_auth_red {n} X :
    SLRed n (syn_wsat_auth n X) (wsat_auth n X).
  Proof using. solve_sl_red. Qed.
  Local Instance ownE_red {n} E :
    SLRed n (syn_ownE E) (ownE E).
  Proof using. solve_sl_red. Qed.
  Local Instance inv_satall_red {n} I :
    SLRed n (syn_inv_satall I) (inv_satall I).
  Proof using. solve_sl_red. Qed.

  Local Instance wsat_red {n} X :
    SLRed _ (syn_wsat n X) (wsat n X).
  Proof using. solve_sl_red. Qed.
  Local Instance wsatl_red {n} X :
    SLRed _ (syn_wsatl n X) (wsatl n X).
  Proof using. induction n; rewrite /SLRed /= ?wsatl_S; solve_sl_red. Qed.

  Local Instance wsats_red {n} E :
    SLRed _ (syn_wsats n E) (wsats n E).
  Proof using. solve_sl_red. Qed.

  Global Instance inv_red {n} N p :
    SLRed n (syn_inv N p) (inv n N p).
  Proof using. rewrite invariants.inv_eq. solve_sl_red. Qed.

  Global Instance fupd_red {n} Ew E1 E2 p P :
    SLRed n p P →
    SLRed n (syn_fupd Ew E1 E2 p) (=|n,Ew|={E1,E2}=> P).
  Proof using. rewrite invariants.uPred_fupd_unseal. solve_sl_red. Qed.
End reduction.

Global Opaque syn_inv syn_fupd.

(* Ltac inv_red :=
  hrepeat do 1 tryany (do 1 rewrite ! inv_red) (do 1 rewrite ! fupd_red). *)

(* Module for constructing concrete structures for stratified propositions and global RAs *)
(* Module inv_instances.
  #[export] Instance τ (uτ: TypG.t) : TypG.t :=
    λ i,
      match i with
      | 0 => ST.t
      | S i' => uτ i'
      end.

  #[export] Instance typG `{uτ: TypG.t} : STτ.t (τ uτ).
  Proof using. econs. econs. instantiate (1:=0); ss. Qed.

  #[export] Instance α {Γ : HRA} `{uτ: TypG.t} (uα: GAT.t) : GAT.t :=
    λ i,
      match i with
      | 0 => @SL.syntax Γ (τ uτ)
      | 1 => inv_syntax
      | S (S i') => uα i'
      end.

  #[export] Instance user_in_α {Γ : HRA} `{uτ: TypG.t} `{a: SAT.t} `{uα: GAT.t} `{ing: !GAT.inG a uα} : GAT.inG a (α uα).
  Proof. destruct ing. exists (S(S inG_id)). et. Defined.
  #[export] Instance SL_in_α `{Γ : HRA, uτ : TypG.t, uα : GAT.t} : GAT.inG (@SL.syntax Γ (τ uτ)) (α uα).
  Proof. exists O; ss. Defined.
  #[export] Instance inv_in_α `{Γ : HRA, uτ : TypG.t, uα : GAT.t} : GAT.inG inv_syntax (α uα).
  Proof. exists 1; ss. Defined.

  #[export] Instance β {Γ : HRA} {Σ : GRA} `{uτ: TypG.t} `{uα: GAT.t} (uβ: @GATIntp.t _ (α uα)) `{!subG Γ Σ, !invG Γ Σ (α uα)} : @GATIntp.t _ (α uα) :=
    λ i,
      match i with
      | 0 => @SL.interp Γ Σ (α uα) (τ uτ) _
      | 1 => @inv_interp Γ Σ (α uα) _ _
      | S (S i') => uβ (S (S i'))
      end.

  #[export] Instance intpg {Γ : HRA} {Σ : GRA} `{uτ: TypG.t} `{uα: GAT.t} `{uβ: @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα)}:
    GATIntp.inG (@SL.syntax Γ (τ uτ)) (α uα) (@SL.interp Γ Σ (α uα) (τ uτ) _) (β uβ).
  Proof using. econs; ss. Qed.

  #[export] Instance invintpg {Σ : GRA} {Γ : HRA} `{uτ : TypG.t} `{uα : GAT.t} `{uβ : @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα)} :
    GATIntp.inG inv_syntax (α uα) inv_interp (β uβ).
  Proof using. econs; ss. Qed.

  #[export] Instance crisg {Σ : GRA} {Γ : HRA} `{uτ: TypG.t} `{uα: GAT.t} `{uβ: @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα)} : crisG Γ Σ (α uα) (β uβ) (τ uτ) _ _.
  Proof using.
    econs; econs; try typeclasses eauto.
  Qed.

  #[export] Instance subH_refl (Γ : HRA) : subG Γ Γ.
  Proof using. move=> i; by exists i. Defined.
  Hint Unfold subH_refl : GRA_index.

  #[export] Instance subHG_app_l (Γ Γ1 : HRA) (Σ2 : GRA) : subG Γ Γ1 → subG Γ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.L _ j). by rewrite /= fin_add_inv_l. Defined.

  #[export] Instance subHG_app_r (Γ Γ1 : HRA) (Σ2 : GRA) : subG Γ Σ2 → subG Γ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.

  #[export] Instance subGH_app_r (Σ: GRA) (Γ1 : HRA) (Σ2 : GRA) : subG Σ Σ2 → subG Σ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.
End inv_instances. *)
(* Module inv_instances.
  #[export] Instance τ : TypG.t :=
    λ i,
      match i with
      | _ => ST.t
      end.
  #[export] Instance typG : STτ.t τ.
  Proof using. econs. econs. instantiate (1:=0); ss. Qed.

  #[export] Instance α {Γ : HRA} : GAT.t :=
    λ i,
      match i with
      | 0 => @SL.syntax Γ τ
      | _ => inv_syntax
      end.
  #[export] Instance SL_in_α `{Γ : HRA} : GAT.inG (@SL.syntax Γ τ) α.
  Proof. exists O; ss. Defined.
  #[export] Instance inv_in_α `{Γ : HRA} : GAT.inG inv_syntax α.
  Proof. exists 1; ss. Defined.

  #[export] Instance β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α} : @GATIntp.t _ α :=
    λ i,
      match i with
      | 0 => @SL.interp Γ Σ α τ _
      | _ => @inv_interp Γ Σ α _ _
      end.
  #[export] Instance intpg {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α} :
    GATIntp.inG (@SL.syntax Γ τ) α (@SL.interp Γ Σ α τ _) β.
  Proof using. econs; ss. Qed.
  #[export] Instance invintpg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Γ Σ α} :
    GATIntp.inG inv_syntax α inv_interp β.
  Proof using. econs; ss. Qed.

  #[export] Instance crisg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Γ Σ α} : crisG Γ Σ α β τ _ _.
  Proof using. econs; econs; try typeclasses eauto. Qed.

  #[export] Instance subH_refl (Γ : HRA) : subG Γ Γ.
  Proof using. move=> i; by exists i. Defined.
  Hint Unfold subH_refl : GRA_index.

  #[export] Instance subHG_app_l (Γ Γ1 : HRA) (Σ2 : GRA) : subG Γ Γ1 → subG Γ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.L _ j). by rewrite /= fin_add_inv_l. Defined.

  #[export] Instance subHG_app_r (Γ Γ1 : HRA) (Σ2 : GRA) : subG Γ Σ2 → subG Γ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.

  #[export] Instance subGH_app_r (Σ: GRA) (Γ1 : HRA) (Σ2 : GRA) : subG Σ Σ2 → subG Σ (GRAs.app Γ1 Σ2).
  Proof using. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.
End inv_instances. *)

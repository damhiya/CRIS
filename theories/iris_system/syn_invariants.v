From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op coPset.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.
Require Export Coqlib own SAT sProp invariants.

Section stid_RA.
  Context `{Γ : HRA}. 
  
  Definition stidRA : ucmra := nat -d> excl' unit.

  Class stidG := {
    #[global] stid_inG :: inG stidRA Γ;
  }.

  Definition stidΓ : HRA := #[stidRA].
  Global Instance subG_stidG : subG stidΓ Γ → stidG.
  Proof using. solve_inG. Defined.
End stid_RA.
Global Arguments stidG : clear implicits.
Hint Unfold subG_stidG stid_inG : GRA_index.

Definition stid_r (tid: nat) : stidRA :=
  (λ t, if t =? tid then Excl' tt else ε).

Definition stid `{Γ : HRA} `{Σ: GRA} `{!subG Γ Σ, !stidG Γ} (tid: nat): iProp Σ :=
  own base_γ (stid_r tid).

Local Notation level := nat.

(* Syntactic invariants *)
Variant inv_ops : Type :=
| _ownI (i : positive)
| _ownI_reserve (X : coPset)
| _ownD (i : positive)
| _wsat_auth (X : coPset).

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
    @SATIntp.t (@domain Σ) α _ :=
  inv_interp_aux.

Class syn_invG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    `{!invG Γ Σ α, !subG Γ Σ} := {
  #[global] syn_invG_inG :: GATIntp.inG inv_syntax α inv_interp β;
}.

Section syn_inv.
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

  Local Definition syn_ownE n (E : coPset) : GTerm.t n :=
    <own> base_γ (CoPset E).

  Local Definition syn_inv_satall {n} (I : gmap positive (GTerm.t n)) : GTerm.t n :=
    ([∗ n map] i ↦ p ∈ I, syn_ownI i p ∗ ((syn_ownD i p ∗ p) ∨ syn_ownE n {[i]}))%SAT.
  Local Definition syn_wsat n X : GTerm.t (S n) :=
    (∃ I : τ{ST.gmapT Φ}, let dom := gset_to_coPset (dom I) in
      ⌜dom ⊆ X⌝ ∗ (⤉ syn_inv_satall I) ∗ (⤉ syn_ownI_reserve (X ∖ dom)))%SAT.

  Local Fixpoint syn_wsatl n X : GTerm.t n :=
    match n with
    | O => emp%SAT
    | S n' => syn_wsat n' X ∗ ⤉ syn_wsatl n' X
    end.
  Local Definition syn_wsats n (E : coPset) : GTerm.t n :=
    syn_wsat_auth n E ∗ syn_wsatl n E.

  (* Interface for the user *)
  Local Definition syn_inv_def {n : level} (N : namespace) (p : GTerm.t n) :=
    (∃ i : τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ syn_ownI i p)%SAT.
  Local Definition syn_inv_aux : seal (@syn_inv_def). Proof using. by eexists. Qed.
  Definition syn_inv := syn_inv_aux.(unseal).
  Local Definition syn_inv_eq : @syn_inv = @syn_inv_def := syn_inv_aux.(seal_eq).

  Local Definition syn_fupd_def {n} (Ew E1 E2 : coPset) (P : GTerm.t n) : GTerm.t n :=
    syn_wsatl n Ew ∗ syn_ownE n E1 ==∗ (syn_wsatl n Ew ∗ syn_ownE n E2 ∗ P).
  Local Definition syn_fupd_aux : seal (@syn_fupd_def). Proof using. by eexists. Qed.
  Definition syn_fupd := syn_fupd_aux.(unseal).
  Local Definition syn_fupd_eq : @syn_fupd = @syn_fupd_def := syn_fupd_aux.(seal_eq).
End syn_inv.

Class crisG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    (SUBG: subG Γ Σ) (INVG: invG Γ Σ α) (STIDG: stidG Γ) := crisG_mk {
  #[global] cris_typG :: STτ.t τ;
  #[global] cris_SLG :: SL.G Γ Σ α β τ;
  #[global] cris_syn_invG :: syn_invG Γ Σ α β τ;
}.

Section reduction.
  Context `{!crisG Γ Σ α β τ _S _I _T}.

  Implicit Types (n : level) (X : coPset).
  Lemma wsat_red n X : ⟦syn_wsat n X⟧ ≡ wsat n X.
  Proof using.
    rewrite /syn_wsat /wsat; SAT_red; SL_red.
    iSplit; iIntros "[%I H]"; SL_red.
    { rewrite ?@SATRed.lift. SAT_red. rewrite /syn_inv_satall; SL_red.
      iExists I; iDestruct "H" as "[$ [H $]]".
      rewrite /inv_satall. iApply (big_sepM_mono with "H"); ss.
      intros k x IN; SL_red; SAT_red; ss.
      iIntros "[$ [[??]|$]]"; iLeft; iFrame.
    }
    { iExists I; SL_red; SAT_red.
      iDestruct "H" as "[$ [H $]]".
      rewrite /syn_inv_satall; SL_red. iApply (big_sepM_mono with "H"); ss.
      intros k x IN; SL_red; SAT_red; ss.
      iIntros "[$ [[??]|$]]"; iLeft; iFrame.
    }
  Qed.

  Lemma wsatl_red n X : ⟦syn_wsatl n X⟧ ≡ wsatl n X.
  Proof using.
    induction n.
    { SAT_red; SL_red; ss. }
    { simpl syn_wsatl. SAT_red; ss. rewrite /wsatl seq_S big_sepL_app //=.
      rewrite wsat_red; SAT_red; rewrite IHn; iSplit; iIntros "[$ H]"; iFrame.
      iDestruct "H" as "[??]"; iFrame.
    }
  Qed.
  
  Lemma wsats_red n E : ⟦syn_wsats n E⟧ ≡ wsats n E.
  Proof using.
    rewrite /syn_wsats /syn_ownE. SAT_red. SL_red.
    rewrite wsatl_red; SAT_red; ss; rewrite /wsats /ownD_auth.
  Qed.

  Lemma inv_red n N p : ⟦syn_inv n N p⟧ ≡ inv n N p.
  Proof using.
    rewrite syn_inv_eq /syn_inv_def. SL_red.
    rewrite /inv invariants.inv_aux.(seal_eq) /invariants.inv_def.
    iSplit; iIntros "[%x H]"; iExists x; SL_red; SAT_red; ss.
  Qed.

  Lemma fupd_red n Ew E1 E2 P : ⟦syn_fupd n Ew E1 E2 P⟧ ≡ uPred_fupd n Ew E1 E2 ⟦P⟧.
  Proof using.
    rewrite syn_fupd_eq /uPred_fupd invariants.uPred_fupd_aux.(seal_eq) /invariants.uPred_fupd_def.
    rewrite /syn_fupd_def SLRed.wand SLRed.upd. repeat SAT_red.
    rewrite wsatl_red /wsatl /syn_ownE; SL_red. done.
  Qed.
End reduction.

Ltac inv_red :=
  hrepeat do 1 tryany (do 1 rewrite ! inv_red) (do 1 rewrite ! fupd_red).

(* Module for constructing concrete structures for stratified propositions and global RAs *)
Module inv_instances.
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

  #[export] Instance user_subG {Γ : HRA} `{uτ: TypG.t} `{a: SAT.t} `{uα: GAT.t} `{ing: !GAT.inG a uα} : GAT.inG a (α uα).
  Proof. destruct ing. exists (S(S inG_id)). et. Defined.

  #[export] Instance β {Γ : HRA} {Σ : GRA} `{uτ: TypG.t} `{uα: GAT.t} (uβ: @GATIntp.t _ (α uα)) `{!subG Γ Σ, !invG Γ Σ (α uα)} : @GATIntp.t _ (α uα) :=
    λ i,
      match i with
      | 0 => @SL.interp Γ Σ (α uα) (τ uτ) _
      | 1 => @inv_interp Γ Σ (α uα) _ _
      | S (S i') => uβ (S (S i'))
      end.

  #[export] Instance intpg {Γ : HRA} {Σ : GRA} `{uτ: TypG.t} `{uα: GAT.t} `{uβ: @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα)}:
    GATIntp.inG (@SL.syntax Γ (τ uτ)) (α uα) (@SL.interp Γ Σ (α uα) (τ uτ) _) (β uβ).
  Proof using. econs; instantiate (1:=0); ss. Qed.

  #[export] Instance invintpg {Σ : GRA} {Γ : HRA} `{uτ: TypG.t} `{uα: GAT.t} `{uβ: @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα)} :
    GATIntp.inG inv_syntax (α uα) inv_interp (β uβ).
  Proof using. econs; instantiate (1:=1); ss. Qed.

  #[export] Instance crisg {Σ : GRA} {Γ : HRA} `{uτ: TypG.t} `{uα: GAT.t} `{uβ: @GATIntp.t _ (α uα)} `{!subG Γ Σ, !invG Γ Σ (α uα), !stidG Γ} : crisG Γ Σ (α uα) (β uβ) (τ uτ) _ _ _.
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
End inv_instances.

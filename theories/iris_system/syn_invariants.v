From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op.
From iris.proofmode Require Import proofmode.
Require Export Coqlib own SAT sProp invariants.

Local Notation level := nat.

(* Syntactic invariants *)
Variant inv_ops : Type :=
| _ownI (u : univ_id) (i : positive)
| _ownI_auth (u : univ_id) (keys : gmap positive unit)
| _wsat_auth (u : univ_id).

Local Definition inv_arity (op : inv_ops) (sProp : Type) : Type :=
  match op with
  | _ownI u i => fin 1
  | _ownI_auth u keys => positive
  | _wsat_auth u => fin 0
  end.

Global Instance inv_syntax : SAT.t := {
  ops := inv_ops;
  arity := inv_arity;
}.

(* Invariant interpretations *)
Local Definition inv_interp_aux `{!invG Γ Σ α, !subG Γ Σ} n (op : inv_ops) :
    (inv_arity op (GTerm.t_prev n) → GTerm.t n) → (inv_arity op (GTerm.t_prev n) → iProp Σ)
    → iProp Σ :=
  match op with
  | _ownI u i => λ syn _, ownI u n i (syn 0%fin)
  | _ownI_auth u keys => λ syn _, ownI_auth u n (map_imap (λ k v, Some (syn k)) keys)
  | _wsat_auth u => λ _ _, wsat_auth u n
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
  Local Existing Instances invG_I invG_E invG_D.

  Local Definition syn_ownI u n i (p : GTerm.t n) : GTerm.t n :=
    ⟨ _ownI u i, λ _, p ⟩.
  Local Definition syn_ownI_auth u n (I : gmap positive (GTerm.t n)) : GTerm.t n :=
    ⟨ _ownI_auth u (gset_to_gmap tt (dom I)), λ i, or_else (I !! i) emp%SAT⟩.
  Local Definition syn_wsat_auth u n : GTerm.t n :=
    ⟨ _wsat_auth u, λ e, match e with end ⟩.

  Local Definition syn_ownE (u : univ_id) n (E : coPset) : GTerm.t n :=
    <own> base_γ (ownER u E).
  Local Definition syn_ownD (u : univ_id) n (D : gset positive) : GTerm.t n :=
    <own> base_γ (ownDR u D).
  Local Definition syn_ownD_auth (u : univ_id) n : GTerm.t n :=
    (∃ D : τ{⇣gset positive}, <own> base_γ (ownD_authR u D))%SAT.

  Local Definition syn_inv_satall u n (I : gmap positive (GTerm.t n)) : GTerm.t n :=
    ([∗ n map] i ↦ p ∈ I, (p ∗ syn_ownD u n {[i]}) ∨ syn_ownE u n {[i]})%SAT.
  Local Definition syn_wsat u n : GTerm.t (S n) :=
    (∃ I : τ{ST.gmapT Φ}, (⤉ syn_ownI_auth u n I) ∗ (⤉ syn_inv_satall u n I))%SAT.

  Local Fixpoint syn_wsatl u n : GTerm.t n :=
    match n with
    | O => emp%SAT
    | S n' => syn_wsat u n' ∗ ⤉ syn_wsatl u n'
    end.
  Local Definition syn_wsats u n (E : coPset) : GTerm.t n :=
    syn_wsat_auth u n ∗ syn_ownE u n E ∗ syn_ownD_auth u n ∗ syn_wsatl u n.

  (* Interface for the user *)
  Local Definition syn_inv_def (u : univ_id) (n : level) (N : namespace) p :=
    (∃ i : τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ syn_ownI u n i p)%SAT.
  Local Definition syn_inv_aux : seal (@syn_inv_def). Proof using. by eexists. Qed.
  Definition syn_inv := syn_inv_aux.(unseal).
  Local Definition syn_inv_eq : @syn_inv = @syn_inv_def := syn_inv_aux.(seal_eq).

  Local Definition syn_fupd_def u b (E1 E2 : coPset) (P : GTerm.t b) : GTerm.t b :=
    syn_wsatl u b ∗ syn_ownE u b E1 ∗ syn_ownD_auth u b
    ==∗ (syn_wsatl u b ∗ syn_ownE u b E2 ∗ syn_ownD_auth u b ∗ P).
  Local Definition syn_fupd_aux : seal (@syn_fupd_def). Proof using. by eexists. Qed.
  Definition syn_fupd := syn_fupd_aux.(unseal).
  Local Definition syn_fupd_eq : @syn_fupd = @syn_fupd_def := syn_fupd_aux.(seal_eq).
End syn_inv.

Class sinvG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t)
    (INVG: invG Γ Σ α) (SUBG: subG Γ Σ) := sinvG_mk {
  #[global] sinv_typG :: STτ.t τ;
  #[global] sinv_SLG :: SL.G Γ Σ α β τ;
  #[global] sinv_syn_invG :: syn_invG Γ Σ α β τ;
}.

Section reduction.
  Context `{!sinvG Γ Σ α β τ _I _S}.

  Lemma ownI_auth_red u n I :
    ⟦syn_ownI_auth u n I⟧ = ownI_auth u n I.
  Proof using.
    SAT_red; ss.
    f_equal. apply map_eq; intros i.
    destruct (decide (i ∈ dom I)).
    { rewrite map_lookup_imap lookup_gset_to_gmap //=. case_guard; ss. apply elem_of_dom in e; ss.
      destruct (I !! i); ss; inv e.
    }
    { rewrite map_lookup_imap lookup_gset_to_gmap //=. case_guard; ss.
      rewrite not_elem_of_dom_1; eauto.
    }
  Qed.

  Lemma wsat_red u n : ⟦syn_wsat u n⟧ ≡ wsat u n.
  Proof using.
    rewrite /syn_wsat /wsat; SAT_red; SL_red.
    iSplit; iIntros "[%I H]"; SL_red.
    { rewrite @SATRed.lift ownI_auth_red. SAT_red. rewrite /syn_inv_satall; SL_red.
      iExists I; iDestruct "H" as "[$ H]".
      rewrite /inv_satall. iApply (big_sepM_mono with "H"); ss.
      rewrite /ownD /ownE. intros k x IN; SL_red; ss.
    }
    { iExists I; SL_red; rewrite !@SATRed.lift ownI_auth_red /syn_inv_satall; SL_red.
      iDestruct "H" as "[$ H]".
      rewrite /inv_satall. iApply (big_sepM_mono with "H"); ss.
      rewrite /ownD /ownE. intros k x IN; SL_red; ss.
    }
  Qed.

  Lemma wsatl_red u n : ⟦syn_wsatl u n⟧ ≡ wsatl u n.
  Proof using.
    induction n.
    { SAT_red; SL_red; ss. }
    { simpl syn_wsatl. SAT_red; ss. rewrite /wsatl seq_S big_sepL_app //=.
      rewrite wsat_red; SAT_red; rewrite IHn; iSplit; iIntros "[$ H]"; iFrame.
      iDestruct "H" as "[??]"; iFrame.
    }
  Qed.
  
  Lemma wsats_red u n E : ⟦syn_wsats u n E⟧ ≡ wsats u n E.
  Proof using.
    rewrite /syn_wsats /syn_ownE /syn_ownD_auth. SAT_red. SL_red.
    rewrite wsatl_red; SAT_red; ss; rewrite /wsats /ownD_auth.
    iSplit; iIntros "($ & $ & [%x H] & $)"; iExists x; SL_red; iFrame.
  Qed.

  Lemma inv_red u n N p : ⟦syn_inv u n N p⟧ ≡ inv u n N p.
  Proof using.
    rewrite syn_inv_eq /syn_inv_def. SL_red.
    rewrite /inv invariants.inv_aux.(seal_eq) /invariants.inv_def.
    iSplit; iIntros "[%x H]"; iExists x; SL_red; SAT_red; ss.
  Qed.

  Lemma fupd_red u n E1 E2 P : ⟦syn_fupd u n E1 E2 P⟧ ≡ uPred_fupd u n E1 E2 ⟦P⟧.
  Proof using.
    rewrite syn_fupd_eq /uPred_fupd invariants.uPred_fupd_aux.(seal_eq) /invariants.uPred_fupd_def.
    rewrite /syn_fupd_def SLRed.wand SLRed.upd. repeat SAT_red.
    rewrite wsatl_red /wsatl /syn_ownE /syn_ownD_auth; SL_red.
    iSplit; iIntros "I [W [E [%x D]]]"; iMod ("I" with "[W E D]") as "[$ [$ [[%x' I] $]]]"; SL_red; iFrame.
    all: ss; iExists _; SL_red; ss.
  Qed.
End reduction.

Ltac inv_red :=
  hrepeat do 1 tryany (do 1 rewrite ! inv_red) (do 1 rewrite ! fupd_red).

(* Module for constructing concrete structures for stratified propositions and global RAs *)
Module inv_instances.
  #[export] Instance τ : TypG.t := λ _, ST.t.

  #[export] Instance typG : STτ.t τ.
  Proof using. econs. econs. instantiate (1:=0); ss. Qed.

  #[export] Instance α {Γ : HRA} : GAT.t :=
    λ n,
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.

  #[export] Instance β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α} : GATIntp.t :=
    λ n,
      match n with
      | 0 => SL.interp
      | _ => inv_interp
      end.

  #[export] Instance intpG {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α} :
    GATIntp.inG (@SL.syntax Γ τ) α (@SL.interp Γ Σ α τ _) β.
  Proof using. econs; instantiate (1:=0); ss. Qed.

  #[export] Instance invintpG {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Γ Σ α} :
    GATIntp.inG inv_syntax α inv_interp β.
  Proof using. econs; instantiate (1:=1); ss. Qed.

  #[export] Instance sinvg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Γ Σ α} : sinvG Γ Σ α β τ _ _.
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

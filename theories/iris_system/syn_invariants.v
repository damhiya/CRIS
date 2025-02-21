From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op.
Require Export Coqlib own SRF sProp invariants.

Local Notation level := nat.

(* Syntactic invariants *)
Variant inv_shape : Type :=
| _ownI (u : univ_id) (i : positive)
| _ownI_auth (u : univ_id) (keys : gmap positive unit)
| _wsat_auth (u : univ_id).

Local Definition inv_degree (s : inv_shape) (sProp : Type) : Type :=
  match s with
  | _ownI u i => fin 1
  | _ownI_auth u keys => positive
  | _wsat_auth u => fin 0
  end.

Global Instance inv_syntax : PF.t := {
  shp := inv_shape;
  deg := inv_degree;
}.

(* Invariant interpretations *)
Local Definition inv_interp_aux `{!invG α Σ Γ, !subG Γ Σ} n (s : inv_shape) :
    (inv_degree s (SRFSyn.t_prev n) → SRFSyn.t n) → (inv_degree s (SRFSyn.t_prev n) → iProp Σ)
    → iProp Σ :=
  match s with
  | _ownI u i => λ syn _, ownI u n i (syn 0%fin)
  | _ownI_auth u keys => λ syn _, ownI_auth u n (map_imap (λ k v, Some (syn k)) keys)
  | _wsat_auth u => λ _ _, wsat_auth u n
  end.

Global Instance inv_interp `{!invG α Σ Γ, !subG Γ Σ} :
    @SRFIntpM.t (@domain Σ) α _ :=
  inv_interp_aux.

Class syn_invG (Σ : GRA) (Γ : HRA) (α : SRFCons.t) (β : SRFIntp.t) (τ : TypG.t)
    `{!invG α Σ Γ, !subG Γ Σ} := {
  #[global] syn_invG_inG :: SRFIntp.inG inv_syntax α inv_interp β;
}.

Section syn_inv.
  Context `{!invG α Σ Γ, !subG Γ Σ, !CtxST.t τ, !SL.G Σ Γ α β τ, !syn_invG Σ Γ α β τ}.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.

  Local Definition syn_ownI u n i (p : SRFSyn.t n) : SRFSyn.t n :=
    ⟨ _ownI u i, λ _, p ⟩.
  Local Definition syn_ownI_auth u n (I : gmap positive (SRFSyn.t n)) : SRFSyn.t n :=
    ⟨ _ownI_auth u (gset_to_gmap tt (dom I)), λ i, or_else (I !! i) emp%SRF⟩.
  Local Definition syn_wsat_auth u n : SRFSyn.t n :=
    ⟨ _wsat_auth u, λ e, match e with end ⟩.

  Local Definition syn_ownE (u : univ_id) n (E : coPset) : SRFSyn.t n :=
    <own> base_γ (ownER u E).
  Local Definition syn_ownD (u : univ_id) n (D : gset positive) : SRFSyn.t n :=
    <own> base_γ (ownDR u D).
  Local Definition syn_ownD_auth (u : univ_id) n : SRFSyn.t n :=
    (∃ D : τ{⇣gset positive}, <own> base_γ (ownD_authR u D))%SRF.

  Local Definition syn_inv_satall u n (I : gmap positive (SRFSyn.t n)) : SRFSyn.t n :=
    ([∗ n map] i ↦ p ∈ I, (p ∗ syn_ownD u n {[i]}) ∨ syn_ownE u n {[i]})%SRF.
  Local Definition syn_wsat u n : SRFSyn.t (S n) :=
    (∃ I : τ{ST.gmapT Φ}, (⤉ syn_ownI_auth u n I) ∗ (⤉ syn_inv_satall u n I))%SRF.

  Local Fixpoint syn_wsatl u n : SRFSyn.t n :=
    match n with
    | O => emp%SRF
    | S n' => syn_wsat u n' ∗ ⤉ syn_wsatl u n'
    end.
  Local Definition syn_wsats u n (E : coPset) : SRFSyn.t n :=
    syn_wsat_auth u n ∗ syn_ownE u n E ∗ syn_ownD_auth u n ∗ syn_wsatl u n.

  (* Interface for the user *)
  Local Definition syn_inv_def (u : univ_id) (n : level) (N : namespace) p :=
    (∃ i : τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ syn_ownI u n i p)%SRF.
  Local Definition syn_inv_aux : seal (@syn_inv_def). Proof. by eexists. Qed.
  Definition syn_inv := syn_inv_aux.(unseal).
  Local Definition syn_inv_eq : @syn_inv = @syn_inv_def := syn_inv_aux.(seal_eq).

  Local Definition syn_fupd_def u b (E1 E2 : coPset) (P : SRFSyn.t b) : SRFSyn.t b :=
    syn_wsatl u b ∗ syn_ownE u b E1 ∗ syn_ownD_auth u b
    ==∗ (syn_wsatl u b ∗ syn_ownE u b E2 ∗ syn_ownD_auth u b ∗ P).
  Local Definition syn_fupd_aux : seal (@syn_fupd_def). Proof. by eexists. Qed.
  Definition syn_fupd := syn_fupd_aux.(unseal).
  Local Definition syn_fupd_eq : @syn_fupd = @syn_fupd_def := syn_fupd_aux.(seal_eq).
End syn_inv.

Class sinvG (Σ : GRA) (Γ : HRA) (α : SRFCons.t) (β : SRFIntp.t) (τ : TypG.t)
    `{!invG α Σ Γ, !subG Γ Σ} := sinvG_mk {
  #[global] sinv_typG :: CtxST.t τ;
  #[global] sinv_SLG :: SL.G Σ Γ α β τ;
  #[global] sinv_syn_invG :: syn_invG Σ Γ α β τ;
}.

Section reduction.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Lemma ownI_auth_red u n I :
    ⟦syn_ownI_auth u n I⟧ = ownI_auth u n I.
  Proof.
    SRF_red; ss.
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
  Proof.
    rewrite /syn_wsat /wsat; SRF_red; SL_red.
    iSplit; iIntros "[%I H]"; SL_red.
    { rewrite @SRFRed.lift ownI_auth_red. SRF_red. rewrite /syn_inv_satall; SL_red.
      iExists I; iDestruct "H" as "[$ H]".
      rewrite /inv_satall. iApply (big_sepM_mono with "H"); ss.
      rewrite /ownD /ownE. intros k x IN; SL_red; ss.
    }
    { iExists I; SL_red; rewrite !@SRFRed.lift ownI_auth_red /syn_inv_satall; SL_red.
      iDestruct "H" as "[$ H]".
      rewrite /inv_satall. iApply (big_sepM_mono with "H"); ss.
      rewrite /ownD /ownE. intros k x IN; SL_red; ss.
    }
  Qed.

  Lemma wsatl_red u n : ⟦syn_wsatl u n⟧ ≡ wsatl u n.
  Proof.
    induction n.
    { SRF_red; SL_red; ss. }
    { simpl syn_wsatl. SRF_red; ss. rewrite /wsatl seq_S big_sepL_app //=.
      rewrite wsat_red; SRF_red; rewrite IHn; iSplit; iIntros "[$ H]"; iFrame.
      iDestruct "H" as "[??]"; iFrame.
    }
  Qed.
  
  Lemma wsats_red u n E : ⟦syn_wsats u n E⟧ ≡ wsats u n E.
  Proof.
    rewrite /syn_wsats /syn_ownE /syn_ownD_auth. SRF_red. SL_red.
    rewrite wsatl_red; SRF_red; ss; rewrite /wsats /ownD_auth.
    iSplit; iIntros "($ & $ & [%x H] & $)"; iExists x; SL_red; iFrame.
  Qed.

  Lemma inv_red u n N p : ⟦syn_inv u n N p⟧ ≡ inv u n N p.
  Proof.
    rewrite syn_inv_eq /syn_inv_def. SL_red.
    rewrite /inv invariants.inv_aux.(seal_eq) /invariants.inv_def.
    iSplit; iIntros "[%x H]"; iExists x; SL_red; SRF_red; ss.
  Qed.

  Lemma fupd_red u n E1 E2 P : ⟦syn_fupd u n E1 E2 P⟧ ≡ uPred_fupd u n E1 E2 ⟦P⟧.
  Proof.
    rewrite syn_fupd_eq /uPred_fupd invariants.uPred_fupd_aux.(seal_eq) /invariants.uPred_fupd_def.
    rewrite /syn_fupd_def SLRed.wand SLRed.upd. repeat SRF_red.
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

  #[export] Instance typG : CtxST.t τ.
  Proof. econs. econs. instantiate (1:=0); ss. Qed.

  #[export] Instance α {Γ : HRA} : SRFCons.t :=
    λ n,
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.

  #[export] Instance β {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG α Σ Γ} : SRFIntp.t :=
    λ n,
      match n with
      | 0 => SL.interp
      | _ => inv_interp
      end.

  #[export] Instance intpG {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG α Σ Γ} :
    SRFIntp.inG (@SL.syntax τ Γ) α (@SL.interp τ α Γ Σ _) β.
  Proof. econs; instantiate (1:=0); ss. Qed.

  #[export] Instance invintpG {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG α Σ Γ} :
    SRFIntp.inG inv_syntax α inv_interp β.
  Proof. econs; instantiate (1:=1); ss. Qed.

  #[export] Instance sinvg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG α Σ Γ} : sinvG Σ Γ α β τ.
  Proof.
    econs; econs; try typeclasses eauto.
  Qed.

  #[export] Instance subG_refl (Γ : HRA) : subG Γ Γ.
  Proof. move=> i; by exists i. Defined.
  Hint Unfold subG_refl : GRA_index.

  #[export] Instance subG_app_l_HRA (Γ : HRA) (Σ1 Σ2 : GRA) : subG Γ Σ1 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.L _ j). by rewrite /= fin_add_inv_l. Defined.
  Lemma subG_app_l_HRA_inG_id Γ Σ1 Σ2 subGins i :
    (subG_app_l_HRA Γ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.L _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_l (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_l_HRA. destruct (subGins i). reflexivity. Qed.

  #[export] Instance subG_app_r_HRA (Γ : HRA) (Σ1 Σ2 : GRA) : subG Γ Σ2 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.
  Lemma subG_app_r_HRA_inG_id Γ Σ1 Σ2 subGins i :
      (subG_app_r_HRA Γ Σ1 Σ2 subGins) i
      = let '(exist _ j jprf) := subGins i in
        exist _ (Fin.R _ j)
        (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_r (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_r_HRA. destruct (subGins i). reflexivity. Qed.

  #[export] Instance subG_app_l_HRA' (Γ Σ1 : HRA) (Σ2 : GRA) : subG Γ Σ1 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.L _ j). by rewrite /= fin_add_inv_l. Defined.
  Lemma subG_app_l_HRA'_inG_id Γ Σ1 Σ2 subGins i :
    (subG_app_l_HRA' Γ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.L _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_l (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_l_HRA'. destruct (subGins i). reflexivity. Qed.

  #[export] Instance subG_app_r_HRA' (Γ Σ2 : HRA) (Σ1 : GRA) : subG Γ Σ2 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.
  Lemma subG_app_r_HRA'_inG_id Γ Σ1 Σ2 subGins i :
      (subG_app_r_HRA' Γ Σ1 Σ2 subGins) i
      = let '(exist _ j jprf) := subGins i in
        exist _ (Fin.R _ j)
        (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_r (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_r_HRA'. destruct (subGins i). reflexivity. Qed.

  #[export] Instance subG_app_l_HRA'' (Γ Σ2 : HRA) (Σ1 : GRA) : subG Γ Σ1 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.L _ j). by rewrite /= fin_add_inv_l. Defined.
  Lemma subG_app_l_HRA''_inG_id Γ Σ1 Σ2 subGins i :
    (subG_app_l_HRA'' Γ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.L _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_l (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_l_HRA''. destruct (subGins i). reflexivity. Qed.

  #[export] Instance subG_app_r_HRA'' (Γ Σ1 : HRA) (Σ2 : GRA) : subG Γ Σ2 → subG Γ (GRAs.app Σ1 Σ2).
  Proof. move=> H i; move: H=> /(_ i) [j ?]. exists (Fin.R _ j). by rewrite /= fin_add_inv_r. Defined.
  Lemma subG_app_r_HRA''_inG_id Γ Σ1 Σ2 subGins i :
    (subG_app_r_HRA'' Γ Σ1 Σ2 subGins) i
    = let '(exist _ j jprf) := subGins i in
      exist _ (Fin.R _ j)
      (eq_ind_r (λ p : DRA, GRA_lookup i = p) jprf (fin_add_inv_r (λ _ : fin (GRA_len + GRA_len), DRA) GRA_lookup GRA_lookup j)).
  Proof. unfold subG_app_r_HRA''. destruct (subGins i). reflexivity. Qed.

  Ltac solve_in_subG_goal :=
    autounfold with GRA_index;
    hrepeat do 1 match goal with
    | [|- context [inG_id (in_subG _ _ _)]] => rewrite inG_id_in_subG
    | [|- context [subG_app_r_HRA _ _ _ _ _]] => rewrite subG_app_r_HRA_inG_id
    | [|- context [subG_app_r_HRA' _ _ _ _ _]] => rewrite subG_app_r_HRA'_inG_id
    | [|- context [subG_app_r_HRA'' _ _ _ _ _]] => rewrite subG_app_r_HRA''_inG_id
    | [|- context [subG_app_l_HRA _ _ _ _ _]] => rewrite subG_app_l_HRA_inG_id
    | [|- context [subG_app_l_HRA' _ _ _ _ _]] => rewrite subG_app_l_HRA'_inG_id
    | [|- context [subG_app_l_HRA'' _ _ _ _ _]] => rewrite subG_app_l_HRA''_inG_id
    | [|- context [subG_refl _ _]] => unfold subG_refl
    | [|- context [inG_id (subG_inG _ _ _)]] => rewrite (inG_id_subG_inG _)
    end.

End inv_instances.

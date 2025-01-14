From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op.
Require Import Coq.Logic.ClassicalEpsilon.
Require Export Coqlib own SRF sProp invariants.

(* TODO : move these to separate files *)
Local Notation univ_id := positive.
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
Local Definition inv_interp_aux `{α : SRFCons.t, Γ : HRA, !subG Γ Σ, !invG Σ Γ} n (s : inv_shape) :
    (inv_degree s (SRFSyn.t_prev n) → SRFSyn.t n) → (inv_degree s (SRFSyn.t_prev n) → iProp Σ)
    → iProp Σ :=
  match s with
  | _ownI u i => λ syn _, ownI u n i (syn 0%fin)
  | _ownI_auth u keys => λ syn _, ownI_auth u n (map_imap (λ k v, Some (syn k)) keys)
  | _wsat_auth u => λ _ _, wsat_auth u n
  end.

Global Instance inv_interp `{α : SRFCons.t, Γ : HRA, !subG Γ Σ, !invG Σ Γ} :
    @SRFIntpM.t (@domain Σ) α _ :=
  inv_interp_aux.

Section syn_inv.
  Context `{Γ : HRA} `{!subG Γ Σ} `{!CtxST.t τ} `{!SRFIntp.inG SL.syntax α SL.t β}.
  Context `{!invG Σ Γ, !SRFIntp.inG _ α inv_interp β}.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.
  (* Local Existing Instances inv_preΣ inv_preΓ invG_I invG_E invG_D. *)

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
  (* wsat_auth u (S n) ∗ ownE u E ∗ ownD_auth u ∗ [∗ list] n ∈ (seq 0 (S n)), wsat u n. *)
  Local Fixpoint syn_wsats_aux u n : SRFSyn.t n :=
    match n with
    | O => emp%SRF
    | S n' => syn_wsat u n' ∗ ⤉ syn_wsats_aux u n'
    end.
  Local Definition syn_wsats u n (E : coPset) : SRFSyn.t n :=
    syn_wsat_auth u n ∗ syn_ownE u n E ∗ syn_ownD_auth u n ∗ syn_wsats_aux u n.

  (* Interface for the user *)
  Local Definition syn_inv_def (u : univ_id) (n : level) (N : namespace) p :=
    (∃ i : τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ syn_ownI u n i p)%SRF.
  Local Definition syn_inv_aux : seal (@syn_inv_def). Proof. by eexists. Qed.
  Definition syn_inv := syn_inv_aux.(unseal).
  Local Definition syn_inv_eq : @syn_inv = @syn_inv_def := syn_inv_aux.(seal_eq).

  Local Definition syn_fupd_def u b (E1 E2 : coPset) (P : SRFSyn.t b) : SRFSyn.t b :=
    syn_wsats u b E1 ==∗ (syn_wsats u b E2 ∗ P).
  Local Definition syn_fupd_aux : seal (@syn_fupd_def). Proof. by eexists. Qed.
  Definition syn_fupd := syn_fupd_aux.(unseal).
  Local Definition syn_fupd_eq : @syn_fupd = @syn_fupd_def := syn_fupd_aux.(seal_eq).
End syn_inv.

Class sinvG (Σ : GRA) (Γ : HRA) α β τ := {
  #[global] sinv_subG :: subG Γ Σ;
  #[global] sinv_typG :: CtxST.t τ;
  #[global] sinv_SL_intpG :: SRFIntp.inG SL.syntax α SL.t β;
  #[global] sinv_invG :: invG Σ Γ;
  #[global] sinv_inv_intpG :: SRFIntp.inG inv_syntax α inv_interp β;
  (* sinv_dom := domain Σ *)
}.

Section reduction.
  Context `{!sinvG Σ Γ α β τ}.
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

  Lemma wsats_aux_red u n : ⟦syn_wsats_aux u n⟧ ≡ ([∗ list] n ∈ (seq 0 n), wsat u n)%I.
  Proof.
    induction n.
    { SRF_red; SL_red; ss. }
    { simpl syn_wsats_aux. rewrite seq_S big_sepL_app; ss. SRF_red; ss.
      rewrite wsat_red; SRF_red; rewrite IHn; iSplit; iIntros "[$ H]"; iFrame.
      iDestruct "H" as "[??]"; iFrame.
    }
  Qed.
  
  Lemma wsats_red u n E : ⟦syn_wsats u n E⟧ ≡ wsats u n E.
  Proof.
    rewrite /syn_wsats /syn_ownE /syn_ownD_auth. SRF_red. SL_red.
    rewrite wsats_aux_red; SRF_red; ss; rewrite /wsats /ownD_auth.
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
    rewrite SLRed.wand SLRed.upd wsats_red. SRF_red; ss.
    rewrite wsats_red; done.
  Qed.
End reduction.

Ltac inv_red :=
  repeat (
    try rewrite ! inv_red;
    try rewrite ! fupd_red
  ).

Module inv_instances.
  Instance τ : Typ.t := λ _, ST.t.

  Instance typG : CtxST.t τ.
  Proof. econs. econs. instantiate (1:=0); ss. Qed.

  Instance α {Γ : HRA} : SRFCons.t :=
    λ n,
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.

  Instance β {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Σ Γ} : SRFIntp.t :=
    λ n,
      match n with
      | 0 => SL.t
      | _ => inv_interp
      end.

  Instance intpG {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Σ Γ} :
    SRFIntp.inG (@SL.syntax τ Γ) α (@SL.t τ α Γ Σ _) β.
  Proof. econs; instantiate (1:=0); ss. Qed.

  Instance invintpG {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Σ Γ} :
    SRFIntp.inG inv_syntax α inv_interp β.
  Proof. econs; instantiate (1:=1); ss. Qed.

  Instance sinvg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Σ Γ} : sinvG Σ Γ α β τ.
  Proof. econs; try typeclasses eauto. Qed.
End inv_instances.

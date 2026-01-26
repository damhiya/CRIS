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

(* Module for constructing concrete structures for stratified propositions and global RAs *)
Module inv_instances.

  (* τ and related instances *)
  #[export] Instance τ : TypG.t :=
    λ i,
      match i with
      | _ => ST.t
      end.

  #[export] Instance typG : STτ.t τ.
  Proof using. econs. econs. instantiate (1:=0); ss. Qed.

  (* α and related instances *)
  #[export] Instance α {Γ : HRA} : GAT.t :=
    fun i => match i with
          | 0 => SPropBi.syntax
          | 1 => SPropBiPlainly.syntax
          | 2 => SPropBiBUpd.syntax
          | 3 => @SPropiProp.syntax Γ
          | _ => inv_syntax
          end.

  #[export] Instance SPropBi_in_α `{Γ : HRA} : GAT.inG SPropBi.syntax α.
  Proof. exists 0. ss. Defined.

  #[export] Instance SPropBiPlainly_in_α `{Γ : HRA} : GAT.inG SPropBiPlainly.syntax α.
  Proof. exists 1. ss. Defined.

  #[export] Instance SPropBiBUpd_in_α `{Γ : HRA} : GAT.inG SPropBiBUpd.syntax α.
  Proof. exists 2. ss. Defined.

  #[export] Instance SPropiProp_in_α `{Γ : HRA} : GAT.inG SPropiProp.syntax α.
  Proof. exists 3. ss. Defined.

  #[export] Instance inv_in_α `{Γ : HRA} : GAT.inG inv_syntax α.
  Proof. exists 4. ss. Defined.

  #[export] Instance β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α} : @GATIntp.t (iPropI Σ) α :=
    fun i => match i with
          | 0 => @SPropBi.interp τ α (iPropI Σ)
          | 1 => @SPropBiPlainly.interp α (iPropI Σ) _
          | 2 => @SPropBiBUpd.interp α (iPropI Σ) _
          | 3 => @SPropiProp.interp α Γ Σ _
          | _ => @inv_interp Γ Σ α _ _
          end.

  #[export] Instance SPropBi_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α}
    : GATIntp.inG
        SPropBi.syntax
        α
        (@SPropBi.interp τ α (iPropI Σ))
        β.
  Proof. econs. ss. Qed.

  #[export] Instance SPropBiPlainly_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α}
    : GATIntp.inG
        SPropBiPlainly.syntax
        α
        (@SPropBiPlainly.interp α (iPropI Σ) _)
        β.
  Proof. econs. ss. Qed.

  #[export] Instance SPropBiBUpd_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α}
    : GATIntp.inG
        SPropBiBUpd.syntax
        α
        (@SPropBiBUpd.interp α (iPropI Σ) _)
        β.
  Proof. econs. ss. Qed.

  #[export] Instance SPropiProp_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α}
    : GATIntp.inG
        SPropiProp.syntax
        α
        (@SPropiProp.interp α Γ Σ _)
        β.
  Proof. econs. ss. Qed.

  #[export] Instance inv_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invG Γ Σ α}
    : GATIntp.inG
        inv_syntax
        α
        (@inv_interp Γ Σ α _ _)
        β.
  Proof. econs. ss. Qed.

  (* crisG *)
  #[export] Instance crisg {Σ : GRA} {Γ : HRA} `{!subG Γ Σ, !invG Γ Σ α} : crisG Γ Σ α β τ _ _.
  Proof using.
    econs.
    - typeclasses eauto.
    - econs; econs; typeclasses eauto.
    - econs. typeclasses eauto.
  Defined.

End inv_instances.

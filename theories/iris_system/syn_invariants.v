From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op coPset.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth excl excl_auth functions frac agree gmap big_op.
Require Export Coqlib own SAT sProp invariants.

Local Notation level := nat.

Module SInv.
  Section syntax.

    Variant ops : Type :=
    | _ownI (i : positive)
    | _ownI_reserve (X : coPset)
    | _ownD (i : positive)
    | _wsat_auth (X : coPset)
    .

    Definition arity (op : ops) (sProp : Type) : Type :=
      match op with
      | _ownI i => fin 1
      | _ownI_reserve X => fin 0
      | _ownD i => fin 1
      | _wsat_auth X => fin 0
      end.

    Global Instance syntax : SAT.t := {
      ops := ops;
      arity := arity;
    }.

  End syntax.

  Section semantics.

    Definition interp_aux `{!invGS Γ Σ α, !subHG Γ Σ} n (op : ops) :
        (arity op (GTerm.t_prev n) → GTerm.t n) →
        (arity op (GTerm.t_prev n) → iProp Σ) →
        iProp Σ :=
      match op with
      | _ownI i => λ syn _, ownI i (syn 0%fin)
      | _ownI_reserve X => λ _ _, ownI_reserve n X
      | _ownD i => λ syn _, ownD i (syn 0%fin)
      | _wsat_auth X => λ _ _, wsat_auth n X
      end.

    Global Instance interp `{!invGS Γ Σ α, !subHG Γ Σ} :
        @SATIntp.t (iPropI Σ) α _ :=
      interp_aux.

  End semantics.

  Class synG (α : GAT.t) :=
    { #[local] synG_inG :: GAT.inG syntax α
    }.

  Class semG (α : GAT.t) `{!synG α} (Γ : HRA) (Σ : GRA) `{!invGS Γ Σ α, !subHG Γ Σ} (β : GATIntp.t) :=
    { #[local] semG_inG :: GATIntp.inG syntax α interp β
    }.

  Section definitions.
    Context `{!synG α}.

    Definition syn_ownI {n} i (p : GTerm.t n) : GTerm.t n :=
      ⟨ _ownI i, λ _, p ⟩.
    Definition syn_ownI_reserve {n} X : GTerm.t n :=
      ⟨ _ownI_reserve X, λ e, match e with end⟩.
    Definition syn_ownD {n} i (p : GTerm.t n) : GTerm.t n :=
      ⟨ _ownD i, λ _, p ⟩.
    Definition syn_wsat_auth n X : GTerm.t n :=
      ⟨ _wsat_auth X, λ e, match e with end ⟩.

  End definitions.

  Section reduction.
    Context `{!synG α, !invGS Γ Σ α, !subHG Γ Σ, !semG α Γ Σ β}.

    #[export] Instance ownI_red n i (p : GTerm.t n) :
      SLRed n (syn_ownI i p) (ownI i p).
    Proof. solve_sl_red. Qed.
    #[export] Instance ownI_reserve_red {n} X :
      SLRed n (syn_ownI_reserve X) (ownI_reserve n X).
    Proof. solve_sl_red. Qed.
    #[export] Instance ownD_red {n} i (p : GTerm.t n) :
      SLRed n (syn_ownD i p) (ownD i p).
    Proof. solve_sl_red. Qed.
    #[export] Instance wsat_auth_red {n} X :
      SLRed n (syn_wsat_auth n X) (wsat_auth n X).
    Proof. solve_sl_red. Qed.

  End reduction.

End SInv.

Section derived.
  Context `{!invGS Γ Σ α, !subHG Γ Σ, !STτ.t τ, !SL.synG Γ τ α, !SL.semG Γ τ α Σ β, !SInv.synG α, !SInv.semG α Γ Σ β}.
  Local Existing Instances invG invGpreS_I invGpreS_E.

  Definition syn_ownE {n} (E : coPset) : GTerm.t n :=
    sown enabled_name (CoPset E).

  Definition syn_inv_satall {n} (I : gmap positive (GTerm.t n)) : GTerm.t n :=
    [∗ map] i ↦ p ∈ I, SInv.syn_ownI i p ∗ ((p ∗ SInv.syn_ownD i p) ∨ syn_ownE {[i]}).

  Definition syn_wsat n X : GTerm.t (S n) :=
    ∃ I : τ{ST.gmapT Φ}%SAT, let dom := gset_to_coPset (dom I) in
      ⌜dom ⊆ X⌝ ∗ (⤉ syn_inv_satall I) ∗ (⤉ SInv.syn_ownI_reserve (X ∖ dom)).

  Fixpoint syn_wsatl n X : GTerm.t n :=
    match n with
    | O => emp
    | S n' => ⤉ syn_wsatl n' X ∗ syn_wsat n' X
    end.

  Definition syn_wsats n (E : coPset) : GTerm.t n :=
    SInv.syn_wsat_auth n E ∗ syn_wsatl n E.

  (* Interface for the user *)
  Definition syn_inv {n : level} (N : namespace) (p : GTerm.t n) : GTerm.t n :=
    ∃ i : τ{⇣positive}%SAT, ⌜i ∈ (↑N : coPset)⌝ ∧ SInv.syn_ownI i p.

  Definition syn_fupd {n} (Ew E1 E2 : coPset) (P : GTerm.t n) : GTerm.t n :=
    syn_wsatl n Ew ∗ syn_ownE E1 o==∗
      (syn_wsatl n Ew ∗ syn_ownE E2∗ P).

End derived.

Module Cris.

  Class synG (Γ : HRA) (τ : TypG.t) (α : GAT.t) :=
    { #[global] synG_STτ :: STτ.t τ
    ; #[global] synG_SL :: SL.synG Γ τ α
    ; #[global] synG_SInv :: SInv.synG α
    }.

  Class semG (Γ : HRA) (τ : TypG.t) (α : GAT.t) `{!synG Γ τ α} (Σ : GRA) (β : GATIntp.t) `(_S : !subG Γ Σ) `(_I : !invGS Γ Σ α) :=
    { #[global] semG_SL :: SL.semG Γ τ α Σ β
    ; #[global] semG_SInv :: SInv.semG α Γ Σ β
    }.

End Cris.

Class crisG (Γ : HRA) (Σ : GRA) (α : GAT.t) (β : GATIntp.t) (τ : TypG.t) (_S : subG Γ Σ) (_I : invGS Γ Σ α) :=
  { #[global] cris_synG :: Cris.synG Γ τ α
  ; #[global] cris_semG :: Cris.semG Γ τ α Σ β _S _I
  }.

Section reduction.

  Context `{!crisG Γ Σ α β τ _S _I}.
  Import SInv.

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
          | _ => SInv.syntax
          end.

  Local Instance SPropBi_in_α `{Γ : HRA} : GAT.inG SPropBi.syntax α.
  Proof. exists 0. ss. Defined.

  Local Instance SPropBiPlainly_in_α `{Γ : HRA} : GAT.inG SPropBiPlainly.syntax α.
  Proof. exists 1. ss. Defined.

  Local Instance SPropBiBUpd_in_α `{Γ : HRA} : GAT.inG SPropBiBUpd.syntax α.
  Proof. exists 2. ss. Defined.

  Local Instance SPropiProp_in_α `{Γ : HRA} : GAT.inG SPropiProp.syntax α.
  Proof. exists 3. ss. Defined.

  Local Instance SInv_in_α `{Γ : HRA} : GAT.inG SInv.syntax α.
  Proof. exists 4. ss. Defined.

  Local Instance β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α} : @GATIntp.t (iPropI Σ) α :=
    fun i => match i with
          | 0 => @SPropBi.interp τ α (iPropI Σ)
          | 1 => @SPropBiPlainly.interp α (iPropI Σ) _
          | 2 => @SPropBiBUpd.interp α (iPropI Σ) _
          | 3 => @SPropiProp.interp α Γ Σ _
          | _ => @SInv.interp Γ Σ α _ _
          end.

  Local Instance SPropBi_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α}
    : GATIntp.inG
        SPropBi.syntax
        α
        (@SPropBi.interp τ α (iPropI Σ))
        β.
  Proof. econs. ss. Qed.

  Local Instance SPropBiPlainly_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α}
    : GATIntp.inG
        SPropBiPlainly.syntax
        α
        (@SPropBiPlainly.interp α (iPropI Σ) _)
        β.
  Proof. econs. ss. Qed.

  Local Instance SPropBiBUpd_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α}
    : GATIntp.inG
        SPropBiBUpd.syntax
        α
        (@SPropBiBUpd.interp α (iPropI Σ) _)
        β.
  Proof. econs. ss. Qed.

  Local Instance SPropiProp_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α}
    : GATIntp.inG
        SPropiProp.syntax
        α
        (@SPropiProp.interp α Γ Σ _)
        β.
  Proof. econs. ss. Qed.

  Local Instance SInv_in_β {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α}
    : GATIntp.inG
        SInv.syntax
        α
        (@SInv.interp Γ Σ α _ _)
        β.
  Proof. econs. ss. Qed.

  (* crisG *)
  Local Instance Cris_synG {Γ} : Cris.synG Γ τ α.
  Proof.
    econs.
    - typeclasses eauto.
    - econs; econs; typeclasses eauto.
    - econs; typeclasses eauto.
  Defined.

  Local Instance Cris_semG {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α} : Cris.semG Γ τ α Σ β _ _.
  Proof.
    econs.
    - econs; econs; typeclasses eauto.
    - econs; typeclasses eauto.
  Defined.

  Local Instance Cris_G {Γ : HRA} {Σ : GRA} `{!subG Γ Σ, !invGS Γ Σ α} : crisG Γ Σ α β τ _ _.
  Proof.
    econs. typeclasses eauto.
  Defined.

  Lemma winv_alloc `{!invGpreS Γ Σ α, !subG Γ Σ} :
    ⊢ o=> ∃ (Hinv : invGS Γ Σ α) τ (β : @GATIntp.t (iProp Σ) α) (_ : @crisG Γ Σ α β τ _ Hinv),
      winv (⊤, ⊤).
  Proof.
  iMod (own_admin_alloc) as "$".
  iMod (own_alloc (CoPset ⊤)) as "[%γe E]"; first done.
  iMod (own_alloc ((λ _, allocs.allocs_auth _ (const True)) : ownIRA)) as "[%γi I]"; first done.
  pose (Build_invGS _ γe γi) as Hinv.
  iModIntro; iExists _, τ, β, Cris_G. iSplitL "E".
  { rewrite /ownE //. }
  iExists 0; rewrite /wsats /wsatl /= right_id /wsat_auth /invariant_name //.
  Qed.
End inv_instances.
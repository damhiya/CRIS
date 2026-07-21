From stdpp Require Import coPset namespaces.
From iris.bi.lib Require Import fixpoint_mono.
From iris.proofmode Require Import coq_tactics proofmode reduction.
From iris.prelude Require Import options.
From CRIS.common Require Import Common ConcRA.

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context `{!crisG Γ Σ α β τ Hsub Hinv} {X_pub_s X_pub_t : Type}.
  Implicit Types
    (n : nat) (* stratification index *)
    (Ew Eo Ei : coPset) (* outer/inner masks *)
    (αP_s : X_pub_s → iProp Σ) (αP_t : X_pub_t → iProp Σ) (* atomic pre-condition *)
    (P : iProp Σ) (* abortion condition *)
    (αQ_t : X_pub_t → Any.t → iProp Σ) (αQ_s : X_pub_s → Any.t → iProp Σ) (* atomic post-condition *)
    (Q : X_pub_s → X_pub_t → Any.t → Any.t → iProp Σ) (* post-condition *)
  .

  (** atomic_acc as the "introduction form" of atomic updates: An accessor
    that can be aborted back to [P]. *)
  Definition atomic_acc n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q : iProp Σ :=
    =|n, Ew|={Eo, Ei}=>
      ∀ (x_s : X_pub_s), αP_s x_s o==∗ ∃ (x_t : X_pub_t), αP_t x_t ∗
        ((αP_t x_t =|n, Ew|={Ei, Eo}=∗ αP_s x_s ∗ P) ∧
         (∀ ret_t, αQ_t x_t ret_t o==∗ ∃ ret_s, αQ_s x_s ret_s ∗
          =|n, Ew|={Ei, Eo}=> Q x_s x_t ret_s ret_t)).

  Lemma atomic_acc_wand n Ew Eo Ei αP_s αP_t P1 P2 αQ_t αQ_s Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀ x_s x_t ret_s ret_t, Φ1 x_s x_t ret_s ret_t -∗ Φ2 x_s x_t ret_s ret_t)) -∗
    (atomic_acc n Ew Eo Ei αP_s αP_t P1 αQ_t αQ_s Φ1 -∗
      atomic_acc n Ew Eo Ei αP_s αP_t P2 αQ_t αQ_s Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as "AS"; iIntros "!> %x_s Hα".
    iMod ("AS" with "Hα") as "[%x_t [Hα Hclose]]"; iFrame "Hα".
    iModIntro. iSplit.
    - iIntros "Hα". iMod ("Hclose" with "Hα") as "[$ Hclose]".
      iApply "HP12". iApply "Hclose".
    - iIntros (y) "Hβ". iMod ("Hclose" with "Hβ") as "[% [$ Hclose]]".
      iApply "HP12". done.
  Qed.

  Lemma atomic_acc_mask n Ew Eo Ed αP_s αP_t P αQ_t αQ_s Q :
    atomic_acc n Ew Eo (Eo∖Ed) αP_s αP_t P αQ_t αQ_s Q ⊣⊢
      ∀ E, ⌜Eo ⊆ E⌝ → atomic_acc n Ew E (E∖Ed) αP_s αP_t P αQ_t αQ_s Q.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep !> Hclose' %x_s Hα". iMod ("Hstep" with "Hα") as (x) "[Hα Hclose]".
    iExists x. iFrame. iModIntro. iSplitWith "Hclose".
    - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod ("Hclose" with "Hβ") as "[% [$ ?]]". iApply "Hclose'". done.
  Qed.

  Lemma atomic_acc_mask_weaken n Ew Eo1 Eo2 Ei αP_s αP_t P αQ_t αQ_s Q :
    Eo1 ⊆ Eo2 →
    atomic_acc n Ew Eo1 Ei αP_s αP_t P αQ_t αQ_s Q -∗ atomic_acc n Ew Eo2 Ei αP_s αP_t P αQ_t αQ_s Q.
  Proof.
    iIntros (HE) "Hstep".
    iMod (fupd_mask_subseteq Eo1) as "Hclose1"; first done.
    iMod "Hstep". iIntros "!> %x_s Hα"; iMod ("Hstep" with "Hα") as "[%x_t [Hα Hclose2]]".
    iIntros "!>". iExists x_t.
    iFrame. iSplitWith "Hclose2".
    - iIntros "Hα". iMod ("Hclose2" with "Hα") as "$". done.
    - iIntros (y) "Hβ". iMod ("Hclose2" with "Hβ") as "[% [$ Hclose]]".
      iModIntro. iMod "Hclose". iFrame.
  Qed.

  (** atomic_update as a fixed-point of the equation
   AU = atomic_acc n α AU β Q
  *)
  Context n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q.

  Definition atomic_update_pre (Ψ : () → iProp Σ) (_ : ()) : iProp Σ :=
    atomic_acc n Ew Eo Ei αP_s αP_t (Ψ ()) αQ_t αQ_s Q.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
      iApply (atomic_acc_wand with "[HP12] AU").
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Local Definition atomic_update_def :=
    bi_greatest_fixpoint atomic_update_pre ().
End definition.

(** Seal it *)
Local Definition atomic_update_aux : seal (@atomic_update_def).
Proof. by eexists. Qed.
Definition atomic_update := atomic_update_aux.(unseal).
Global Arguments atomic_update {Γ Σ α _ Hsub Hinv X_pub_s X_pub_t}.
Local Definition atomic_update_unseal :
  @atomic_update = _ := atomic_update_aux.(seal_eq).

Global Arguments atomic_acc {Γ Σ α _ Hsub Hinv X_pub_s X_pub_t} n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q : simpl never.
Global Arguments atomic_update {Γ Σ α _ Hsub Hinv X_pub_s X_pub_t} n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q : simpl never.

(** Notation: Atomic updates *)
(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'AU' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 (λ x_t ret_t, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s x_t ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, αQ_s, Q at level 200, x_s binder, x_t binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 (λ x_t ret_t, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s x_t _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, Q at level 200, x_s binder, x_t binder, ret_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 (λ x_t _, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s x_t ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, αQ_s, Q at level 200, x_s binder, x_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 (λ x_t _, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s x_t _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, Q at level 200, x_s binder, x_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 (λ _ ret_t, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s _ ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, αQ_s, Q at level 200, x_s binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 (λ _ ret_t, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s _ _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, Q at level 200, x_s binder, ret_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 (λ _ _, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s _ ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, αQ_s, Q at level 200, x_s binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∀∀ x_s , αP_s , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 (λ _ _, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s _ _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, αQ_t, Q at level 200, x_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 (λ x_t ret_t, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ x_t ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, αQ_s, Q at level 200, x_t binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 (λ x_t ret_t, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ x_t _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, Q at level 200, x_t binder, ret_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 (λ x_t _, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ x_t ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, αQ_s, Q at level 200, x_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' ∃∃ x_t , αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 (λ x_t _, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ x_t _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, Q at level 200, x_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 (λ _ ret_t, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ _ ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, αQ_s, Q at level 200, ret_t binder, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' αP_t '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 (λ _ ret_t, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ _ _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, Q at level 200, ret_t binder,
   format "'[hv   ' 'AU'  '<{'  '[' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 (λ _ _, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ _ ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, αQ_s, Q at level 200, ret_s binder,
   format "'[hv   ' 'AU'  '<{'  '[' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AU' '<{' αP_t '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_update n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 (λ _ _, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ _ _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, αQ_t, Q at level 200,
   format "'[hv   ' 'AU'  '<{'  '[' αP_t ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'AACC' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t ret_t, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s x_t ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, αQ_s, Q at level 200, x_s binder, x_t binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t ret_t, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s x_t s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, Q at level 200, x_s binder, x_t binder, ret_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t _, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s x_t ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, αQ_s, Q at level 200, x_s binder, x_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t _, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s x_t _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, Q at level 200, x_s binder, x_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ ret_t, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s _ ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, αQ_s, Q at level 200, x_s binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ ret_t, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, Q at level 200, x_s binder, ret_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ _, αQ_t%I)
                 (λ x_s ret_s, αQ_s%I)
                 (λ x_s _ ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, αQ_s, Q at level 200, x_s binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∀∀ x_s , αP_s , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ x_s, αP_s%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ _, αQ_t%I)
                 (λ x_s _, emp%I)
                 (λ x_s _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_s, αP_t, P, αQ_t, Q at level 200, x_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∀∀  x_s ,  '/' αP_s ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t ret_t, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ x_t ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, αQ_s, Q at level 200, x_t binder, ret_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t ret_t, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ x_t ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, Q at level 200, x_t binder, ret_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t _, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ x_t ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, αQ_s, Q at level 200, x_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' ∃∃ x_t , αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ x_t, αP_t%I)
                 P%I
                 (λ x_t _, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ x_t _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, Q at level 200, x_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' ∃∃  x_t ,  '/' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ ret_t, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ _ ret_s ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, αQ_s, Q at level 200, ret_t binder, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' ∀∀ ret_t , αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ ret_t, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ _ ret_t, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, Q at level 200, ret_t binder,
   format "'[hv   ' 'AACC'  '<{'  '[' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  ret_t ,  '/' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , ∃∃ ret_s , αQ_s , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ _, αQ_t%I)
                 (λ _ ret_s, αQ_s%I)
                 (λ _ _ ret_s _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, αQ_s, Q at level 200, ret_s binder,
   format "'[hv   ' 'AACC'  '<{'  '[' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  ∃∃  ret_s ,  '/' αQ_s ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.
 
Notation "'AACC' '<{' αP_t , 'ABORT' P '}>' @ n , Ew , Eo , Ei '<{' αQ_t , 'COMM' Q '}>'" :=
  (atomic_acc n Ew Eo Ei
                 (λ (_ : ()), emp%I)
                 (λ _, αP_t%I)
                 P%I
                 (λ _ _, αQ_t%I)
                 (λ _ _, emp%I)
                 (λ _ _ _, Q%I)
  )
  (at level 20, n, Ew, Eo, Ei, αP_t, P, αQ_t, Q at level 200,
   format "'[hv   ' 'AACC'  '<{'  '[' αP_t ,  '/' ABORT  P  ']'  '}>'  '/' @  '[' n ,  '/' Ew ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' αQ_t ,  '/' COMM  Q ']'  '}>' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  Context `{!crisG Γ Σ α β τ Hsub Hinv} {X_pub_s X_pub_t : Type}.
  Implicit Types
    (αP_s : X_pub_s → iProp Σ)
    (αP_t : X_pub_t → iProp Σ)
    (αQ_t : X_pub_t → Any.t → iProp Σ)
    (αQ_s : X_pub_s → Any.t → iProp Σ)
    (P : iProp Σ)
    .

  Local Existing Instance atomic_update_pre_mono.

  Lemma atomic_update_mask_weaken n Ew Eo1 Eo2 Ei αP_s αP_t αQ_t αQ_s Q :
    Eo1 ⊆ Eo2 →
    atomic_update n Ew Eo1 Ei αP_s αP_t αQ_t αQ_s Q -∗ atomic_update n Ew Eo2 Ei αP_s αP_t αQ_t αQ_s Q.
  Proof.
    rewrite atomic_update_unseal {2}/atomic_update_def /=.
    iIntros (Heo) "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, atomic_update_def n Ew Eo1 Ei αP_s αP_t αQ_t αQ_s Q)); last done.
    iIntros "!> *". rewrite {1}/atomic_update_def /= greatest_fixpoint_unfold.
    iApply atomic_acc_mask_weaken. done.
  Qed.

  Local Lemma aupd_unfold n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q :
    atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q ⊣⊢
    atomic_acc n Ew Eo Ei αP_s αP_t (atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q) αQ_t αQ_s Q.
  Proof.
    rewrite atomic_update_unseal /atomic_update_def /=. apply: greatest_fixpoint_unfold.
  Qed.

  (** The elimination form: an atomic accessor *)
  Lemma aupd_aacc n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q :
    atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q ⊢
    atomic_acc n Ew Eo Ei αP_s αP_t (atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q) αQ_t αQ_s Q.
  Proof. by rewrite {1}aupd_unfold. Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_mod_aupd n φ Ew Eo Ei E αP_s αP_t αQ_t αQ_s Q (Q1 Q2 : iProp Σ) :
    (∀ R, ElimModal φ false false (=|n, Ew|={E,Ei}=> R) R Q1 Q2) →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q)
              (∀ x_s, αP_s x_s o==∗ ∃ x_t, αP_t x_t ∗
                (αP_t x_t =|n, Ew|={Ei,E}=∗ αP_s x_s ∗ atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q) ∧
                (∀ ret_t, αQ_t x_t ret_t o==∗ ∃ ret_s, αQ_s x_s ret_s ∗
                  =|n, Ew|={Ei,E}=> Q x_s x_t ret_s ret_t))
              Q1 Q2.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (aupd_aacc with "AU") as "AC".
    iMod (atomic_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  (** The introduction lemma for atomic_update. This should usually not be used
  directly; use the [iAuIntro] tactic instead. *)
  Local Lemma aupd_intro n P P2 αP_s αP_t αQ_t αQ_s Ew Eo Ei Q :
    Absorbing P → Persistent P →
    (P ∧ P2 ⊢ atomic_acc n Ew Eo Ei αP_s αP_t P2 αQ_t αQ_s Q) →
    P ∧ P2 ⊢ atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q.
  Proof.
    rewrite atomic_update_unseal {1}/atomic_update_def /=.
    iIntros (?? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coiter _ (λ _, P2)); last done. iIntros "!>" ([]) "HQ".
    iApply HAU. iSplit; by iFrame.
  Qed.

  Lemma aacc_intro n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q :
    Ei ⊆ Eo → ⊢ ((∀ x_s, αP_s x_s o==∗ (∃ x_t, αP_t x_t ∗
      ((αP_t x_t =|n, Ew|={Eo}=∗ αP_s x_s ∗ P) ∧
       (∀ ret_t, αQ_t x_t ret_t o==∗ ∃ ret_s, αQ_s x_s ret_s ∗
        =|n, Ew|={Eo}=> Q x_s x_t ret_s ret_t)))) -∗
    atomic_acc n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q).
  Proof.
    iIntros (?) "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose' %x_s Hα".
    iMod ("H" with "Hα") as "[%x_t [Hα Hclose]]".
    iExists x_t. iFrame. iModIntro. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod ("Hclose" with "Hβ") as "[% [$ Hclose]]".
      iModIntro. iMod "Hclose'" as "_". iApply "Hclose".
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic accessor. *)
  Global Instance elim_acc_aacc {X} n Ew E1 E2 Ei (αP' αQ' : X → iProp Σ) γ' αP_s αP_t αQ_t αQ_s Pas Q :
    ElimAcc (X:=X) True (fupd_ex n Ew E1 E2) (fupd_ex n Ew E2 E1) αP' αQ' γ'
            (atomic_acc n Ew E1 Ei αP_s αP_t Pas αQ_t αQ_s Q)
            (λ x', atomic_acc n Ew E2 Ei αP_s αP_t (αQ' x' ∗ (γ' x' -∗? Pas))%I αQ_t αQ_s
                (λ x_s x_t ret_s ret_t, αQ' x' ∗ (γ' x' -∗? Q x_s x_t ret_s ret_t))
            )%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as "Hinner".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose''".
    iIntros (x_s) "Hα"; iMod ("Hinner" with "Hα") as (x_t) "[Hα Hclose']".
    iExists x_t. iFrame. iModIntro. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[$ [Hβ' HPas]]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros (y) "Hβ".
      iMod ("Hclose'" with "Hβ") as "[% [$ Hβ']]".
      iModIntro. iMod "Hclose''" as "_". iMod ("Hβ'") as "Hβ'".
      iDestruct "Hβ'" as "[Hβ HΦ]".
      iMod ("Hclose" with "Hβ") as "Hγ'".
      iModIntro. iFrame. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  accessors can eliminate as well.  This is a forwarding instance needed because
  atomic_acc is becoming opaque. *)
  Global Instance elim_modal_acc p q φ P P' n Ew Eo Ei αP_s αP_t Pas αQ_t αQ_s Q :
    (∀ QQ, ElimModal φ p q P P' (=|n, Ew|={Eo,Ei}=> QQ) (=|n, Ew|={Eo,Ei}=> QQ)) →
    ElimModal φ p q P P'
              (atomic_acc n Ew Eo Ei αP_s αP_t Pas αQ_t αQ_s Q)
              (atomic_acc n Ew Eo Ei αP_s αP_t Pas αQ_t αQ_s Q).
  Proof. intros Helim. apply Helim. Qed.

  (* Note on the aacc_aupd_* lemmas in iris: since the AU construct we define here
  already accounts for semantic atomic updates occuring at both sides, we do not need them here *)
End lemmas.

(** ProofMode support for atomic updates. *)
Section proof_mode.
  Context `{!crisG Γ Σ α β τ Hsub Hinv} {X_pub_s X_pub_t : Type}.
  Implicit Types
    (αP_s : X_pub_s → iProp Σ)
    (αP_t : X_pub_t → iProp Σ)
    (αQ_t : X_pub_t → Any.t → iProp Σ)
    (αQ_s : X_pub_s → Any.t → iProp Σ)
    (P : iProp Σ)
    .

  Lemma tac_aupd_intro Γp Γs i αP_s αP_t αQ_t αQ_s n Ew Eo Ei Q P :
    P = env_to_prop Γs →
    envs_entails (Envs Γp Γs i) (atomic_acc n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q) →
    envs_entails (Envs Γp Γs i) (atomic_update n Ew Eo Ei αP_s αP_t αQ_t αQ_s Q).
  Proof.
    intros ->. rewrite envs_entails_unseal of_envs_eq /atomic_acc /=.
    setoid_rewrite env_to_prop_sound =>HAU.
    rewrite assoc. apply: aupd_intro. by rewrite -assoc.
  Qed.
End proof_mode.

(** * Now the coq-level tactics *)

Tactic Notation "iAuIntro" :=
  match goal with
  | |- environments.envs_entails (environments.Envs ?Γp ?Γs _) (atomic_update ?n ?Ew ?Eo ?Ei ?αP_s ?αP_t ?αQ_t ?αQ_s ?Q) =>
      notypeclasses refine (tac_aupd_intro Γp Γs _ _ _ _ _ _ _ _ _ Q _ _ _); [
        (* P = ...: make the P pretty *) pm_reflexivity
      | (* the new proof mode goal *) ]
  end.

(** Tactic to apply [aacc_intro]. This only really works well when you have
[α ?] already and pass it as [iAaccIntro with "Hα"]. Doing
[rewrite /atomic_acc /=] is an entirely legitimate alternative. *)
Tactic Notation "iAaccIntro" constr(pat) "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |- environments.envs_entails _ (@atomic_acc _ _ _ _ _ _ _ _ ?n ?Ew ?Eo ?Ei ?αP_s ?αP_t ?P ?αQ_t ?αQ_s ?Q) =>
      iApply (@aacc_intro _ _ _ _ _ _ _ _ n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q);
    first try solve_ndisj; last (iIntros pat; iFrame sel)
  | _ => fail "iAAccIntro: Goal is not an atomic accessor"
  end.

Tactic Notation "iAaccIntro" "with" constr(sel) := iAaccIntro "_ _ !>" with sel.

(* From here on, prevent TC search from implicitly unfolding these. *)
Global Typeclasses Opaque atomic_acc atomic_update.

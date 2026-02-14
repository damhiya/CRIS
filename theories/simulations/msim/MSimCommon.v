Require Import Common Mod.

Variant contextuality : Type := 
| open 
| closed.

Notation ist_type Σ := (gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
Notation retr_type Σ Rs Rt :=
  (gmap key (option Any.t) * Rs → gmap key (option Any.t) * Rt → iProp Σ).
Notation msim_type Σ Rs Rt :=
  (bool → bool →
  gmap key (option Any.t) * itree crisE Rs → gmap key (option Any.t) * itree crisE Rt → Σ → Prop).

Section Ist.
  Context {Σ : GRA}.

  Definition IstProd (IstL IstR : ist_type Σ) : ist_type Σ :=
    λ (st_src st_tgt : gmap key (option Any.t)),
      (∃ st_srcL st_tgtL st_srcR st_tgtR,
        ⌜st_src = union_with uwnd st_srcL st_srcR ∧
         st_tgt = union_with uwnd st_tgtL st_tgtR⌝ ∗
        IstL st_srcL st_tgtL ∗ IstR st_srcR st_tgtR)%I.

  Definition IstSB (scopes : list string) (Ist : ist_type Σ) : ist_type Σ :=
    λ st_src st_tgt,
      (⌜(set_map fst (dom st_src)) ⊆@{gset string} list_to_set scopes ∧
        (set_map fst (dom st_tgt)) ⊆@{gset string} list_to_set scopes⌝ ∗
      Ist st_src st_tgt)%I.

  Definition IstEq : ist_type Σ := (λ st_src st_tgt, ⌜st_src = st_tgt⌝)%I.

  Definition IstTrue : ist_type Σ := λ _ _, True%I.

  Definition IstFalse : ist_type Σ := λ _ _, False%I.

  Definition ist_with_eq (Ist : ist_type Σ) {R} :=
    λ '(st_src, v_src) '(st_tgt, v_tgt), (⌜v_src = (v_tgt: R)⌝ ∗ Ist st_src st_tgt)%I.
End Ist.

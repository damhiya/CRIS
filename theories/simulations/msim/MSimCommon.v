Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import Mod.

Variant contextuality : Type := 
| open 
| closed.

Notation ist_type Σ := (nat → alist key Any.t → alist key Any.t → iProp Σ).
Notation retr_type Σ Rs Rt := (nat → alist key Any.t * Rs → alist key Any.t * Rt → iProp Σ).
Notation msim_type Σ Rs Rt := (bool → bool → nat → alist key Any.t * itree crisE Rs → alist key Any.t * itree crisE Rt → Σ → Prop).

Section IST.

  Context `{Σ: GRA}.

  Definition Ist_monotone (Ist: ist_type Σ) : Prop :=
    ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
      Ist nths st_src st_tgt ⊢ Ist nths' st_src st_tgt.

  Definition IstProd (IstL IstR : ist_type Σ) :=
  fun nths (st_src st_tgt : alist key Any.t) =>
    (∃ st_srcL st_tgtL st_srcR st_tgtR,
     ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
     IstL nths st_srcL st_tgtL ∗ IstR nths st_srcR st_tgtR)%I.

  Definition IstSB scopes (Ist : ist_type Σ) :=
    fun nths st_src st_tgt =>
      (⌜incl (Mod.state_scopes st_src) scopes ∧
         incl (Mod.state_scopes st_tgt) scopes⌝
           ∗ Ist nths st_src st_tgt)%I.

  Definition IstEq : ist_type Σ :=
    (fun _ st_src st_tgt => ⌜st_src = st_tgt⌝)%I.

  Definition IstTrue : ist_type Σ
    := λ _ _ _, True%I.

  Definition IstFalse : ist_type Σ
    := λ _ _ _, False%I.

  Definition ist_with_eq (Ist : ist_type Σ) {R} :=
    fun nths '(st_src, v_src) '(st_tgt, v_tgt) =>
      (⌜v_src = (v_tgt: R)⌝ ∗ Ist nths st_src st_tgt)%I.

End IST.

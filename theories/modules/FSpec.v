Require Import Common.

Set Implicit Arguments.
  
Section FSPEC.
  Context {Σ : GRA}.

  Record fspec : Type := mk_fspec {
    meta : Type;
    (*** meta-variable → virtual arg → physical arg → iProp ***)
    precond : meta → Any.t → Any.t → iProp Σ; 
    (*** meta-variable → virtual ret → physical ret → iProp ***)
    postcond : meta → Any.t → Any.t → iProp Σ; 
  }.

  Record fspecbody : Type := mk_specbody {
    fsb_fspec :> fspec;
    fsb_body : Any.t → itree hmodE Any.t;
  }.

  Definition fspec_trivial : fspec :=
    mk_fspec (meta:=unit)
             (λ _ argh argl, (⌜argh = argl⌝)%I)
             (λ _ reth retl, (⌜reth = retl⌝)%I).

  Definition fbody_trivial : Any.t → itree hmodE Any.t :=
    λ _, trigger (Choose _).

  Definition fspec_virtual (M VA VR : Type)
      (precond: M → VA → Any.t → iProp Σ)
      (postcond: M → VR → Any.t → iProp Σ) :=
    mk_fspec (meta:=M)
      (λ x varg arg, (∃ va: VA, ⌜varg = va↑⌝ ∗ precond x va arg)%I)
      (λ x vret ret, (∃ vr: VR, ⌜vret = vr↑⌝ ∗ postcond x vr ret)%I).

  Definition fspec_simple {X : Type} (DPQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    mk_fspec (λ x y a, (((fst ∘ DPQ) x a) ∗ ⌜y = a⌝)%I)
             (λ x z a, (((snd ∘ DPQ) x a) ∗ ⌜z = a⌝)%I).

  Definition fspec_false : fspec := {|
    meta := Empty_set;
    precond := λ _ _ _, False%I;
    postcond := λ _ _ _, False%I; 
  |}.
  
  Definition app_fspec (fspecs : list fspec) : fspec := {|
    meta := { i : nat & (nth i fspecs fspec_false).(meta) };
    precond := λ '(existT i meta_i), (nth i fspecs fspec_false).(precond) meta_i;
    postcond := λ '(existT i meta_i), (nth i fspecs fspec_false).(postcond) meta_i 
  |}.

End FSPEC.

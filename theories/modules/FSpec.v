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
             (λ _ varg arg, (⌜varg = arg⌝)%I)
             (λ _ vret ret, (⌜vret = ret⌝)%I).

  Definition fbody_trivial : Any.t → itree hmodE Any.t :=
    λ _, trigger (Choose _).

  Definition fbody_ub : Any.t → itree hmodE Any.t :=
    λ _, triggerUB.

  Definition fbody_nb : Any.t → itree hmodE Any.t :=
    λ _, triggerNB.

  Definition fspec_virtual (M VA VR : Type)
      (precond: M → VA → Any.t → iProp Σ)
      (postcond: M → VR → Any.t → iProp Σ) :=
    mk_fspec (meta:=M)
      (λ x varg arg, (∃ va: VA, ⌜varg = va↑⌝ ∗ precond x va arg)%I)
      (λ x vret ret, (∃ vr: VR, ⌜vret = vr↑⌝ ∗ postcond x vr ret)%I).

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

  Record fspecS : Type := mk_fspecS {
    metaS : Type;
    precondS : metaS → Any.t → iProp Σ; 
    postcondS : metaS → Any.t → iProp Σ; 
  }.

  Definition make_fspecS {X} (DPQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspecS :=
    mk_fspecS (fun x => (DPQ x).1) (fun x => (DPQ x).2).

  Definition fspecS_false : fspecS := {|
    metaS := Empty_set;
    precondS := λ _ _, False%I;
    postcondS := λ _ _, False%I; 
  |}.
  
  Definition app_fspecS (fspecs : list fspecS) : fspecS := {|
    metaS := { i : nat & (nth i fspecs fspecS_false).(metaS) };
    precondS := λ '(existT i meta_i), (nth i fspecs fspecS_false).(precondS) meta_i;
    postcondS := λ '(existT i meta_i), (nth i fspecs fspecS_false).(postcondS) meta_i 
  |}.

  Definition fspec_proph (fsp: fspecS) (body: Any.t → itree hmodE Any.t) (arg: Any.t) : itree hmodE Any.t :=
    let Pre := λ x, fsp.(precondS) x arg in
    let Post := fsp.(postcondS) in
    Q <- AssumeProph Pre Post;;
    ret <- body arg;;
    trigger (Guarantee (Q ret));;;
    Ret ret.

  Definition to_fspec (fsp: fspecS) : fspec :=
    mk_fspec (λ x varg arg, (fsp.(precondS) x arg ∗ ⌜varg = arg⌝)%I)
             (λ x vret ret, (fsp.(postcondS) x ret ∗ ⌜vret = ret⌝)%I).
  
  Definition fspec_simple {X} (DPQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    to_fspec (make_fspecS DPQ).

End FSPEC.

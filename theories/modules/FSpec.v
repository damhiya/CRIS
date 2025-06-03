Require Import Common.
From iris.proofmode Require Import proofmode.

Set Implicit Arguments.

Section FSPEC.
  Context {Σ : GRA}.

  Record _fspec : Type := _mk_fspec {
    _meta : Type;
    (*** meta-variable → virtual arg → physical arg → iProp ***)
    _precond : _meta → Any.t → Any.t → iProp Σ; 
    (*** meta-variable → virtual ret → physical ret → iProp ***)
    _postcond : _meta → Any.t → Any.t → iProp Σ; 
  }.

  Definition fspec := option _fspec.

  Definition _fspec_trivial: _fspec :=
    @_mk_fspec unit (λ _ varg arg, ⌜varg = arg⌝%I)
                    (λ _ vret ret, ⌜vret = ret⌝%I).

  Definition meta (fsp: fspec) : Type :=
    _meta (or_else fsp _fspec_trivial).

  Definition precond (fsp: fspec) : meta fsp → Any.t → Any.t → iProp Σ :=
    _precond (or_else fsp _fspec_trivial).

  Definition postcond (fsp: fspec) : meta fsp → Any.t → Any.t → iProp Σ :=
    _postcond (or_else fsp _fspec_trivial).

  Definition mk_fspec {meta : Type} (P Q: meta → Any.t → Any.t → iProp Σ) :=
    Some (_mk_fspec P Q).

  Definition fbody : Type := (Any.t → itree hmodE Any.t).
  
  Definition fspecbody : Type := (fspec * fbody)%type.

  Definition fspec_none : fspec := None.

  Definition fspec_trivial : fspec := Some (_fspec_trivial).
  
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

  Definition fspec_false : fspec :=
    mk_fspec (λ (_:void) _ _, False%I) (λ _ _ _, False%I).

  Definition app_fspec (fspecs : list fspec) : fspec :=
    @mk_fspec { i : nat & meta (nth i fspecs fspec_false) }
      (λ '(existT i meta_i), precond (nth i fspecs fspec_false) meta_i)
      (λ '(existT i meta_i), postcond (nth i fspecs fspec_false) meta_i).

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

  Definition fspec_proph (fsp: fspecS) (body: fbody) : fbody :=
    fun arg =>
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

  (** fspec_weaker fsp0 fsp1 means that [fsp0] is weaker spec than [fsp1]
      For the notion of a weaker spec, consider the consequence rule of Hoare triple:
        if P0 ⊢ P1 and Q1 ⊢ Q0 and { P1 } e { Q1 }
        then { P0 } e { Q0 }
      Therefore (P0, Q0) is weaker than (P1, Q1) if P0 ⊢ P1 and Q1 ⊢ Q0 *)
  Definition fspec_weaker (fsp0 fsp1: fspec): Prop :=
    match fsp0, fsp1 with
    | None, None => True
    | Some _fsp0, Some _fsp1 => 
      forall x0,
      exists x1,
      (<<PRE: forall varg arg,
          (_precond _fsp0 x0 varg arg) ⊢ |==> (_precond _fsp1 x1 varg arg)>>) ∧
      (<<POST: forall vret ret,
          (_postcond _fsp1 x1 vret ret) ⊢ |==> (_postcond _fsp0 x0 vret ret)>>)
    | _, _ => False    
    end.

  Global Program Instance fspec_weaker_PreOrder : PreOrder fspec_weaker.
  Next Obligation.
  Proof using.
    ii. destruct x; ss. i. exists x0. esplits; ii.
    { iStartProof. iIntros "H". iApply "H". }
    { iStartProof. iIntros "H". iApply "H". }
  Qed.
  Next Obligation.
  Proof using.
    ii. destruct x,y,z; ss. i.
    hexploit (H x0). i. des.
    hexploit (H0 x1). i. des. esplits; ii.
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply PRE0.
      iApply bupd_idemp. iApply PRE. iApply "H". }
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply POST.
      iApply bupd_idemp. iApply POST0. iApply "H". }
  Qed.
  
End FSPEC.

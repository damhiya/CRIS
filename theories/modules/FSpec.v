Require Import Common.
From iris.proofmode Require Import proofmode.

Set Implicit Arguments.

Section FSPEC.
  Context {Σ : GRA}.

  Record fspec : Type := mk_fspec {
    meta : Type;
    (* meta-variable → virtual arg → physical arg → iProp *)
    precond : meta → Any.t → Any.t → iProp Σ;
    (* meta-variable → virtual ret → physical ret → iProp *)
    postcond : meta → Any.t → Any.t → iProp Σ;
  }.

  Definition fbody : Type := Any.t → itree crisE Any.t.

  Definition fspecbody : Type := fspec * fbody.

  Definition fspec_trivial : fspec :=
    @mk_fspec unit (λ _ varg arg, ⌜varg = arg⌝%I)
                   (λ _ vret ret, ⌜vret = ret⌝%I).

  Definition fspec_bot : fspec :=
    @mk_fspec unit (λ _ varg arg, True%I)
                   (λ _ vret ret, False%I).

  Definition fspec_top : fspec :=
    @mk_fspec False (λ _ varg arg, False%I)
                    (λ _ vret ret, True%I).

  Definition fspec_flat (fspo : option fspec) : fspec :=
    or_else fspo fspec_trivial.

  Definition fbody_trivial : Any.t → itree crisE Any.t :=
    λ _, trigger (Choose _).

  Definition fbody_ub : Any.t → itree crisE Any.t :=
    λ _, triggerUB.

  Definition fbody_nb : Any.t → itree crisE Any.t :=
    λ _, triggerNB.

  Definition fspec_virtual
      {M VA VR : Type}
      (DPQ: M → (VA → Any.t → iProp Σ) * (VR → Any.t → iProp Σ)) :=
    mk_fspec (meta:=M)
      (λ x varg arg, (∃ va: VA, ⌜varg = va↑⌝ ∗ (DPQ x).1 va arg)%I)
      (λ x vret ret, (∃ vr: VR, ⌜vret = vr↑⌝ ∗ (DPQ x).2 vr ret)%I).

  Definition app_fspec (fspecs : list fspec) : fspec :=
    @mk_fspec { i : nat & meta (nth i fspecs fspec_top) }
      (λ '(existT i meta_i), precond (nth i fspecs fspec_top) meta_i)
      (λ '(existT i meta_i), postcond (nth i fspecs fspec_top) meta_i).

  Record fspecS : Type := mk_fspecS {
    metaS : Type;
    precondS : metaS → Any.t → iProp Σ;
    postcondS : metaS → Any.t → iProp Σ;
  }.

  Definition make_fspecS {X} (DPQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspecS :=
    mk_fspecS (λ x, (DPQ x).1) (λ x, (DPQ x).2).

  Definition fspecS_bot : fspecS := {|
    metaS := unit;
    precondS := λ _ _, False%I;
    postcondS := λ _ _, True%I;
  |}.

  Definition app_fspecS (fspecs : list fspecS) : fspecS := {|
    metaS := { i : nat & (nth i fspecs fspecS_bot).(metaS) };
    precondS := λ '(existT i meta_i), (nth i fspecs fspecS_bot).(precondS) meta_i;
    postcondS := λ '(existT i meta_i), (nth i fspecs fspecS_bot).(postcondS) meta_i
  |}.

  Definition img_lat (peeking: bool) (fsp : fspecS) (lbody: itree crisE ()) (body: fbody) : fbody :=
    λ arg,
    ITree.iter (λ _,
      lbody;;;
      x <- trigger (Take (metaS fsp));;
      trigger (Assume (precondS fsp x arg));;;
      'b: bool <- trigger (Choose bool);;
      if peeking && b
      then trigger (Guarantee (precondS fsp x arg));;; Ret (inl ())
      else ret <- body arg;;
           trigger (Guarantee (postcondS fsp x ret));;; Ret (inr ret)
      ) ().

  Definition to_fspec (fsp : fspecS) : fspec :=
    mk_fspec (λ x varg arg, (fsp.(precondS) x arg ∗ ⌜varg = arg⌝)%I)
             (λ x vret ret, (fsp.(postcondS) x ret ∗ ⌜vret = ret⌝)%I).

  Definition from_fspec (fsp : fspec) : fspecS :=
    mk_fspecS (λ x arg, (fsp.(precond) x arg arg)%I)
              (λ x ret, (fsp.(postcond) x ret ret)%I).

  Definition fspec_simple {X} (DPQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    to_fspec (make_fspecS DPQ).

  (** fspec_imply fsp0 fsp1 means that [fsp0] is stronger spec than [fsp1]
      For the notion of a stronger spec, consider the consequence rule of Hoare triple:
        if P1 ⊢ P0 and Q0 ⊢ Q1 and { P0 } e { Q0 } then { P1 } e { Q1 }
      Therefore (P0, Q0) is stronger than (P1, Q1) if P1 ⊢ P0 and Q0 ⊢ Q1 *)
  Definition fspec_imply (fsp0 fsp1 : fspec) : Prop :=
    forall x1,
    exists x0,
      (<<PRE: forall varg arg,
          (precond fsp1 x1 varg arg) ⊢ |==> (precond fsp0 x0 varg arg)>>) ∧
      (<<POST: forall vret ret,
          (postcond fsp0 x0 vret ret) ⊢ |==> (postcond fsp1 x1 vret ret)>>).

  Global Program Instance fspec_imply_PreOrder : PreOrder fspec_imply.
  Next Obligation.
  Proof using.
    ii. exists x1. esplits; ii; et.
  Qed.
  Next Obligation.
  Proof using.
    ii. hexploit (H0 x1). i. des. hexploit (H x0). i. des. exists x2.
    esplits; ii.
    - rewrite PRE PRE0. iIntros ">> H". et.
    - rewrite POST0 POST. iIntros ">> H". et.
  Qed.

  Lemma fspec_bot_strongest fsp :
    fspec_imply fspec_bot fsp.
  Proof.
    ii. exists (). s. esplits; et. i. iIntros "%". ss.
  Qed.

  Lemma fspec_top_weakest fsp :
    fspec_imply fsp fspec_top.
  Proof.
    ii. ss.
  Qed.
End FSPEC.

Section FSPEC_WINV.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition fspec_winv (E : coPset) (fsp : fspec) : fspec :=
    mk_fspec (meta := fsp.(meta))
      (λ x varg arg, winv (E, E) ∗ fsp.(precond) x varg arg)%I
      (λ x vret ret, winv (E, E) ∗ fsp.(postcond) x vret ret)%I.

  Definition icond_winv (E : coPset) (I : iProp Σ) : iProp Σ :=
    winv (E, E) ∗ I.
End FSPEC_WINV.

Global Arguments precond : simpl never.
Global Arguments postcond : simpl never.
Global Arguments precondS : simpl never.
Global Arguments postcondS : simpl never.


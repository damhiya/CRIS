Require Import Common.
From iris.proofmode Require Import proofmode.

Set Implicit Arguments.

Section FSPEC.
  Context {Σ : GRA}.

  Definition fspec_rel :=
    (Any.t → Any.t → iProp Σ) → (Any.t → Any.t → iProp Σ) → Prop.

  Record fspec : Type := mk_fspec {
    meta : Type;
    (* meta-variable → virtual arg → physical arg → iProp *)
    precond : meta → Any.t → Any.t → iProp Σ;
    (* meta-variable → virtual ret → physical ret → iProp *)
    postcond : meta → Any.t → Any.t → iProp Σ;
  }.

  Record FSpec (fsp: fspec_rel) : Type := mk_FSpec {
    Precond: Any.t → Any.t → iProp Σ;
    Postcond: Any.t → Any.t → iProp Σ;
    related: fsp Precond Postcond;
  }.

  Definition idx_to_rel {I A B} fP fQ := λ (P: A) (Q: B), ∃ x: I, P = fP x ∧ Q = fQ x.

  Definition fspec_to_rel: fspec → fspec_rel :=
    λ fsp, idx_to_rel fsp.(precond) fsp.(postcond).

  Definition fsp_none : option fspec_rel := None.

  Definition fsp_some (fsp: fspec_rel) : option fspec_rel := Some fsp.

  Coercion fspec_to_rel: fspec >-> fspec_rel.

  Lemma fspec_to_rel_satisfy (fsp: fspec) x:
    fspec_to_rel fsp (fsp.(precond) x) (fsp.(postcond) x).
  Proof. eexists. et. Qed.

  Definition fbody : Type := Any.t → itree crisE Any.t.

  Definition fspec_trivial : fspec :=
    @mk_fspec unit (λ _ varg arg, ⌜varg = arg⌝%I)
                   (λ _ vret ret, ⌜vret = ret⌝%I).

  Definition fspec_bot : fspec :=
    @mk_fspec unit (λ _ varg arg, True%I)
                   (λ _ vret ret, False%I).

  Definition fspec_top : fspec :=
    @mk_fspec False (λ _ varg arg, False%I)
                    (λ _ vret ret, True%I).

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

  Definition to_fspec (fsp : fspecS) : fspec :=
    mk_fspec (λ x varg arg, (fsp.(precondS) x arg ∗ ⌜varg = arg⌝)%I)
             (λ x vret ret, (fsp.(postcondS) x ret ∗ ⌜vret = ret⌝)%I).

  Definition from_fspec (fsp : fspec) : fspecS :=
    mk_fspecS (λ x arg, (fsp.(precond) x arg arg)%I)
              (λ x ret, (fsp.(postcond) x ret ret)%I).
  
  Definition lat_img_body (peeking: bool) (fsp : fspecS) (lbody: itree crisE ()) (body: fbody) (arg: Any.t) :=
    lbody;;;
    x <- trigger (Take (metaS fsp));;
    trigger (Assume (precondS fsp x arg));;;
    let peek := trigger (Guarantee (precondS fsp x arg));;; Ret (inl ()) in
    let update := ret <- body arg;; trigger (Guarantee (postcondS fsp x ret));;; Ret (inr ret) in
    if peeking
    then 'b: bool <- trigger (Choose bool);;
         (if b then peek else update)
    else update.

  Definition lat_img peeking fsp lbody body : fbody :=
    λ arg, ITree.iter (λ _, lat_img_body peeking fsp lbody body arg) ().

  Definition lat_real_body (peeking: bool) (fsp : fspecS) (lbody: itree crisE ()) (body: fbody) (arg: Any.t) :=
    lbody;;;
    let peek := RealUpdate (idx_to_rel (λ x, precondS fsp x arg) (λ x, precondS fsp x arg));;; Ret (inl ()) in
    let update := ret <- body arg;; RealUpdate (idx_to_rel (λ x, precondS fsp x arg) (λ x, postcondS fsp x ret));;; Ret (inr ret) in
    if peeking
    then 'b: bool <- trigger (Choose bool);;
         (if b then peek else update)
    else update.

  Definition lat_real peeking fsp lbody body : fbody :=
    λ arg, ITree.iter (λ _, lat_real_body peeking fsp lbody body arg) ().

  Definition fspec_simple {X} (DPQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    to_fspec (make_fspecS DPQ).


  Definition fspec_flat (fspo : option fspec_rel) : fspec_rel :=
    or_else fspo fspec_trivial.
  
  (** fspec_imply fsp0 fsp1 means that [fsp0] is stronger spec than [fsp1]
      For the notion of a stronger spec, consider the consequence rule of Hoare triple:
        if P1 ⊢ P0 and Q0 ⊢ Q1 and { P0 } e { Q0 } then { P1 } e { Q1 }
      Therefore (P0, Q0) is stronger than (P1, Q1) if P1 ⊢ P0 and Q0 ⊢ Q1 *)
  Definition fspec_imply (fsp0 fsp1 : fspec_rel) : Prop :=
    ∀ P1 Q1 (ValidSP: fsp1 P1 Q1), 
    ∃ P0 Q0, <<ValidSP: fsp0 P0 Q0>> ∧
      (<<PRE: forall varg arg,
          (P1 varg arg) ⊢ |==> (P0 varg arg)>>) ∧
      (<<POST: forall vret ret,
          (Q0 vret ret) ⊢ |==> (Q1 vret ret)>>).    

  Global Program Instance fspec_imply_PreOrder : PreOrder fspec_imply.
  Next Obligation. 
  Proof using.
    ii. exists P1, Q1. esplits; ii; et.
  Qed.
  Next Obligation.
  Proof using.
    ii. hexploit (H0 P1 Q1); et. i. des. hexploit (H P0 Q0); et. i. des. exists P2, Q2.
    esplits; et; ii.
    - rewrite PRE PRE0. iIntros ">> H". et.
    - rewrite POST0 POST. iIntros ">> H". et.
  Qed.  

  Lemma fspec_bot_strongest fsp :
    fspec_imply fspec_bot fsp.
  Proof.
    ii. esplits; i.
    - rr; esplits; et.
    - et.
    - iIntros. ss.
    Unshelve. exact ().
  Qed.

  Lemma fspec_top_weakest fsp :
    fspec_imply fsp fspec_top.
  Proof.
    ii. rr in ValidSP. des; ss.
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


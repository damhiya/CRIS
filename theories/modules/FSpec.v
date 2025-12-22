Require Import Common.
From iris.proofmode Require Import proofmode.

(* Function specifications *)
Section fspec.
  Context {Σ : GRA}.

  (** CRIS specification of functions *)
  Record fspec : Type := fspec_mk {
    meta : Type;
    precond : (namespace * nat) → meta → Any.t → Any.t → iProp Σ;
    postcond : (namespace * nat) → meta → Any.t → Any.t → iProp Σ;
  }.
  Arguments fspec_mk {meta} precond postcond.

  Definition fspec_trivial : fspec :=
    @fspec_mk unit
      (λ _ _ varg arg, ⌜varg = arg⌝%I)
      (λ _ _ vret ret, ⌜vret = ret⌝%I).

  Definition fspec_bot : fspec :=
    @fspec_mk unit
      (λ _ _ varg arg, True%I)
      (λ _ _ vret ret, False%I).

  Definition fspec_top : fspec :=
    @fspec_mk False
      (λ _ _ varg arg, False%I)
      (λ _ _ vret ret, True%I).

  Definition fspec_flat (fspo : option fspec) : fspec :=
    or_else fspo fspec_trivial.

  Definition fbody : Type := Any.t → itree crisE Any.t.

  Definition fbody_trivial : Any.t → itree crisE Any.t :=
    λ _, trigger (Choose _).

  Definition fbody_ub : Any.t → itree crisE Any.t :=
    λ _, triggerUB.

  Definition fbody_nb : Any.t → itree crisE Any.t :=
    λ _, triggerNB.

  Definition fspec_simple {X} (PQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    fspec_mk
      (λ A x varg arg, ⌜varg = arg⌝ ∗ (PQ x).1 varg)%I
      (λ A x vret ret, ⌜vret = ret⌝ ∗ (PQ x).1 vret)%I.

  Definition fspec_virtual
      {M VA VR : Type}
      (DPQ : M → (VA → Any.t → iProp Σ) * (VR → Any.t → iProp Σ)) :=
    fspec_mk
      (λ _ x varg arg, (∃ (va : VA), ⌜varg = va↑⌝ ∗ (DPQ x).1 va arg)%I)
      (λ _ x vret ret, (∃ (vr : VR), ⌜vret = vr↑⌝ ∗ (DPQ x).2 vr ret)%I).

  Definition app_fspec (fspecs : list fspec) : fspec :=
    @fspec_mk { i : nat & meta (nth i fspecs fspec_top) }
      (λ A '(existT i meta_i), precond (nth i fspecs fspec_top) A meta_i)
      (λ A '(existT i meta_i), postcond (nth i fspecs fspec_top) A meta_i).

  (* Simple fspecs. Assumes virtual arg = physical arg *)
  (* Record fspecS : Type := mk_fspecS {
    metaS : Type;
    precondS : metaS → Any.t → iProp Σ;
    postcondS : metaS → Any.t → iProp Σ;
  }. *)

  (* Definition make_fspecS {X} (DPQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspecS :=
    mk_fspecS (λ x, (DPQ x).1) (λ x, (DPQ x).2). *)

  (* Definition fspecS_bot : fspecS := {|
    metaS := unit;
    precondS := λ _ _, False%I;
    postcondS := λ _ _, True%I;
  |}. *)

  (* Definition app_fspecS (fspecs : list fspecS) : fspecS := {|
    metaS := { i : nat & (nth i fspecs fspecS_bot).(metaS) };
    precondS := λ '(existT i meta_i), (nth i fspecs fspecS_bot).(precondS) meta_i;
    postcondS := λ '(existT i meta_i), (nth i fspecs fspecS_bot).(postcondS) meta_i
  |}. *)

  (* Takes fspecS, generates inlinable specification *)
  Definition atomic_body
    (fsp : fspec) (body : (namespace * nat) → meta fsp → Any.t → itree crisE Any.t)
    : Any.t → itree crisE Any.t :=
  λ arg,
    x <- trigger (Take ((namespace * nat) * meta fsp));;
    trigger (Assume ((precond fsp) x.1 x.2 arg arg));;;
    ret <- body x.1 x.2 arg;;
    trigger (Guarantee ((postcond fsp) x.1 x.2 ret ret));;;
    Ret ret.

  (* Definition lat_img_body
      (peeking: bool) (fsp : fspecS) (lbody : itree crisE ()) (body : fbody) (arg : Any.t) :=
    lbody;;;
    x <- trigger (Take (metaS fsp));;
    trigger (Assume (precondS fsp x arg));;;
    let peek := trigger (Guarantee (precondS fsp x arg));;; Ret (inl ()) in
    let update := ret <- body arg;; trigger (Guarantee (postcondS fsp x ret));;; Ret (inr ret) in
    if peeking
    then 'b: bool <- trigger (Choose bool);;
         (if b then peek else update)
    else update. *)

  (* Definition lat_img peeking fsp lbody body : fbody :=
    λ arg, ITree.iter (λ _, lat_img_body peeking fsp lbody body arg) (). *)

  (* Definition lat_real_body
      (peeking : bool) (fsp : fspecS) (lbody : itree crisE ()) (body : fbody) (arg : Any.t) :=
    lbody;;;
    let peek := RealUpdate (λ x, precondS fsp x arg) (λ x, precondS fsp x arg);;; Ret (inl ()) in
    let update := ret <- body arg;; RealUpdate (λ x, precondS fsp x arg) (λ x, postcondS fsp x ret);;; Ret (inr ret) in
    if peeking
    then 'b: bool <- trigger (Choose bool);;
         (if b then peek else update)
    else update.

  Definition lat_real peeking fsp lbody body : fbody :=
    λ arg, ITree.iter (λ _, lat_real_body peeking fsp lbody body arg) ().

  Definition to_fspec (fsp : fspecS) : fspec :=
    fspec_call
      (λ x varg arg, (fsp.(precondS) x arg ∗ ⌜varg = arg⌝)%I)
      (λ x vret ret, (fsp.(postcondS) x ret ∗ ⌜vret = ret⌝)%I). *)

  (* Definition from_fspec (fsp : fspec) : fspecS :=
    mk_fspecS (λ x arg, (precond fsp x arg arg)%I)
              (λ x ret, (postcond fsp x ret ret)%I). *)

  (* Definition fspec_simple {X} (DPQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    to_fspec (make_fspecS DPQ). *)

  (** fspec_imply fsp0 fsp1 means that [fsp0] is stronger spec than [fsp1]
      For the notion of a stronger spec, consider the consequence rule of Hoare triple:
        if P1 ⊢ P0 and Q0 ⊢ Q1 and { P0 } e { Q0 } then { P1 } e { Q1 }
      Therefore (P0, Q0) is stronger than (P1, Q1) if P1 ⊢ P0 and Q0 ⊢ Q1 *)
  Definition fspec_imply (fsp0 fsp1 : fspec) : Prop :=
    ∀ Ntid, ∀ x1, ∃ x0,
      (∀ varg arg, (precond fsp1 Ntid x1 varg arg ⊢ |==> precond fsp0 Ntid x0 varg arg)) ∧
      (∀ vret ret, (postcond fsp0 Ntid x0 vret ret ⊢ |==> postcond fsp1 Ntid x1 vret ret)).

  Global Program Instance fspec_imply_PreOrder : PreOrder fspec_imply.
  Next Obligation.
  Proof using. ii; eexists; esplits; ii; et. Qed.
  Next Obligation.
  Proof using.
    intros x y z Hxy Hyz Ntid mz; hexploit (Hyz Ntid mz); intros [my [Hzy Hyz']].
    hexploit (Hxy Ntid my); intros [mx [Hyx Hxy']]; exists mx; split.
    { ii; rewrite Hzy Hyx; iIntros ">>$ //". }
    { ii; rewrite Hxy' Hyz'; iIntros ">>$ //". }
  Qed.

  (* Definition fspec_imply' (fsp0 fsp1 : fspec) : Prop :=
    match fsp0, fsp1 with
    | @fspec_spawn m0 pre0 post0, @fspec_spawn m1 pre1 post1 =>
        ∀ tid x1, ∃ x0,
          (∀ varg arg, (pre1 (tid, x1) varg arg ⊢ |==> pre0 (tid, x0) varg arg)) ∧
            (∀ vret ret, (post0 (tid, x0) vret ret ⊢ |==> post1 (tid, x1) vret ret))
    | @fspec_call m0 pre0 post0, @fspec_call m1 pre1 post1 =>
        fspec_imply fsp0 fsp1
    | _, _ => False
    end. *)

  (* Global Program Instance fspec_imply'_PreOrder : PreOrder fspec_imply'.
  Next Obligation.
  Proof using. ii. destruct x; ss; try refl. i. exists x1. esplits; ii; et. Qed.
  Next Obligation.
  Proof using.
    ii. destruct x, y, z; ss; try by etrans; et. i.
    hexploit (H0 tid x1). intros [? [PRE POST]]. hexploit (H tid x). intros [? [PRE1 POST1]].
    exists x0.
    esplits; ii.
    - rewrite PRE PRE1. iIntros ">> H". et.
    - rewrite POST1 POST. iIntros ">> H". et.
  Qed. *)

  Lemma fspec_bot_strongest fsp : fspec_imply fspec_bot fsp.
  Proof. ii. exists (). s. esplits; et. i. iIntros "%". ss. Qed.

  Lemma fspec_top_weakest fsp : fspec_imply fsp fspec_top.
  Proof. ii; ss. Qed.

  (* Definition is_spawn_ospec (fspo: option fspec) : bool :=
    match fspo with
    | Some (@fspec_spawn _ _ _) => true
    | _ => false
    end. *)
End fspec.

Section fspec_WINV.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition fspec_winv (E : coPset) (fsp : fspec) : fspec :=
    fspec_mk (meta := meta fsp)
      (λ '(NS, tid) x varg arg, winv (E, E) ∗ precond fsp (NS, tid) x varg arg)%I
      (λ '(NS, tid) x vret ret, winv (E, E) ∗ postcond fsp (NS, tid) x vret ret)%I.

  Definition icond_winv (E : coPset) (I : iProp Σ) : iProp Σ :=
    winv (E, E) ∗ I.
End fspec_WINV.

Global Arguments precond : simpl never.
Global Arguments postcond : simpl never.
(* Global Arguments precondS : simpl never.
Global Arguments postcondS : simpl never. *)

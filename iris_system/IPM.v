Require Import Coqlib.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.
Require Import Coq.Init.Decimal.
Require Export IProp.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.

Section IPM.
  Context {Σ: GRA.t}.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp') : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp' := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp') : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp' := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp'.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp' uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c, iProp_intro (fun x => forall n, c n x) _.
  Next Obligation.
    i. ss. i. eapply iProp_mono; eauto.
  Qed.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.

  Lemma iProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ _) (@Ex _) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - econs.
      { uipropall. ii. split; ii; eapply H; et. }
      { uipropall. i. econs. i. des. split; i.
        { eapply H; et. }
        { eapply H1; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H. ss. }
      { uipropall. ii. eapply H. ss. }
    - econs. i. split.
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
    - econs. i. split.
      { uipropall. ii. exploit H; et. i. eapply x3; et. }
      { uipropall. ii. exploit H; et. i. eapply x3; et. }
    - econs. i. split.
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x3; et. }
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x3; et. }
    - econs. i. split.
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
    - econs. uipropall. i. split.
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
    - ii. econs. uipropall. i. split.
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
    - exact Pure_intro.
    - exact Pure_elim.
    - exact And_elim_l.
    - exact And_elim_r.
    - exact And_intro.
    - exact Or_intro_l.
    - exact Or_intro_r.
    - exact Or_elim.
    - exact Impl_intro_r.
    - exact Impl_elim_l.
    - exact Univ_intro.
    - exact Univ_elim.
    - exact Ex_intro.
    - exact Ex_elim.
    - exact Sepconj_mono.
    - exact Emp_Sepconj_l.
    - exact Emp_Sepconj_r.
    - exact Sepconj_comm.
    - exact Sepconj_assoc.
    - exact Wand_intro_r.
    - exact Wand_elim_l.
    - exact Persistently_mono.
    - exact Persistently_idem.
    - exact Persistently_emp.
    - exact Persistently_and2.
    - exact Persistently_ex.
    - exact Persistently_sep.
    - exact Persistently_and.
  Qed.

  Lemma iProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ _) (@Ex _) Sepconj Persistently Later.
  Proof.
    econs.
    - ii. uipropall. rr. split. ii. ss. apply H. auto.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. specialize (H x). uipropall.
    - ii. uipropall. ii. right. des. exists x. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. right. ss.
  Qed.

  Canonical Structure iProp: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  Definition OwnM (M: URA.t) `{@GRA.inG M Σ} (r: M): iProp := Own (GRA.embed r).

  (** extra BI instances *)
  Lemma iProp_bupd_mixin: BiBUpdMixin iProp Upd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. des. esplits; et. eapply H; et. eapply URA.wf_mon; et. eapply H2. rewrite URA.unit_id. et. }
      { ii. des. esplits; et. eapply H; et. eapply URA.wf_mon; et. eapply H2. rewrite URA.unit_id. et. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_absorbing (P: iProp): Absorbing P.
  Proof.
    rr. uipropall. i. rr in H. uipropall. des. eapply iProp_mono; eauto.
    exists a. rewrite H. r_solve.
  Qed.

  Global Instance iProp_affine (P: iProp): Affine P.
  Proof.
    rr. uipropall. i. rr. uipropall.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. specialize (H a). rr in H. uipropall.
  Qed.

  Global Instance iProp_bi_affine : BiAffine (iProp) | 0.
  Proof. exact iProp_affine. Qed.

  Global Instance iProp_bi_persistently_forall : BiPersistentlyForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. rr. uipropall. i. specialize (H x). rr in H. uipropall.
  Qed.
  
End IPM.
Global Hint Immediate iProp_bi_affine : core.
Arguments OwnM: simpl never.

Section TEST.
  Context {Σ: GRA.t}.

  Goal forall (P Q R: iProp) (PQ: P -∗ Q) (QR: Q -∗ R), P -∗ R.
  Proof.
    i. iStartProof. iIntros "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q: iProp), ((bupd P) ∗ Q) -∗ (bupd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.
End TEST.

Infix "⊢" := (@bi_entails iProp) (only parsing).
Infix "**" := bi_sep (at level 99, only parsing).
Infix "-*" := bi_wand (at level 99, right associativity, only parsing).
Notation "#=> P" := ((@bupd (bi_car (@iProp _)) (@bi_bupd_bupd (@iProp _) (@iProp_bi_bupd _))) P) (at level 99, only parsing).

Section IUPD.
  Context {Σ: GRA.t}.

  Variable P: iProp.

  Check (P ⊢ P).
  Check (P ** P).
  Check (#=> P).

  Definition IUpd (I: iProp): iProp -> iProp :=
    fun P => (I -∗ #=> (I ∗ P))%I.

  Lemma IUpd_intro I: forall P, P ⊢ IUpd I P.
  Proof.
    ii. iIntros "H INV". iModIntro. iFrame.
  Qed.

  Lemma IUpd_mono I: forall P Q, (P ⊢ Q) -> (IUpd I P ⊢ IUpd I Q).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]". iModIntro.
    iFrame. iApply H. auto.
  Qed.

  Lemma IUpd_trans I: forall P, (IUpd I (IUpd I P)) ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]".
    iApply "H1". auto.
  Qed.

  Lemma IUpd_frame_r I: forall P R, ((IUpd I P) ∗ R) ⊢ (IUpd I (P ∗ R)).
  Proof.
    ii. unfold IUpd. iIntros "[H0 H1] INV".
    iPoseProof ("H0" with "INV") as "> [H0 H2]".
    iModIntro. iFrame.
  Qed.

  Lemma Upd_IUpd I: forall P, #=> P ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV". iFrame.
  Qed.

  Lemma iProp_bupd_mixin_IUpd I: BiBUpdMixin iProp (IUpd I).
  Proof.
    econs.
    - ii. unfold bupd. unfold IUpd. rewrite H. auto.
    - apply IUpd_intro.
    - apply IUpd_mono.
    - apply IUpd_trans.
    - apply IUpd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd_IUpd I: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin_IUpd I |}.
End IUPD.
Notation "#=( Q )=> P" := ((@bupd (bi_car (@iProp _)) (@bi_bupd_bupd (@iProp _) (@iProp_bi_bupd_IUpd _ Q))) P) (at level 99).
Notation "P =( I ) =∗ Q" := (P ⊢ #=( I )=> Q) (only parsing, at level 99) : stdpp_scope.
Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.





Class IsOp {A : URA.t} (a b1 b2 : A) := is_op : a = b1 ⋅ b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : URA.t} (a b : A) : IsOp (URA.add a b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : URA.t} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : URA.t} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : URA.t} (a b : A) : IsOp'LR (URA.add a b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. inv H. red. uipropall. i. des. subst.
    unfold URA.extends in *. des. subst.
    exists (URA.add ctx0 ctx). repeat rewrite URA.add_assoc.
    f_equal. rewrite URA.add_comm. rewrite URA.add_assoc. f_equal.
    eapply URA.add_comm.
  Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof.
    ii. apply bi.intuitionistically_if_mono. inv H.
    uipropall. i. unfold URA.extends in *. des. subst. split.
    { exists (URA.add b2 ctx). eapply URA.add_assoc. }
    { exists (URA.add b1 ctx). rewrite URA.add_assoc.
      f_equal. eapply URA.add_comm. }
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. red. inv H. uipropall. i.
    unfold URA.extends in *. des. subst.
    exists b1, (URA.add b2 ctx). split.
    { symmetry. eapply URA.add_assoc. }
    esplits.
    { eapply URA.unit_id. }
    { et. }
  Qed.

  Global Instance from_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. unfold OwnM. inv H0.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    rewrite GRA.embed_add. iApply "H".
  Qed.

  Global Instance into_and_ownM (M: URA.t) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. apply bi.intuitionistically_if_mono. inv H0.
    unfold OwnM. rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplit.
    { iApply "H1". }
    { iApply "H2". }
  Qed.

  Global Instance into_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. inv H0. unfold OwnM.
    rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplitL "H1"; iFrame.
  Qed.
End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.

  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. unfold URA.extends in *. des. subst.
    esplits; et. i. eapply (URA.wf_mon (b:=ctx)). r_wf H.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: URA.wf a)
    :
      P a.
  Proof.
    uipropall. eapply SAT; et. refl.
  Qed.

  Lemma OwnM_valid (M: URA.t) `{@GRA.inG M Σ} (m: M):
    OwnM m -∗ ⌜URA.wf m⌝.
  Proof.
    rr. uipropall. i. red. rr. unfold OwnM, Own in *. uipropall.
    unfold URA.extends in *. des. subst.
    eapply URA.wf_mon in WF. eapply GRA.embed_wf. et.
  Qed.

  Lemma Upd_Pure P
    :
      #=> ⌜P⌝ ⊢ ⌜P⌝.
  Proof.
    rr. uipropall. i. rr. uipropall. des. rr in H. uipropall.
  Qed.

  (*** this is deprecated in 1.1 ***)
  (* Lemma Own_Upd_set *)
  (*       (r1: Σ) B *)
  (*       (UPD: URA.updatable_set r1 B) *)
  (*   : *)
  (*     (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (Own b))) *)
  (* . *)
  (* Proof. *)
  (*   cut (Entails (Own r1) (Upd (Ex (fun b => Sepconj (Pure (B b)) (Own b))))); ss. *)
  (*   uipropall. i. red in H. des. subst. *)
  (*   exploit (UPD (ctx0 ⋅ ctx)). *)
  (*   { rewrite URA.add_assoc. et. } *)
  (*   i. des. exists (b ⋅ ctx0). split. *)
  (*   { rewrite <- URA.add_assoc. et. } *)
  (*   { exists b. uipropall. esplits; [|apply IN|refl]. *)
  (*     eapply URA.add_comm. } *)
  (* Qed. *)

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    uipropall. i. exists r2. esplits; et. { refl. } i. eapply UPD. eapply URA.wf_extends; et.
    eapply URA.extends_add; et.
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; et.
  Qed.

  Lemma Own_persistently (r : Σ) : Own r ⊢ <pers> Own (URA.core r).
  Proof.
    uipropall. i. rr; uipropall. apply URA.extends_core. ss.
  Qed.

  Lemma OwnM_persistently {M : URA.t} `{@GRA.inG M Σ} (r : M) : OwnM r ⊢ <pers> OwnM (URA.core r).
  Proof.
    unfold OwnM. rewrite GRA.embed_core. apply Own_persistently.
  Qed.

  Lemma OwnM_unit {M : URA.t} `{@GRA.inG M Σ} : ⊢ OwnM ε.
  Proof.
    Local Transparent GRA.to_URA.
    rr; uipropall. i. rr; uipropall. rr. exists r.
    rewrite GRA.embed_unit. rewrite URA.unit_idl. ss.
  Qed.

  
  (*** this is deprecated in 1.1 ***)
  (* Lemma OwnM_Upd_set (M: URA.t) `{@GRA.inG M Σ} *)
  (*       (r1: M) B *)
  (*       (UPD: URA.updatable_set r1 B) *)
  (*   : *)
  (*     (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (OwnM b))) *)
  (* . *)
  (* Proof. *)
  (*   assert (UPDM: URA.updatable_set *)
  (*                   (GRA.embed r1) *)
  (*                   (fun r => exists m, r = GRA.embed m /\ B m)). *)
  (*   { red. i. red in UPD. *)
  (*     unshelve hexploit UPD. *)
  (*     { eapply (@eq_rect URA.t (Σ (@GRA.inG_id _ _ H)) (@URA.car)). *)
  (*       { eapply (ctx (@GRA.inG_id _ _ H)). } *)
  (*       { symmetry. eapply (@GRA.inG_prf _ _ H). } *)
  (*     } *)
  (*     Local Transparent GRA.to_URA. *)
  (*     { ur in WF. ss. specialize (WF GRA.inG_id). *)
  (*       destruct H. subst. ss. *)
  (*       unfold GRA.embed in WF. ss. *)
  (*       replace (PeanoNat.Nat.eq_dec inG_id inG_id) *)
  (*         with (@left (inG_id = inG_id) (inG_id <> inG_id) eq_refl) in WF; ss. *)
  (*       { des_ifs. repeat f_equal. eapply proof_irrelevance. } *)
  (*     } *)
  (*     i. des. exists (GRA.embed b). esplits; et. *)
  (*     ur. Local Transparent GRA.to_URA. ss. *)
  (*     i. unfold GRA.embed. des_ifs. *)
  (*     { ss. unfold PCM.GRA.cast_ra. destruct  H. subst. ss. } *)
  (*     { ur in WF. specialize (WF k). rewrite URA.unit_idl. *)
  (*       eapply URA.wf_mon. rewrite URA.add_comm. et. *)
  (*     } *)
  (*   } *)
  (*   iIntros "H". *)
  (*   iPoseProof (Own_Upd_set with "H") as "> H". *)
  (*   { eapply UPDM. } *)
  (*   iDestruct "H" as (b) "[% H1]". des. subst. *)
  (*   iModIntro. iExists m. iFrame. ss. *)
  (* Qed. *)

  Lemma OwnM_Upd (M: URA.t) `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: URA.updatable r1 r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    uipropall. i. exists (GRA.embed r2). esplits; et.
    { unfold OwnM in *. uipropall. refl. }
    i. eapply GRA.embed_updatable in UPD. eapply UPD. eapply URA.wf_extends; et. eapply URA.extends_add; et.
    unfold OwnM in H0. uipropall.
  Qed.

  Lemma OwnM_extends (M: URA.t) `{@GRA.inG M Σ}
        (a b: M)
        (EXT: URA.extends a b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    red. unfold OwnM. uipropall. i. unfold URA.extends in *.
    des. subst. rewrite <- GRA.embed_add.
    rewrite <- URA.add_assoc. et.
  Qed.

  Lemma OwnM_combine (M: URA.t) `{@GRA.inG M Σ} (a0 a1: M)
    :
    (OwnM a0 ∗ OwnM a1) -∗ OwnM (a0 ⋅ a1).
  Proof.
    iIntros "[H0 H1]". iCombine "H0 H1" as "H". auto.
  Qed.
  
  Lemma IUpd_unfold I P
    :
    #=(I)=> P ⊢ (I -∗ #=> (I ∗ P)).
  Proof.
    reflexivity.
  Qed.

  Lemma IUpd_fold I P
    :
    (I -∗ #=> (I ∗ P)) ⊢ #=(I)=> P.
  Proof.
    reflexivity.
  Qed.

  Definition SubIProp P Q: iProp :=
    Q -∗ #=> (P ∗ (P -∗ #=> Q)).

  Lemma SubIProp_refl P
    :
    ⊢ SubIProp P P.
  Proof.
    iIntros "H". iFrame. auto.
  Qed.

  Lemma SubIProp_trans P Q R
    :
    (SubIProp P Q)
      -∗
      (SubIProp Q R)
      -∗
      (SubIProp P R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof ("H1" with "H2") as "> [H1 H2]".
    iPoseProof ("H0" with "H1") as "> [H0 H1]".
    iFrame. iModIntro. iIntros "H".
    iPoseProof ("H1" with "H") as "> H".
    iPoseProof ("H2" with "H") as "H". auto.
  Qed.

  Lemma SubIProp_sep_l P Q
    :
    ⊢ (SubIProp P (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma SubIProp_sep_r P Q
    :
    ⊢ (SubIProp Q (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma IUpd_sub_mon P Q R
    :
    (SubIProp P Q)
      -∗
      (#=(P)=> R)
      -∗
      (#=(Q)=> R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof (IUpd_unfold with "H1") as "H1".
    iPoseProof ("H0" with "H2") as "> [H0 H2]".
    iPoseProof ("H1" with "H0") as "> [H0 H1]".
    iPoseProof ("H2" with "H0") as "H0". iFrame. auto.
  Qed.
  
End ILEMMAS.

Global Instance upd_elim_iupd `{GRA.t} I P Q
       `{ElimModal _ True false false (#=(I)=> P) P Q R}
  :
  ElimModal True false false (#=> P) P Q R.
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "> H0". iApply "H1". auto.
Qed.

Global Instance iupd_elim_upd `{GRA.t} I P Q b
  :
  ElimModal True b false (#=> P) P (#=(I)=> Q) (#=(I)=> Q).
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "H0".
  iIntros "H". iPoseProof ("H0" with "H") as "> [H0 H2]".
  destruct b; ss.
  { iPoseProof ("H2") as "# > H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
  { iPoseProof ("H2") as "> H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
Qed.

Global Instance subiprop_elim_upd `{GRA.t} I J P Q b
  :
  ElimModal True b false ((SubIProp I J) ∗ #=(I)=> P) P (#=(J)=> Q) (#=(J)=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (_) "[[SUB P] K] J".
  iMod ("SUB" with "J") as "[I IJ]". iMod ("P" with "I") as "[I P]".
  iMod ("IJ" with "I") as "J". iPoseProof ("K" with "P J") as "K". iFrame.
Qed.

Ltac iOwnWf' H :=
  iPoseProof (OwnM_valid with H) as "%".

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  iOwnWf' H;
  match goal with
  | H0: @URA.wf _ _ |- _ => rename H0 into WF
  end
.

(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.


Section AUX.
  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. spc DISJ. des; rewrite DISJ.
    - rewrite URA.unit_idl; et.
    - rewrite URA.unit_id; et.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

  Lemma lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.
End AUX.


Section OWN.
  Context `{Σ: GRA.t}.
  Lemma own_ctx a b
      (OWN: Own a ⊢ #=> Own b)
    :
      forall ctx, Own (ctx ⋅ a) ⊢ #=> Own (ctx ⋅ b)
  .
  Proof.
    i. iIntros "[H H0]".
    iPoseProof (OWN with "H0") as "H0".
    iSplitL "H"; et.
  Qed.

  Lemma own_wf (r r': Σ)
      (OWN: Own r ⊢ #=> Own r')
      (WF: URA.wf r)
    :
      URA.wf r'
  .
  Proof. 
    uipropall. hexploit OWN; et. { refl. }
    esplits; et. des.
    eapply URA.wf_extends; et.
    specialize (H0 ε). rewrite ! URA.unit_id in H0.
    et.
  Qed.

  (* replace with imod_trans *)
  Lemma own_trans (a b c: Σ) (A: Own a ⊢ #=> Own b) (B: Own b ⊢ #=> Own c): Own a ⊢ #=> Own c.
  Proof.
    iIntros "H". 
    iPoseProof (A with "H") as "H". iMod "H".
    iPoseProof (B with "H") as "H". et.
  Qed.

  Lemma own_mod (r: Σ) P (OWN: Own r ⊢ P): Own r ⊢ #=> P.
  Proof. iIntros "H". iModIntro. iPoseProof (OWN with "H") as "H"; et. Qed.

  Lemma own_pure (P: Prop) (fmr: Σ) (WF: URA.wf fmr) (OWN: Own fmr ⊢ ⌜P⌝) : P.
  Proof.
    uipropall. hexploit OWN; [et|refl|].
    i. rr in H. uipropall.
  Qed.

  Lemma not_wf_sat (r: Σ) (ILL: ¬ URA.wf r) P: Own r ⊢ P.
  Proof.
    rr. uipropall. i.
    eapply URA.wf_extends in WF; et.
    clarify.
  Qed.

  Lemma iProp_sepconj_upd_aux P Q r 
      (SAT: Own r ⊢ #=> (P ∗ Q))
    :
      exists rp rq, (URA.updatable r (rp ⋅ rq)) /\ 
                    (Own rp ⊢ P) /\ 
                    (Own rq ⊢ Q)
  .
  Proof.
    destruct (classic (URA.wf r)); cycle 1.
    {
      exists r, r. esplits; eauto using not_wf_sat.
      rr. i. eapply URA.wf_mon in H0. clarify. 
    }

    uipropall.
    hexploit SAT; et. { r_solve. }
    i. des.
    esplits; et; uipropall.
    {
      instantiate (1:= b). instantiate (1:=a).
      unfold URA.updatable. subst. et. 
    }
    {
      i. destruct P. ss.
      hexploit H4. i.
      eapply URA.wf_extends in H4; et.
    }
    {
      i. destruct Q. ss.
      hexploit H4. i.
      eapply URA.wf_extends in H4; et.
    }
  Qed.

  Lemma iProp_sepconj_upd P Q r 
      (SAT: Own r ⊢ #=> (P ∗ Q))
    :
      exists rp rq, (Own r ⊢ #=> Own (rp ⋅ rq)) /\ 
                    (Own rp ⊢ P) /\ 
                    (Own rq ⊢ Q)
  .
  Proof.
    eapply iProp_sepconj_upd_aux in SAT; et. des.
    eapply Own_Upd in SAT.
    esplits; et. 	
  Qed.	

  Lemma iProp_Own (P: iProp) a (A: P a): Own a ⊢ P. Proof. uiprop. i. eauto using iProp_mono. Qed.
  Lemma Own_iProp (P: iProp) a (OWN: Own a ⊢ P) (WF: URA.wf a) : P a. Proof. uiprop in OWN. eapply OWN; eauto. refl. Qed.
  Lemma iProp_sepconj (P Q: iProp) r (OWN: Own r ⊢ P ∗ Q) (WF: URA.wf r): 
    exists p q, r = p ⋅ q /\ P p /\ Q q.
  Proof.
    uiprop in OWN. edestruct OWN; eauto; try refl.
  Qed.

End OWN.

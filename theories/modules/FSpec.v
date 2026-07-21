From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.

(* Function specifications *)
Record fspec `{Σ : GRA} : Type := fspec_mk {
  meta : Type;
  precond : meta → Any.t → Any.t → iProp Σ;
  postcond : meta → Any.t → Any.t → iProp Σ;
}.
Arguments fspec_mk {Σ meta} precond postcond.

Definition fspec_rel `{Σ : GRA} : Type :=
  (Any.t → Any.t → iProp Σ) → (Any.t → Any.t → iProp Σ) → Prop.

Record FSpec `{Σ : GRA} (fsp : fspec_rel) : Type := FSpec_mk {
  Precond : Any.t → Any.t → iProp Σ;
  Postcond : Any.t → Any.t → iProp Σ;
  related : fsp Precond Postcond;
}.
Arguments FSpec_mk {Σ fsp} Precond Postcond related.
Arguments Precond {Σ fsp} f.
Arguments Postcond {Σ fsp} f.
Arguments related {Σ fsp} f.

Definition idx_to_rel {I A B} fP fQ := λ (P : A) (Q : B), ∃ x: I, P = fP x ∧ Q = fQ x.

Section fspec.
  Context `{Σ : GRA}.

  Definition fspec_to_rel : fspec → fspec_rel :=
    λ fsp, idx_to_rel fsp.(precond) fsp.(postcond).
  #[warning="-uniform-inheritance"]
  Coercion fspec_to_rel : fspec >-> fspec_rel.

  Definition fsp_none : option fspec_rel := None.
  Definition fsp_some (fsp : fspec_rel) : option fspec_rel := Some fsp.

  Lemma fspec_to_rel_satisfy (fsp : fspec) x :
    fspec_to_rel fsp (fsp.(precond) x) (fsp.(postcond) x).
  Proof. by eexists. Qed.

  Definition fspec_trivial : fspec :=
    @fspec_mk _ unit
      (λ _ varg arg, ⌜varg = arg⌝%I)
      (λ _ vret ret, ⌜vret = ret⌝%I).

  Definition fspec_bot : fspec :=
    @fspec_mk _ unit
      (λ _ varg arg, True%I)
      (λ _ vret ret, False%I).

  Definition fspec_top : fspec :=
    @fspec_mk _ False
      (λ _ varg arg, False%I)
      (λ _ vret ret, True%I).

  Definition fbody_trivial : Any.t → itree crisE Any.t :=
    λ _, trigger (Choose _).

  Definition fbody_ub : Any.t → itree crisE Any.t :=
    λ _, triggerUB.

  Definition fbody_nb : Any.t → itree crisE Any.t :=
    λ _, triggerNB.

  Definition fspec_simple {X} (PQ : X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    fspec_mk
      (λ x varg arg, ⌜varg = arg⌝ ∗ (PQ x).1 varg)%I
      (λ x vret ret, ⌜vret = ret⌝ ∗ (PQ x).2 vret)%I.

  Definition fspec_simple_typ {A R} (ft: fntyp_t A R) {X} (PQ : X → (A → iProp Σ) * (R → iProp Σ)) : fspec :=
    fspec_simple (λ x, (λ a, ∃ v, ⌜a = v↑⌝ ∗ (PQ x).1 v,
                        λ r, ∃ v, ⌜r = v↑⌝ ∗ (PQ x).2 v))%I.

  Definition fspec_virtual
      {M VA VR : Type}
      (DPQ : M → (VA → Any.t → iProp Σ) * (VR → Any.t → iProp Σ)) :=
    fspec_mk
      (λ x varg arg, (∃ (va : VA), ⌜varg = va↑⌝ ∗ (DPQ x).1 va arg)%I)
      (λ x vret ret, (∃ (vr : VR), ⌜vret = vr↑⌝ ∗ (DPQ x).2 vr ret)%I).

  Definition fspec_virtual_typ {A R} (ft: fntyp_t A R)
      {M VA VR : Type}
      (DPQ : M → (VA → A → iProp Σ) * (VR → R → iProp Σ)) :=
      fspec_mk
      (λ x varg arg, (∃ (va : VA) pa, ⌜varg = va↑ ∧ arg = pa↑⌝ ∗ (DPQ x).1 va pa)%I)
      (λ x vret ret, (∃ (vr : VR) pr, ⌜vret = vr↑ ∧ ret = pr↑⌝ ∗ (DPQ x).2 vr pr)%I).

  Definition fspec_physical (fsp : fspec) : Prop :=
    (∀ x va a, fsp.(precond) x va a ⊢ ⌜va = a⌝%I) ∧
    (∀ x vr r, fsp.(postcond) x vr r ⊢ ⌜vr = r⌝%I).

  Definition fspec_rel_physical (fsp : fspec_rel) : Prop :=
    ∀ P Q, fsp P Q →
      (∀ varg arg, P varg arg ⊢ ⌜varg = arg⌝) ∧ (∀ vret ret, Q vret ret ⊢ ⌜vret = ret⌝).
      
  Definition fbody `{Σ : GRA} : Type := Any.t → itree crisE Any.t.

  Definition to_physical (fsp : fspec) : fspec :=
    fspec_mk (λ x va a, ⌜va=a⌝ ∗ fsp.(precond) x va a)%I
             (λ x vr r, ⌜vr=r⌝ ∗ fsp.(postcond) x vr r)%I.

  Definition fspec_flat (fspo : option fspec_rel) : fspec_rel :=
    or_else fspo fspec_trivial.
  
  (** fspec_imply fsp0 fsp1 means that [fsp0] is stronger spec than [fsp1]
      For the notion of a stronger spec, consider the consequence rule of Hoare triple:
        if P1 ⊢ P0 and Q0 ⊢ Q1 and { P0 } e { Q0 } then { P1 } e { Q1 }
      Therefore (P0, Q0) is stronger than (P1, Q1) if P1 ⊢ P0 and Q0 ⊢ Q1 *)
  Definition fspec_imply (fsp0 fsp1 : fspec_rel) : iProp Σ :=
    ∀ P1 Q1, ⌜fsp1 P1 Q1⌝ →
      ∀ varg arg, P1 varg arg o==∗
        ∃ P0 Q0, ⌜fsp0 P0 Q0⌝ ∧ P0 varg arg ∗ ∀ vret ret, Q0 vret ret o==∗ Q1 vret ret.

  Lemma fspec_bot_strongest fsp : ⊢ fspec_imply fspec_bot fsp.
  Proof.
    iIntros (P1 Q1) "PQ1 %varg %arg P1"; iExists _, _; iModIntro; iSplit; first (iExists tt; ss).
    iSplit; first done; iIntros (??) "[]".
  Qed.

  Lemma fspec_top_weakest fsp : ⊢ fspec_imply fsp fspec_top.
  Proof. by iIntros (??) "[% %]". Qed.

  Lemma fspec_imply_refl fsp : ⊢ fspec_imply fsp fsp.
  Proof using. iIntros (??) "% % % P"; iExists _, _; iModIntro; iSplit; eauto with iFrame. Qed.

  Definition add_fspec (sp1 sp2: fspec) : fspec := {|
    meta := (meta sp1) + (meta sp2);
    precond := λ m, match m with inl m => precond sp1 m | inr m => precond sp2 m end;
    postcond := λ m, match m with inl m => postcond sp1 m | inr m => postcond sp2 m end
  |}.

End fspec.

Definition fspec_winv `{!crisG Γ Σ α β τ _S _I} (E : coPset) (fsp : fspec) : fspec :=
  fspec_mk
    (λ x varg arg, winv (E, E) ∗ precond fsp x varg arg)%I
    (λ x vret ret, winv (E, E) ∗ postcond fsp x vret ret)%I.

Global Arguments precond : simpl never.
Global Arguments postcond : simpl never.

(****************************
  Notations for spec addtion
 ****************************)

Declare Scope cris_scope.
Delimit Scope cris_scope with cris.

Notation "[ ]" := fspec_top (format "[ ]") : cris_scope.
Notation "[ x ]" := (add_fspec x fspec_top) : cris_scope.
Notation "[ x ; y ; .. ; z ]" := (add_fspec x (add_fspec y .. (add_fspec z fspec_top) ..)) : cris_scope.

Notation "'meta0' x" := (inl x) (at level 1, only parsing) : cris_scope.
Notation "'meta1' x" := (inr (inl x)) (at level 1, only parsing) : cris_scope.
Notation "'meta2' x" := (inr (inr (inl x))) (at level 1, only parsing) : cris_scope.
Notation "'meta3' x" := (inr (inr (inr (inl x)))) (at level 1, only parsing) : cris_scope.
Notation "'meta4' x" := (inr (inr (inr (inr (inl x))))) (at level 1, only parsing) : cris_scope.
Notation "'meta5' x" := (inr (inr (inr (inr (inr (inl x)))))) (at level 1, only parsing) : cris_scope.
Notation "'meta6' x" := (inr (inr (inr (inr (inr (inr (inl x))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta7' x" := (inr (inr (inr (inr (inr (inr (inr (inl x)))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta8' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta9' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta10' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta11' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta12' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta13' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta14' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta15' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta16' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta17' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta18' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))))))))) (at level 1, only parsing) : cris_scope.
Notation "'meta19' x" := (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))))))))))) (at level 1, only parsing) : cris_scope.

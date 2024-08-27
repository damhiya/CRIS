From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Require Import Coqlib PCM IProp IPM.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.IndefiniteDescription.


Lemma dependent_functional_choice (A : Type) (B : A -> Type) :
  forall R : forall x : A, B x -> Prop,
    (forall x : A, exists y : B x, R x y) ->
    (exists f : (forall x : A, B x), forall x : A, R x (f x)).
Proof.
  eapply ChoiceFacts.non_dep_dep_functional_choice.
  clear. exact functional_choice.
Qed.  



Section POINTWISE.

  Lemma unfold_pointwise_add X (M: URA.t) (f0 f1: (X ==> M)%ra)
    :
    f0 ⋅ f1 = (fun x => f0 x ⋅ f1 x).
  Proof.
    ur. ur. auto.
  Qed.

  Lemma updatable_set_impl (M: URA.t)
        (P0 P1: M -> Prop)
        (IMPL: forall r, URA.wf r -> P0 r -> P1 r)
        (m: M)
        (UPD: URA.updatable_set m P0)
    :
    URA.updatable_set m P1.
  Proof.
    ii. eapply UPD in WF; eauto. des.
    esplits; eauto. eapply IMPL; auto.
    eapply URA.wf_mon. eauto.
  Qed.

  Lemma pointwise_extends A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.extends (f0 a) (f1 a))
    :
    URA.extends f0 f1.
  Proof.
    hexploit (choice (fun a ctx => f1 a = ((f0 a) ⋅ ctx))).
    { i. specialize (UPD x). r in UPD. des. eauto. }
    i. des. exists f.
    rewrite (@unfold_pointwise_add A M). extensionality a. auto.
  Qed.

  Lemma pointwise_updatable A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_updatable_set A (M: URA.t)
        (f: (A ==> M)%ra)
        (P: A -> M -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii. hexploit (choice (fun a m => P a m /\ URA.wf (m ⋅ ctx a))).
    { i. eapply (UPD x). ur in WF. auto. }
    i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Definition maps_to_res {A} {M: URA.t}
             a m: (A ==> M)%ra :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else URA.unit.

  Lemma maps_to_res_add A (M: URA.t)
        (a: A) (m0 m1: M)
    :
    maps_to_res a m0 ⋅ maps_to_res a m1
    =
      maps_to_res a (m0 ⋅ m1).
  Proof.
    extensionality a'. unfold maps_to_res. ur. des_ifs.
    { ur. auto. }
    { r_solve. }
  Qed.

  Lemma maps_to_res_updatable A (M: URA.t)
        (a: A) (m0 m1: M)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (maps_to_res a m0) (maps_to_res a m1).
  Proof.
    eapply pointwise_updatable. i.
    unfold maps_to_res. des_ifs.
  Qed.

  Lemma maps_to_res_updatable_set A (M: URA.t)
        (a: A) (m: M) (P: M -> Prop)
        (UPD: URA.updatable_set m P)
    :
    URA.updatable_set
      (maps_to_res a m)
      (fun f => exists (m1: M), f = maps_to_res a m1 /\ P m1).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionality a'. unfold maps_to_res. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Definition map_update {A} {M: URA.t}
             (f: (A ==> M)%ra) a m :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else f a'.

End POINTWISE.

Global Opaque URA.unit.

Section UNIT.

  Program Instance Unit : URA.t := {| URA.unit := tt; URA._add := fun _ _ => tt; URA._wf := fun _ => True; URA.core := fun _ => tt; |}.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". i. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. unseal "ra". i. exists tt. ss. Qed.

  Lemma Unit_wf : forall x, @URA.wf Unit x.
  Proof. unfold URA.wf. unseal "ra". ss. Qed.

End UNIT.
Global Opaque Unit.


Section URA_PROD.

  Lemma unfold_prod_add (M0 M1 : URA.t) : @URA.add (URA.prod M0 M1) = fun '(a0, a1) '(b0, b1) => (a0 ⋅ b0, a1 ⋅ b1).
  Proof. rewrite URA.unfold_add. extensionalities r0 r1. destruct r0, r1. ss. Qed.

  Lemma unfold_prod_wf (M0 M1 : URA.t) : @URA.wf (URA.prod M0 M1) = fun r => URA.wf (fst r) /\ URA.wf (snd r).
  Proof. rewrite URA.unfold_wf. extensionalities r. destruct r. ss. Qed.

End URA_PROD.

Section PWDEP.

  Lemma pointwise_dep_updatable
        A (Ms : A -> URA.t)
        (f0 f1 : @URA.pointwise_dep A Ms)
        (UPD : forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_dep_updatable_set
        A (Ms : A -> URA.t)
        (f : @URA.pointwise_dep A Ms)
        (P : forall (a : A), (Ms a) -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii.
    set (R := fun (a : A) => (fun (m : Ms a) => P a m /\ URA.wf (m ⋅ ctx a))).
    hexploit (dependent_functional_choice _ _ R).
    { subst R. ss. i. eapply (UPD x). ur in WF. auto. }
    subst R. ss. i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Program Definition maps_to_res_dep {A : Type} {Ms : A -> URA.t} (a : A) (m : Ms a)
    : @URA.pointwise_dep A Ms.
  Proof.
    ii. destruct (excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact ε.
  Defined.

  Lemma maps_to_res_dep_eq
        A (Ms : A -> URA.t)
        (a : A)
        (m : Ms a)
    :
    (@maps_to_res_dep A Ms a m) a = m.
  Proof.
    unfold maps_to_res_dep. des_ifs. unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq. auto.
  Qed.

  Lemma maps_to_res_dep_neq
        A (Ms : A -> URA.t)
        (a b : A)
        (m : Ms a)
    :
    a <> b -> (@maps_to_res_dep A Ms a m) b = ε.
  Proof.
    i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_add
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
    :
    @maps_to_res_dep _ Ms a m0 ⋅ @maps_to_res_dep _ Ms a m1 = @maps_to_res_dep _ Ms a (m0 ⋅ m1).
  Proof.
    extensionalities a'. unfold URA.add at 1. unseal "ra". ss.
    destruct (excluded_middle_informative (a' = a)).
    - subst a'. rewrite ! @maps_to_res_dep_eq. auto.
    - rewrite ! @maps_to_res_dep_neq; auto. apply URA.unit_id.
  Qed.

  Lemma maps_to_res_dep_updatable
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (@maps_to_res_dep A Ms a m0) (@maps_to_res_dep A Ms a m1).
  Proof.
    eapply pointwise_dep_updatable. i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_updatable_set
        A (Ms : A -> URA.t)
        (a : A)
        (m : Ms a)
        (P : forall (a' : A), Ms a' -> Prop)
        (UPD: URA.updatable_set m (P a))
    :
    URA.updatable_set
      (@maps_to_res_dep A Ms a m)
      (fun f => exists (m1 : Ms a), f = @maps_to_res_dep A Ms a m1 /\ (P a m1)).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_dep_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P a' m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res_dep in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionalities a'. unfold maps_to_res_dep. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Program Definition maps_to_res_dep_update {A} {Ms: A -> URA.t}
          (f: @URA.pointwise_dep A Ms) a (m : Ms a) : @URA.pointwise_dep A Ms.
  Proof.
    ii. destruct (excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact (f k).
  Qed.

End PWDEP.



Tactic Notation "unfold_prod" :=
  try rewrite ! unfold_prod_add;
  rewrite unfold_prod_wf;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite ! unfold_prod_add in H;
  rewrite unfold_prod_wf in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.

Section PWAUX.

  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; eauto. Qed.

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
    ii; ss. ur. i. ur in WF0. ur in WF1. specialize (DISJ k). des; rewrite DISJ.
    - rewrite URA.unit_idl; eauto.
    - rewrite URA.unit_id; eauto.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, functions.fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

  Lemma pw_lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

End PWAUX.

Section PWDAUX.

  Context {K: Type} `{M: K -> URA.t}.
  Let RA := @URA.pointwise_dep K M.

  Lemma pwd_extends (f0 f1: forall (k : K), M k) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; eauto. Qed.

  Lemma pwd_wf: forall (f: forall (k : K), M k) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pwd_add_disj_wf
        (f g: forall (k : K), M k)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. specialize (DISJ k). des; rewrite DISJ.
    - rewrite URA.unit_idl; eauto.
    - rewrite URA.unit_id; eauto.
  Qed.

  Lemma pwd_lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

End PWDAUX.

Module Gset.
  Import gmap.

  Definition add (x y : option (gset positive)) : option (gset positive) :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : URA.t :=
    {|
      URA.car := option (gset positive);
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    unfold add. intros [] []; des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.

End Gset.


Module CoPset.

  Definition add (x y : option coPset) : option coPset :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : URA.t :=
    {|
      URA.car := option coPset;
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    intros [] []; ss. des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. f_equal. set_solver.
  Qed.

End CoPset.

Section PROOF.
  Context `{Σ: GRA.t}.

  Lemma Own_unit
    :
      bi_entails True%I (Own ε)
  .
  Proof.
    red. uipropall. ii. rr. esplits; et. rewrite URA.unit_idl. refl.
  Qed.

  Context `{@GRA.inG M Σ}.

  Lemma embed_unit
    :
      (GRA.embed ε) = ε
  .
  Proof.
    unfold GRA.embed.
    Local Transparent GRA.to_URA. unfold GRA.to_URA. Local Opaque GRA.to_URA.
    Local Transparent URA.unit. unfold URA.unit. Local Opaque URA.unit.
    cbn.
    apply func_ext_dep. i.
    dependent destruction H. ss. rewrite inG_prf. cbn. des_ifs.
  Qed.

End PROOF.

Section PROOF.
  Context `{@GRA.inG M Σ}.

  Lemma OwnM_unit
    :
      bi_entails True%I (OwnM ε)
  .
  Proof.
    unfold OwnM. r. uipropall. ii. rr. esplits; et. rewrite embed_unit. rewrite URA.unit_idl. refl.
  Qed.
End PROOF.

Lemma URA_wf_extends_add `{Σ: GRA.t} (r r' c: Σ)
  (EXT : URA.extends r r')
  (WF : URA.wf (r' ⋅ c))
  :
  URA.wf (r ⋅ c).
Proof.
  eapply URA.wf_extends; eauto.
  eapply URA.extends_add. eauto.
Qed.

Lemma URA_extends_refl `{Σ: GRA.t} (r: Σ):
  URA.extends r r.
Proof. refl. Qed.

From iris.bi Require Import bi.

Section bi_proset_mixin.

  Context (PROP : bi).
  Context (ob : Type).
  Context (hom : ob -> ob -> PROP).

  Record BiProsetMixin : Prop :=
    {
      proset_mixin_refl : forall x, emp ⊢ hom x x;
      proset_mixin_trans : forall x y z, hom x y ∗ hom y z ⊢ hom x z;
    }.

  Context (unit : ob).
  Context (tensor : ob -> ob -> ob).

  Record BiMonProsetMixin : Prop :=
    {
      proset_mixin_tensor_hom : forall x x' y y', hom x x' ∗ hom y y' ⊢ hom (tensor x y) (tensor x' y');
      proset_mixin_tensor_assoc : forall x y z, emp ⊢ hom (tensor (tensor x y) z) (tensor x (tensor y z));
      proset_mixin_tensor_assoc_inv : forall x y z, emp ⊢ hom (tensor x (tensor y z)) (tensor (tensor x y) z);
      proset_mixin_tensor_left_unit : forall x, emp ⊢ hom (tensor unit x) x;
      proset_mixin_tensor_left_unit_inv : forall x, emp ⊢ hom x (tensor unit x);
      proset_mixin_tensor_right_unit : forall x, emp ⊢ hom (tensor x unit) x;
      proset_mixin_tensor_right_unit_inv : forall x, emp ⊢ hom x (tensor x unit);
    }.

  Record BiSymMonProsetMixin : Prop :=
    {
      proset_mixin_tensor_braid : forall x y, emp ⊢ hom (tensor x y) (tensor y x);
    }.

End bi_proset_mixin.

Section bi_proset.

  (* (PROP,∗,emp)-enriched preordered set equipped with symmetric monoidal structure *)
  Record BiProset (PROP : bi) : Type :=
    { proset_ob :> Type;
      proset_hom : proset_ob -> proset_ob -> PROP;
      proset_unit : proset_ob;
      proset_tensor : proset_ob -> proset_ob -> proset_ob;
      proset_bi_proset_mixin : BiProsetMixin PROP proset_ob proset_hom;
      proset_bi_mon_proset_mixin : BiMonProsetMixin PROP proset_ob proset_hom proset_unit proset_tensor;
      proset_bi_sym_mon_proset_mixin : BiSymMonProsetMixin PROP proset_ob proset_hom proset_tensor;
    }.

End bi_proset.

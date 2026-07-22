From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod SMod.

Class MapLookupResult {A}
    (m : gmap fname A) (fn : fname) (result : option A) : Prop :=
  { map_lookup_result_eq : m !! fn = result }.

Global Hint Mode MapLookupResult + + + - : typeclass_instances.

Global Instance map_lookup_result_empty {A} fn :
  MapLookupResult (∅ : gmap fname A) fn None.
Proof. constructor. apply lookup_empty. Qed.

Global Instance map_lookup_result_insert_hit {A} k (v : A) m :
  MapLookupResult (<[k := v]> m) k (Some v) | 5.
Proof. constructor. apply lookup_insert. Qed.

Global Instance map_lookup_result_insert {A} k (v : A) m fn result
    `{Hlookup : !MapLookupResult m fn result} :
  MapLookupResult (<[k := v]> m) fn
    (if decide (fn = k) then Some v else result) | 10.
Proof.
  constructor. destruct (decide (fn = k)) as [-> | Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne; [apply map_lookup_result_eq | congruence].
Qed.

Class FnsemLookupResult {A}
    (m : gmap fname A) (fn : fname) (result : option A) : Prop :=
  { fnsem_lookup_result_eq : m !! fn = result }.

Global Hint Mode FnsemLookupResult + + + - : typeclass_instances.

Definition merge_lookup_result {A} (f : A → A → option A)
    (left right : option A) : option A :=
  match left, right with
  | None, None => None
  | Some x, None => Some x
  | None, Some y => Some y
  | Some x, Some y => f x y
  end.

Global Instance fnsem_lookup_result_add `{Σ : GRA}
    (left right : @Mod.t Σ) fn left_result right_result
    `{Hleft : !FnsemLookupResult (Mod.fnsems left) fn left_result,
      Hright : !FnsemLookupResult (Mod.fnsems right) fn right_result} :
  FnsemLookupResult (Mod.fnsems (left ★ right)) fn
    (merge_lookup_result uwnd left_result right_result) | 10.
Proof.
  constructor. rewrite /Mod.add /Mod.fnsems /= lookup_union_with
    !fnsem_lookup_result_eq.
  destruct left_result, right_result; done.
Qed.

Global Instance fnsem_lookup_result_to_mod
    `{!crisG Γ Σ α β τ _S _I}
    sp (m : SMod.t) fn result
    `{Hlookup : !MapLookupResult (SMod.fnsems m) fn result} :
  FnsemLookupResult (Mod.fnsems (SMod.to_mod sp m)) fn
    ((λ x : option (emask * (option fspec_rel * fbody)),
        map_snd (SModTr.trans_fnsem sp) <$> x) <$> result) | 30.
Proof.
  constructor. rewrite /SMod.to_mod /Mod.fnsems /= lookup_fmap
    map_lookup_result_eq //.
Qed.

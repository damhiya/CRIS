Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod.
Require Export FSpec ModTr Sandbox.

Module Mod. Section Mod.
  Context {Σ : GRA}.
  Record t : Type := mk {
    scopes : gmultiset string;
    fnsems : gmap (option string) (option (emask * fbody));
    initial_st : gmap key (option Any.t);

    well_scoped_fns :
      map_Forall
        (λ _ '((msk, _) : emask * _),
          (∀ (k : key) (v : Any.t), msk _ (subevent _ (SPut k v)) = true → k.1 ∈ scopes) ∧
          (∀ (k : key), msk _ (subevent _ (SGet k)) = true → k.1 ∈ scopes))
        (omap id fnsems);
    well_scoped_init :
      (set_map fst (dom initial_st)) ⊆ dom scopes;
    nodup_init :
      (∀ x, multiplicity x scopes ≤ 1) → map_Forall (const is_Some) initial_st;
  }.

  Record wf (ms : t) : Prop := mk_wf {
    wf_fns : map_Forall (const is_Some) (fnsems ms);
    wf_scopes : ∀ x, multiplicity x (scopes ms) ≤ 1;
  }.

  (** Linking *)
  Program Definition empty : t := {|
    scopes := ∅;
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Solve All Obligations with ii; ss.

  Program Definition add (ms1 ms2 : t) : t := {|
    scopes := (scopes ms1) ⊎ (scopes ms2);
    fnsems := union_with (λ _ _, Some None) (fnsems ms1) (fnsems ms2);
    initial_st := union_with (λ _ _, Some None) (initial_st ms1) (initial_st ms2);
  |}.
  Next Obligation.
    intros ms1 ms2 fn [msk p].
    rewrite lookup_omap lookup_union_with.
    destruct ((fnsems ms1) !! fn) eqn: Heq1; destruct ((fnsems ms2) !! fn) eqn: Heq2; ss; intros ->.
    { hexploit (ms1.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq1 //. }
      intros [? ?]; split; ii; apply gmultiset_elem_of_disj_union; left; eauto.
    }
    { hexploit (ms2.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq2 //. }  
      intros [? ?]; split; ii; apply gmultiset_elem_of_disj_union; right; eauto.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 fn [[scp ?] [-> [? Hin]%elem_of_dom]]%elem_of_map; ss.
    apply lookup_union_with_Some in Hin; des; ss;
      apply gmultiset_elem_of_dom, gmultiset_elem_of_disj_union; [left|right|left].
    { hexploit (ms1.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
    { hexploit (ms2.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
    { hexploit (ms1.(well_scoped_init)) => /(_ scp); rewrite gmultiset_elem_of_dom; eauto.
      intros k; apply: k; apply elem_of_map; eexists (_, _); split; eauto; apply elem_of_dom; done.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 H1; rewrite map_Forall_lookup; intros [scp key] v.
    rewrite lookup_union_with_Some; intros [Hl | [Hl | [? [? [Hl1 Hl2]]]]]; des.
    { apply (nodup_init ms1); eauto.
      intros x; hexploit (H1 x); rewrite multiplicity_disj_union; lia.
    }
    { apply (nodup_init ms2); eauto.
      intros x; hexploit (H1 x); rewrite multiplicity_disj_union; lia.
    }
    hexploit (well_scoped_init ms1) => /(_ scp); rewrite elem_of_map.
    intros Hin1; hexploit Hin1; [exists (scp, key); split; ss; apply elem_of_dom; eauto|].
    rewrite gmultiset_elem_of_dom elem_of_multiplicity.
    hexploit (well_scoped_init ms2) => /(_ scp); rewrite elem_of_map.
    intros Hin2; hexploit Hin2; [exists (scp, key); split; ss; apply elem_of_dom; eauto|].
    rewrite gmultiset_elem_of_dom elem_of_multiplicity.
    hexploit (H1 scp); rewrite multiplicity_disj_union; lia.
  Qed.

  Lemma t_eq (ms1 ms2 : t) :
    scopes ms1 = scopes ms2 →
    fnsems ms1 = fnsems ms2 →
    initial_st ms1 = initial_st ms2 →
    ms1 = ms2.
  Proof.
    destruct ms1, ms2; ss. intros Hscp Hfns Hst.
    subst scopes0 fnsems0 initial_st0; f_equal; apply proof_irrelevance.
  Qed.

  Lemma add_comm (ms1 ms2 : t) : Mod.add ms1 ms2 = Mod.add ms2 ms1.
  Proof.
    apply t_eq; ss.
    { rewrite gmultiset_disj_union_comm; eauto. }
    { apply fin_maps.union_with_comm; done. }
    { apply fin_maps.union_with_comm; done. }
  Qed.

  Lemma add_wf (ms1 ms2 : t) : wf (add ms1 ms2) → wf ms1 ∧ wf ms2.
  Proof.
    intros [Hfnsems Hscopes]; split; econs; eauto; try
      (intros x; hexploit (Hscopes x); ss; rewrite multiplicity_disj_union; lia).
    { rewrite map_Forall_lookup; intros i x Hix; rewrite map_Forall_lookup in Hfnsems.
      hexploit (Hfnsems i x); eauto.
      rewrite lookup_union_with Hix; destruct (_ ms2 !! i) eqn : Hms2; ss.
      hexploit (Hfnsems i None); [rewrite lookup_union_with Hix Hms2 //|intros Hf; inv Hf].
    }
    { rewrite map_Forall_lookup; intros i x Hix; rewrite map_Forall_lookup in Hfnsems.
      hexploit (Hfnsems i x); eauto.
      rewrite lookup_union_with Hix; destruct (_ ms1 !! i) eqn : Hms1; ss.
      hexploit (Hfnsems i None); [rewrite lookup_union_with Hix Hms1 //|intros Hf; inv Hf].
    }
  Qed.

  Lemma lookup_add_l (ms1 ms2 : t) (fno : option string) (mb : emask * fbody) :
    wf (add ms1 ms2) →
    (fnsems ms1) !! fno = Some (Some mb) →
    (fnsems (add ms1 ms2)) !! fno = Some (Some mb).
  Proof.
    intros Hwf; rewrite /= lookup_union_with => Hin; rewrite Hin.
    hexploit (wf_fns _ Hwf); rewrite map_Forall_lookup => /(_ fno) /=.
    rewrite lookup_union_with Hin; destruct (_ ms2 !! _) eqn : Hms2; ss.
    by move => /(_ None (reflexivity _)) [? ?].
  Qed.

  Lemma lookup_add_r (ms1 ms2 : t) (fno : option string) (mb : emask * fbody) :
    wf (add ms1 ms2) →
    (fnsems ms2) !! fno = Some (Some mb) →
    (fnsems (add ms1 ms2)) !! fno = Some (Some mb).
  Proof.
    intros Hwf; rewrite /= lookup_union_with => Hin; rewrite Hin.
    hexploit (wf_fns _ Hwf); rewrite map_Forall_lookup => /(_ fno) /=.
    rewrite lookup_union_with Hin; destruct (_ ms1 !! _) eqn : Hms1; ss.
    by move => /(_ None (reflexivity _)) [? ?].
  Qed.

  Definition to_lmod (ms : t) (r : Σ) : LMod.t := {|
    LMod.fnsems := ModTr.trans_fnsem <$> (SB.sandbox_body <$> omap id (fnsems ms));
    LMod.initial_st := Any.pair (ModTr.state_encode (initial_st ms)) r↑;
  |}.

  Lemma mod_dom_subseteq (ms1 ms2 ms3 : t) :
    dom (fnsems ms1) ⊆ dom (fnsems ms2) →
    dom (fnsems (Mod.add ms1 ms3)) ⊆ dom (fnsems (Mod.add ms2 ms3)).
  Proof.
    intros Hsub x; rewrite ?elem_of_dom ?lookup_union_with.
    destruct (_ ms1 !! x) eqn: Heq1.
    { apply elem_of_dom_2, Hsub, elem_of_dom in Heq1.
      destruct (_ ms2 !! x) eqn : Heq2; [|inv Heq1].
      destruct (_ ms3 !! x); ss.
    }
    { apply not_elem_of_dom_2 in Heq1.
      destruct (_ ms3 !! x) eqn : Heq3; [|intros ?%is_Some_None]; ss.
      destruct (_ ms2 !! x) eqn : Heq2; ss.
    }
  Qed.

  Definition modc : Type := (t * iProp Σ)%type.
  Global Instance modc_equiv : Equiv modc := λ m1 m2, m1.1 = m2.1 ∧ m1.2 ≡ m2.2.
  Global Instance modc_equiv_equiv : Equivalence modc_equiv.
  Proof using.
    split; ss; ii.
    { inv H; split; clarify. }
    { inv H; inv H0; split; clarify; ss.
      { rewrite H1 H; ss. }
      { i; rewrite H2 H3; ss. }
    }
  Qed.

  Definition empty_mc : modc := (empty, emp%I).
End Mod. End Mod.

Infix "★" := Mod.add (at level 60, right associativity).
Notation "⌽" := Mod.empty (at level 9).

Section ModFacts.
  Context `{Σ : GRA}.

  Lemma mod_add_assoc (md1 md2 md3 : Mod.t) :
    (md1 ★ md2) ★ md3 = md1 ★ md2 ★ md3.
  Proof using.
    destruct md1, md2, md3.
    apply Mod.t_eq; s; try rewrite assoc //.
    { apply map_eq; intros ?; rewrite ?lookup_union_with; repeat (destruct (_ !! _)); ss. }
    { apply map_eq; intros ?; rewrite ?lookup_union_with; repeat (destruct (_ !! _)); ss. }
  Qed.

  Lemma mod_add_empty_l (md : Mod.t) : md = ⌽ ★ md.
  Proof using. destruct md. apply Mod.t_eq; s; rewrite left_id //. Qed.

  Lemma mod_add_empty_r (md : Mod.t) : md = md ★ ⌽.
  Proof using. destruct md. apply Mod.t_eq; s; rewrite right_id //. Qed.

  Lemma mod_addc_assoc (md : Mod.t) (P Q R : iProp Σ) :
    (md, (P ∗ Q) ∗ R)%I ≡ (md, P ∗ Q ∗ R)%I.
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "[[P Q] R]"; iFrame. }
    { iIntros "[P [Q R]]"; iFrame. }
  Qed.

  Lemma mod_addc_empty_l (md : Mod.t) (P : iProp Σ) :
    (md, P) ≡ (md, emp ∗ P)%I.
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "P"; iFrame. }
    { iIntros "[_ P]"; iFrame. }
  Qed.

  Lemma mod_addc_empty_r (md : Mod.t) (P : iProp Σ) :
   (md, P) ≡ (md, P ∗ emp)%I.
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "P"; iFrame. }
    { iIntros "[P _]"; iFrame. }
  Qed.
End ModFacts.

(* Tactics for map definitions. *)
Tactic Notation "mod_tac" tactic(tac) :=
  let rec go :=
  match goal with
  | |- map_Forall ?P ∅ => apply map_Forall_empty
  | |- map_Forall ?P {[_:=_]} => apply map_Forall_singleton; tac
  | |- map_Forall ?P (<[_:=_]> _) =>
      apply map_Forall_insert_2; [tac|go]
  end
  in try go.

Ltac scope_solver := ss; split; i; case_decide; naive_solver.

(* Lemmas related to module states and function maps *)
Lemma map_Forall_union_with `{Countable K} {V} (m1 m2 : gmap K (option V)) :
  map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
  map_Forall (const is_Some) m1 ∧ map_Forall (const is_Some) m2.
Proof.
  rewrite ?map_Forall_lookup => Hwf; split; intros i v Hi; move: (Hwf i v);
    rewrite lookup_union_with Hi; repeat destruct (_ !! i) as [[|]|]; ss; clarify; eauto.
Qed.

Lemma lookup_union_with_l `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) (v : V):
  map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
  m1 !! k = Some (Some v) →
  union_with (λ _ _, Some None) m1 m2 !! k = Some (Some v).
Proof.
  intros Hwf Hm1; rewrite lookup_union_with Hm1; destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma lookup_union_with_r `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) (v : V):
  map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
  m2 !! k = Some (Some v) →
  union_with (λ _ _, Some None) m1 m2 !! k = Some (Some v).
Proof.
  intros Hwf Hm2; rewrite lookup_union_with Hm2; destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma insert_union_with_l' `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
  is_Some (m1 !! k) →
  <[k := v]> (union_with (λ _ _, Some None) m1 m2) =
  union_with (λ _ _, Some None) (<[k := v]> m1) m2.
Proof.
  intros Hwf [? Hm1]; apply insert_union_with_l.
  destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma insert_union_with_r' `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
  is_Some (m2 !! k) →
  <[k := v]> (union_with (λ _ _, Some None) m1 m2) =
  union_with (λ _ _, Some None) m1 (<[k := v]> m2).
Proof.
  intros Hwf [? Hm2]; apply insert_union_with_r.
  destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

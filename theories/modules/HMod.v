Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import PropExtensionality.

Require Import Mod.
Require Export HModTr.

Set Implicit Arguments.

Definition fnsems_scopes {T} (fn : string) (fnsems : alist string (list string * T)) :=
  match (alist_find fn fnsems) with
  | Some (keys, body) => keys
  | None => []
  end.

Definition state_scopes (st : alist key Any.t) :=
  List.map (fst ∘ fst) st.

Module HMod. Section HMod.
  Context {Σ : GRA}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist string (list string * (Any.t → itree hmodE Any.t));
    initial_st : alist key Any.t;

    well_scoped_fns :
      ∀ fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init :
      incl (state_scopes initial_st) scopes;
    nodup_fns :
      List.NoDup scopes → List.NoDup (List.map fst initial_st);
  }.

  Record wf (ms : t) : Prop := mk_wf {
    wf_fns : List.NoDup (List.map fst ms.(fnsems));
    wf_scopes : List.NoDup ms.(scopes);
  }.

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := [];
    initial_st := [];
  |}.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. econs. Qed.

  Program Definition add ms1 ms2 : t := {|
    fnsems := ms1.(fnsems) ++ ms2.(fnsems);
    scopes := ms1.(scopes) ++ ms2.(scopes);
    initial_st := ms1.(initial_st) ++ ms2.(initial_st);
  |}.
  Next Obligation.
    ii. unfold fnsems_scopes in H. des_ifs.
    rewrite alist_find_app_o in Heq. des_ifs.
    {
      hexploit (ms1.(well_scoped_fns) fn a).
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
    {
      hexploit (ms2.(well_scoped_fns) fn a).
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
  Qed.
  Next Obligation.
    unfold state_scopes. ii. destruct ms1, ms2. ss.
    rewrite map_app in H. apply in_or_app. apply in_app_or in H.
    destruct H; eauto.
  Qed.
  Next Obligation.
    ii. exploit nodup_app_l; eauto. i.
    exploit nodup_app_r; eauto; i.
    apply ms1 in x0. apply ms2 in x1.
    assert (INCL1:= ms1.(well_scoped_init)).
    assert (INCL2:= ms2.(well_scoped_init)).
    revert_until ms2. unfold state_scopes.
    generalize (initial_st ms1) as l1.
    generalize (initial_st ms2) as l2.
    i. revert_until l1. induction l1; ss.
    i. econs; cycle 1.
    {
      eapply IHl1; eauto.
      { eapply NoDup_cons_iff in x0. des. eauto. }
      { ss. ii. eapply INCL1. ss. eauto. }
    }
    ii. rewrite map_app in H0. eapply in_app_or in H0. des.
    { eapply NoDup_cons_iff in x0. des. eauto. }
    eapply NoDup_app_disjoint; eauto.
    { eapply INCL1. s. left. eauto. }
    { eapply INCL2. rewrite - List.map_map. eapply in_map. eauto. }
  Qed.

  Definition to_mod (ms : t) (r : Σ) : Mod.t := {|
    Mod.fnsems := List.map (map_snd (HModTr.trans_ktree ∘ HModTr.sandbox_body)) ms.(fnsems);
    Mod.initial_st := Any.pair (HModTr.alist_encode ms.(initial_st)) r↑;
  |}.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

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

  Definition pair : Type := (univ_id → t) * iProp Σ.
  Global Instance pair_equiv : Equiv pair :=
    λ m1 m2, ∀ υ, (m1.1 υ, m1.2) ≡ (m2.1 υ, m2.2).
  Global Instance pair_equiv_equiv : Equivalence pair_equiv.
  Proof using.
    split; ss; ii.
    { specialize (H υ). inv H; split; clarify. }
    { specialize (H υ). specialize (H0 υ). inv H; inv H0; split; clarify; ss.
      { rewrite H1 H; ss. }
      { i; rewrite H2 H3; ss. }
    }
  Qed.

  Definition pair_included (p1 p2 : pair) : Prop :=
    (∀ u, p1.1 u = p2.1 u) ∧ (p2.2 ⊢ p1.2)%I.
  Global Instance pair_subseteq : SubsetEq pair := pair_included.
End HMod. End HMod.

Infix "★" := HMod.add (at level 60, right associativity).
Notation "⌽" := HMod.empty (at level 9).

Notation "░ it" := (HModTr.sandbox _ it) (at level 60, only printing).

Section HModFacts.
  Context `{Σ : GRA}.

  Lemma hmod_extensionality (ms1 ms2 : HMod.t)
      (SCOPE : HMod.scopes ms1 = HMod.scopes ms2)
      (FNSEM : HMod.fnsems ms1 = HMod.fnsems ms2)
      (INITS : HMod.initial_st ms1 = HMod.initial_st ms2)
       :
    ms1 = ms2.
  Proof using. destruct ms1, ms2; ss. subst. f_equal; apply proof_irrelevance. Qed.

  Lemma hmod_add_assoc (md1 md2 md3 : HMod.t) :
    (md1 ★ md2) ★ md3 = md1 ★ md2 ★ md3.
  Proof using.
    destruct md1, md2, md3.
    apply hmod_extensionality; s; try rewrite app_assoc; eauto.
  Qed.

  Lemma hmod_add_empty_l (md : HMod.t) : ⌽ ★ md = md.
  Proof using. destruct md. apply hmod_extensionality; s; eauto. Qed.

  Lemma hmod_add_empty_r (md : HMod.t) : md ★ ⌽ = md.
  Proof using.
    destruct md. apply hmod_extensionality; s; try rewrite app_nil_r; eauto.
  Qed.

  Lemma hmod_addL_app l l' : HMod.addL (l ++ l') = (HMod.addL l) ★ (HMod.addL l').
  Proof using.
    induction l; s.
    - rewrite hmod_add_empty_l. eauto.
    - rewrite hmod_add_assoc. rewrite IHl. eauto.
  Qed.

  Lemma hmod_addc_assoc (md : HMod.t) (P Q R : iProp Σ) :
    (md, (P ∗ Q) ∗ R)%I ≡ (md, P ∗ Q ∗ R)%I.
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "[[P Q] R]"; iFrame. }
    { iIntros "[P [Q R]]"; iFrame. }
  Qed.

  Lemma hmod_addc_empty_l (md : HMod.t) (P : iProp Σ) :
    (md, emp ∗ P)%I ≡ (md, P).
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "[_ P]"; iFrame. }
    { iIntros "P"; iFrame. }
  Qed.

  Lemma hmod_addc_empty_r (md : HMod.t) (P : iProp Σ) :
    (md, P ∗ emp)%I ≡ (md, P).
  Proof using.
    econs; ss.
    iSplit.
    { iIntros "[P _]"; iFrame. }
    { iIntros "P"; iFrame. }
  Qed.

  Lemma case_itrH R (itrH : itree hmodE R) :
    (exists v, itrH = Ret v) \/
    (exists itrH', itrH = tau;; itrH') \/
    (exists P itrH', itrH = (trigger (Assume P);;; itrH')) \/
    (exists P itrH', itrH = (trigger (Guarantee P);;; itrH')) \/
    (exists R (s : schE R) ktrH', itrH = (trigger s >>= ktrH')) \/
    (exists R (c : callE R) ktrH', itrH = (trigger c >>= ktrH')) \/
    (exists R (s : pgE R) ktrH', itrH = (trigger s >>= ktrH')) \/
    (exists R (e : coreE R) ktrH', itrH = (trigger e >>= ktrH')).
  Proof using.
    ides itrH; eauto.
    right; right.
    destruct e; [destruct a|destruct p; [|destruct s; [|destruct s]]].
    - left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - do 2 right; left. exists X, s, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 3 right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 4 right; left. exists X, p, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 5 right. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  Qed.
End HModFacts.

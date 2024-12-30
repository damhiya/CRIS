Require Import Common.
Require Import PropExtensionality.

Require Import Skeleton Mod.
Require Export HMod2Mod.

Set Implicit Arguments.

Definition fnsems_scopes {T} (fn : gname) (fnsems : alist gname (list string * T)) :=
  match (alist_find fn fnsems) with
  | Some (keys, body) => keys
  | None => []
  end.

Definition state_scopes (st : alist key Any.t) :=
  List.map (fst ∘ fst) st.

Module HModSem. Section HModSem.
  Context {Σ : GRA}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist gname (list string * (Any.t → itree hmodE Any.t));
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

  (**** Sandboxing ****)
  Definition handle_sandbox scopes : hmodE -< hmodE :=
    λ T e,
      match e with
       | inr1 (inr1 (inr1 (inl1 (SPut (s, f) v)))) =>
           if existsb (String.eqb s) scopes then e else inr1 (inr1 (inr1 (inr1 (Choose T))))
       | inr1 (inr1 (inr1 (inl1 (SGet (s, f))))) =>
           if existsb (String.eqb s) scopes then e else inr1 (inr1 (inr1 (inr1 (Choose T))))
       | _ => e
      end.

  Definition sandbox {T} scopes (itr : itree hmodE T) :=
    translate (handle_sandbox scopes) itr.

  Definition sandbox_body (kb : list string * (Any.t → itree hmodE Any.t)) :=
    λ arg, sandbox kb.1 (kb.2 arg).

  Definition to_mod (ms : t) (r : Σ) : ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (interp_hp_fun ∘ sandbox_body)) ms.(fnsems);
    ModSem.initial_st := Any.pair (alist_encode ms.(initial_st)) r↑;
  |}.
End HModSem. End HModSem.

Module HMod. Section HMod.
  Context {Σ : GRA}.
  Notation iProp := (iProp Σ).

  Record t : Type := mk {
    modsem : Sk.t → HModSem.t;
    sk : Sk.t;
  }.

  Definition empty := {|
    modsem := const (HModSem.empty);
    sk := []
  |}.

  Definition add (md0 md1 : t) : t := {|
    modsem := λ sk, HModSem.add (md0.(modsem) sk) (md1.(modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

  Definition scopes (md : t) : Sk.t → list string :=
    λ sk, (md.(modsem) sk).(HModSem.scopes).

  Definition modc : Type := (t * (Sk.t → iProp))%type.
  Global Instance modc_equiv : Equiv modc := λ m1 m2, m1.1 = m2.1 ∧ ∀ sk, m1.2 sk ≡ m2.2 sk.
  Global Instance modc_equiv_equiv : Equivalence modc_equiv.
  Proof.
    split; ss; ii.
    { inv H; split; clarify. i; rewrite H1; ss. }
    { inv H; inv H0; split; clarify; ss.
      { rewrite H1 H; ss. }
      { i; rewrite H2 H3; ss. }
    }
  Qed.

  Definition empty_mc : modc := (empty, const(emp%I)).

  Definition addc (C C' : Sk.t → iProp) : Sk.t → iProp :=
    (λ sk, C sk ∗ C' sk)%I.
End HMod. End HMod.

Infix "★" := HMod.add (at level 9, right associativity).
Notation "⌽" := HMod.empty (at level 9).
Infix "∗∗" := HMod.addc (at level 9, right associativity).

Notation "░ it" := (HModSem.sandbox _ it) (at level 60, only printing).

Section HModProperties.
  Context `{Σ : GRA}.
  Notation iProp := (iProp Σ).

  Lemma hmodsem_extensionality (ms1 ms2 : HModSem.t)
      (SCOPE : HModSem.scopes ms1 = HModSem.scopes ms2)
      (FNSEM : HModSem.fnsems ms1 = HModSem.fnsems ms2)
      (INITS : HModSem.initial_st ms1 = HModSem.initial_st ms2) :
    ms1 = ms2.
  Proof. destruct ms1, ms2; ss. subst. f_equal; apply proof_irrelevance. Qed.

  Lemma hmodsem_add_assoc (ms1 ms2 ms3 : HModSem.t) :
    HModSem.add (HModSem.add ms1 ms2) ms3 = HModSem.add ms1 (HModSem.add ms2 ms3).
  Proof.
    destruct ms1, ms2, ms3.
    apply hmodsem_extensionality; s; try rewrite app_assoc; eauto.
  Qed.

  Lemma hmodsem_add_empty_l (ms : HModSem.t) :
    HModSem.add HModSem.empty ms = ms.
  Proof. destruct ms. apply hmodsem_extensionality; s; eauto. Qed.

  Lemma hmodsem_add_empty_r ms : HModSem.add ms HModSem.empty = ms.
  Proof. destruct ms. apply hmodsem_extensionality; s; try rewrite app_nil_r; eauto. Qed.

  Lemma hmod_add_assoc (md1 md2 md3 : HMod.t) :
    (md1 ★ md2) ★ md3 = md1 ★ md2 ★ md3.
  Proof.
    destruct md1, md2, md3. unfold HMod.add. s. f_equal.
    - extensionalities. rewrite hmodsem_add_assoc. eauto.
    - unfold Sk.add. rewrite app_assoc. eauto.
  Qed.

  Lemma hmod_add_empty_l (md : HMod.t) : ⌽ ★ md = md.
  Proof.
    destruct md. unfold HMod.add. s. f_equal. extensionalities. apply hmodsem_add_empty_l.
  Qed.

  Lemma hmod_add_empty_r (md : HMod.t) : md ★ ⌽ = md.
  Proof.
    destruct md. unfold HMod.add. s. f_equal.
    - extensionalities. apply hmodsem_add_empty_r.
    - destruct sk; ss. unfold Sk.add. s. rewrite app_nil_r. eauto.
  Qed.

  Lemma hmod_addL_app l l' : HMod.addL (l ++ l') = (HMod.addL l) ★ (HMod.addL l').
  Proof.
    induction l; s.
    - rewrite hmod_add_empty_l. eauto.
    - rewrite hmod_add_assoc. rewrite IHl. eauto.
  Qed.

  Lemma hmod_addc_assoc (md : HMod.t) (P Q R : Sk.t → iProp) :
    (md, (P ∗∗ Q) ∗∗ R) ≡ (md, P ∗∗ Q ∗∗ R).
  Proof.
    econs; ss.
    intros sk; iSplit.
    { iIntros "[[P Q] R]"; iFrame. }
    { iIntros "[P [Q R]]"; iFrame. }
  Qed.

  Lemma hmod_addc_empty_l (md : HMod.t) (P : Sk.t → iProp) :
    (md, (const(emp%I)) ∗∗ P) ≡ (md, P).
  Proof.
    econs; ss.
    intros sk; iSplit.
    { iIntros "[_ P]"; iFrame. }
    { iIntros "P"; iFrame. rewrite /const //. }
  Qed.

  Lemma hmod_addc_empty_r (md : HMod.t) (P : Sk.t → iProp) :
    (md, P ∗∗ (const(emp%I))) ≡ (md, P).
  Proof.
    econs; ss.
    intros sk; iSplit.
    { iIntros "[P _]"; iFrame. }
    { iIntros "P"; iFrame. }
  Qed.
End HModProperties.

(* Sandboxing interpretation lemmas *)
Module HModSB. Section HModSB.
  Context `{Σ : GRA}.

  Lemma transl_bind A B scopes (itr : itree hmodE A) (ktr : A → itree hmodE B) :
    HModSem.sandbox scopes (itr >>= ktr)
    = a <- (HModSem.sandbox scopes itr);; (HModSem.sandbox scopes (ktr a)).
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_bind _ _ _)); eauto. Qed.

  Lemma transl_tau A scopes (itr : itree hmodE A) :
    HModSem.sandbox scopes (tau;; itr) = tau;; (HModSem.sandbox scopes itr).
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_tau _ _)); eauto. Qed.

  Lemma transl_ret A (a : A) scopes :
    HModSem.sandbox scopes (Ret a) = Ret a.
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_ret _ _)); eauto. Qed.

  Lemma transl_call {A} (e : callE A) scopes :
    HModSem.sandbox scopes (trigger e) = trigger e.
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_put scopes k v :
    HModSem.sandbox scopes (trigger (SPut k v))
    = if existsb (String.eqb k.1) scopes then trigger (SPut k v) else trigger (Choose _).
  Proof.
    unfold HModSem.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_get scopes k :
    HModSem.sandbox scopes (trigger (SGet k))
    = if existsb (String.eqb k.1) scopes then trigger (SGet k) else trigger (Choose Any.t).
  Proof.
    unfold HModSem.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_core T scopes (e : coreE T) :
    HModSem.sandbox scopes (trigger e) = trigger e.
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities;
      rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_ag {A} (e : agE A) scopes :
    HModSem.sandbox scopes (trigger e) = trigger e.
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_sch {A} (e : schE A) scopes :
    HModSem.sandbox scopes (trigger e) = trigger e.
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_unwrapU R scopes (r : option R) :
    HModSem.sandbox scopes (unwrapU r) = unwrapU r.
  Proof.
    unfold unwrapU. destruct r.
    - apply transl_ret.
    - unfold triggerUB. rewrite !transl_bind !transl_core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma transl_unwrapN R scopes (r : option R) :
    HModSem.sandbox scopes (unwrapN r) = unwrapN r.
  Proof.
    unfold unwrapN. destruct r.
    - apply transl_ret.
    - unfold triggerNB. rewrite !transl_bind !transl_core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma transl_asm scopes P :
    HModSem.sandbox scopes (assume P) = assume P.
  Proof.
    unfold assume. rewrite transl_bind transl_core transl_ret. eauto.
  Qed.

  Lemma transl_guar scopes P :
    HModSem.sandbox scopes (guarantee P) = guarantee P.
  Proof. rewrite /guarantee transl_bind transl_core transl_ret. eauto. Qed.
End HModSB. End HModSB.

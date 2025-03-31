Require Import Common.
Require Import PropExtensionality.

Require Import Mod.
Require Export HMod2Mod.

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

  Definition to_mod (ms : t) (r : Σ) : Mod.t := {|
    Mod.fnsems := List.map (map_snd (interp_hp_fun ∘ sandbox_body)) ms.(fnsems);
    Mod.initial_st := Any.pair (alist_encode ms.(initial_st)) r↑;
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

Notation "░ it" := (HMod.sandbox _ it) (at level 60, only printing).

Section HModProperties.
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
End HModProperties.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind A B scopes (itr : itree hmodE A) (ktr : A → itree hmodE B) :
    HMod.sandbox scopes (itr >>= ktr)
    = a <- (HMod.sandbox scopes itr);; (HMod.sandbox scopes (ktr a)).
  Proof using. unfold HMod.sandbox. rewrite (bisim_is_eq (translate_bind _ _ _)); eauto. Qed.

  Lemma tau A scopes (itr : itree hmodE A) :
    HMod.sandbox scopes (tau;; itr) = tau;; (HMod.sandbox scopes itr).
  Proof using. unfold HMod.sandbox. rewrite (bisim_is_eq (translate_tau _ _)); eauto. Qed.

  Lemma ret A (a : A) scopes :
    HMod.sandbox scopes (Ret a) = Ret a.
  Proof using. unfold HMod.sandbox. rewrite (bisim_is_eq (translate_ret _ _)); eauto. Qed.

  Lemma vis_ag {X R} scopes (e : agE X) (ktr : X -> itree hmodE R) :
    HMod.sandbox scopes (vis e ktr) = vis e (fun x => HMod.sandbox scopes (ktr x)).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma vis_sch {X R} scopes (e : schE X) (ktr : X -> itree hmodE R) :
    HMod.sandbox scopes (vis e ktr) = vis e (fun x => HMod.sandbox scopes (ktr x)).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma vis_call {X R} scopes (e : callE X) (ktr : X -> itree hmodE R) :
    HMod.sandbox scopes (vis e ktr) = vis e (fun x => HMod.sandbox scopes (ktr x)).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma vis_put {R} scopes k v (ktr : () -> itree hmodE R) :
    HMod.sandbox scopes (vis (SPut k v) ktr)
    = if existsb (String.eqb k.1) scopes
      then vis (SPut k v) (fun x => HMod.sandbox scopes (ktr x))
      else vis (Choose ()) (fun x => HMod.sandbox scopes (ktr x)).
  Proof using. destruct k; ss. eapply observe_eta; ss. des_ifs. Qed.

  Lemma vis_get {R} k scopes (ktr : Any.t -> itree hmodE R) :
    HMod.sandbox scopes (vis (SGet k) ktr)
    = if existsb (String.eqb k.1) scopes
      then vis (SGet k) (fun x => HMod.sandbox scopes (ktr x))
      else vis (Choose Any.t) (fun x => HMod.sandbox scopes (ktr x)).
  Proof using. destruct k; ss. eapply observe_eta; ss. des_ifs. Qed.

  Definition putSB {R} scopes k v (itr : itree hmodE R) : itree hmodE R :=
    HMod.sandbox scopes (trigger (SPut k v));;; itr.

  Definition getSB {R} scopes k (ktr : Any.t -> itree hmodE R) : itree hmodE R :=
    HMod.sandbox scopes (trigger (SGet k)) >>= ktr.

  Lemma SPut_putSB {R} scopes k v (ktr : () -> itree hmodE R) :
    HMod.sandbox scopes (vis (SPut k v) ktr) = putSB scopes k v (HMod.sandbox scopes (ktr tt)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x. destruct x.
    eapply observe_eta; ss.
  Qed.

  Lemma putSB_SPut {R} scopes k v (itr : itree hmodE R) :
    putSB scopes k v itr = HMod.sandbox scopes (trigger (SPut k v));;; itr.
  Proof using.
    reflexivity.
  Qed.

  Lemma putSB_bind {T U} scopes k v (itr : itree hmodE T) (ktr : T -> itree hmodE U) :
    putSB scopes k v itr >>= ktr = putSB scopes k v (itr >>= ktr).
  Proof using.
    unfold putSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma SGet_getSB {R} scopes k (ktr : Any.t -> itree hmodE R) :
    HMod.sandbox scopes (vis (SGet k) ktr) = getSB scopes k (fun x => HMod.sandbox scopes (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma getSB_SGet {R} scopes k (ktr : Any.t -> itree hmodE R) :
    getSB scopes k ktr = x <- HMod.sandbox scopes (trigger (SGet k));; ktr x.
  Proof using.
    reflexivity.
  Qed.

  Lemma getSB_bind {T U} scopes k (ktr1 : Any.t -> itree hmodE T) (ktr2 : T -> itree hmodE U) :
    getSB scopes k ktr1 >>= ktr2 = getSB scopes k (fun x => ktr1 x >>= ktr2).
  Proof using.
    unfold getSB. rewrite bind_bind. reflexivity.
  Qed.

  Lemma vis_core {X R} (e : coreE X) scopes (k : X -> itree hmodE R) :
    HMod.sandbox scopes (vis e k) = vis e (fun x => HMod.sandbox scopes (k x)).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma assumeK {R} scopes P (itr : itree hmodE R) :
    HMod.sandbox scopes (assumeK P itr) = assumeK P (HMod.sandbox scopes itr).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma guaranteeK {R} scopes P (itr : itree hmodE R) :
    HMod.sandbox scopes (guaranteeK P itr) = guaranteeK P (HMod.sandbox scopes itr).
  Proof using. eapply observe_eta; ss. Qed.

  Lemma unwrapUK {X R} scopes x (ktr : X -> itree hmodE R) :
    HMod.sandbox scopes (unwrapUK x ktr) = unwrapUK x (fun x => HMod.sandbox scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} scopes x (ktr : X -> itree hmodE R) :
    HMod.sandbox scopes (unwrapNK x ktr) = unwrapNK x (fun x => HMod.sandbox scopes (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call {A} (e : callE A) scopes :
    HMod.sandbox scopes (trigger e) = trigger e.
  Proof using.
    unfold HMod.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma put scopes k v :
    HMod.sandbox scopes (trigger (SPut k v))
    = if existsb (String.eqb k.1) scopes then trigger (SPut k v) else trigger (Choose _).
  Proof using.
    unfold HMod.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma get scopes k :
    HMod.sandbox scopes (trigger (SGet k))
    = if existsb (String.eqb k.1) scopes then trigger (SGet k) else trigger (Choose Any.t).
  Proof using.
    unfold HMod.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma core T scopes (e : coreE T) :
    HMod.sandbox scopes (trigger e) = trigger e.
  Proof using.
    unfold HMod.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities;
      rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma ag {A} (e : agE A) scopes :
    HMod.sandbox scopes (trigger e) = trigger e.
  Proof using.
    unfold HMod.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma sch {A} (e : schE A) scopes :
    HMod.sandbox scopes (trigger e) = trigger e.
  Proof using.
    unfold HMod.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma unwrapU R scopes (r : option R) :
    HMod.sandbox scopes (unwrapU r) = unwrapU r.
  Proof using.
    unfold unwrapU. destruct r.
    - apply ret.
    - unfold triggerUB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma unwrapN R scopes (r : option R) :
    HMod.sandbox scopes (unwrapN r) = unwrapN r.
  Proof using.
    unfold unwrapN. destruct r.
    - apply ret.
    - unfold triggerNB. rewrite !bind !core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma asm scopes P :
    HMod.sandbox scopes (assume P) = assume P.
  Proof using.
    unfold assume. rewrite bind core ret. eauto.
  Qed.

  Lemma guar scopes P :
    HMod.sandbox scopes (guarantee P) = guarantee P.
  Proof using. rewrite /guarantee bind core ret. eauto. Qed.
End SBRed. End SBRed.

Section HModProp.
  Context {Σ : GRA}.

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
End HModProp.

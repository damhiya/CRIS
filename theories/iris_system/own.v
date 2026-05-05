From iris.algebra Require Import proofmode_classes functions coPset excl csum.
From iris.proofmode Require Import proofmode.
Require Export base_logic.
Require Import allocs.
Require Import Coqlib.
Require Export base_logic iprop.
Import uPred.

Local Definition iRes_singleton `{i : !inG A Σ} (γ : gname) (a : A) : Σ :=
  discrete_fun_singleton (inG_id i) (allocs_frag γ (cmra_transport inG_prf a)).
Global Instance: Params (@iRes_singleton) 4 := {}.

(** * Definitions of resource ownership with ghost locations. *)
Local Definition own_def `{!inG A Σ} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Local Definition own_aux : seal (@own_def). Proof using. by eexists. Qed.
Definition own := own_aux.(unseal).
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Global Arguments own {_ _ _} γ a.

Local Program Definition own_admin_def (Σ : GRA) : iProp Σ :=
  ∃ (X : coPset), ⌜set_infinite X⌝
    ∗ uPred_ownM ((λ i, allocs_auth (@GRA_lookup Σ i) (.∈ X)) : GRAUR Σ).
Local Definition own_admin_aux : seal (@own_admin_def). Proof using. by eexists. Qed.
Definition own_admin := own_admin_aux.(unseal).
Local Definition own_admin_eq : @own_admin = @own_admin_def := own_admin_aux.(seal_eq).
Global Arguments own_admin {_}.
Definition ir_own_admin {Σ : GRA} : GRAUR Σ :=
  λ i, allocs_auth (@GRA_lookup Σ i) (.∈ (⊤ ∖ {[base_γ]} : coPset)).

(** * Definitions of resource ownership - for metatheoretical uses only *)
Local Definition Own_def {Σ : GRA} (a : Σ) : iProp Σ := uPred_ownM a.
Local Definition Own_aux : seal (@Own_def). Proof using. by eexists. Qed.
Definition Own := Own_aux.(unseal).
Local Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).
Global Arguments Own {Σ} a.

Lemma make_own_admin {Σ : GRA} : Own ir_own_admin ⊢ own_admin.
Proof using.
  rewrite own.own_admin_eq /own.own_admin_def.
  iIntros "H". iExists (⊤ ∖ {[base_γ]}).
  iSplit.
  { iPureIntro. eapply difference_infinite, singleton_finite. eapply top_infinite. }
  { rewrite /ir_own_admin own.Own_eq /own.Own_def. iFrame. }
Qed.

Section own_admin.
  Context `{i : !inG A Σ}.
  Implicit Types a : A.
  (* Note : There is no way to impose restrictions on ghost locs for now.
     There probably doesn't exist a model that (1) allows rules
     [own_alloc_strog_dep] and (2) allow splitting of [own_admin].
  *)
  Lemma own_admin_alloc_gen a : ✓ a → own_admin ⊢ |==> own_admin ∗ ∃ γ, own γ a.
  Proof using.
    intros hwf. rewrite ?own_admin_eq /own_admin_def.
    iIntros "[%X [%INF ●]]".
    iMod (bupd_ownM_update _
      (((λ i, allocs_auth (@GRA_lookup Σ i) (.∈ X ∖ {[coPpick X]})) : GRAUR Σ)
      ⋅ iRes_singleton (coPpick X) a)
      with "●") as "[● H]".
    { apply discrete_fun_update; intros i'.
      destruct (decide (inG_id i = i')) as [<-|NE].
      { rewrite discrete_fun_lookup_op. etrans.
        { eapply (allocs_alloc (cmra_transport inG_prf a) _ (.∈ X∖{[coPpick X]}) (coPpick X)).
          { eapply cmra_transport_valid, hwf. }
          { set_solver. }
          { split; last set_solver. apply coPpick_elem_of, coPset_infinite_finite; ss. }
        }
        { eapply cmra_update_op; first reflexivity.
          rewrite /iRes_singleton discrete_fun_lookup_singleton //.
        }
      }
      { rewrite discrete_fun_lookup_op /iRes_singleton discrete_fun_lookup_singleton_ne; eauto.
        rewrite right_id.
        etrans; first eapply
          (allocs_auth_split (.∈ X) (.∈ X∖({[coPpick X]} : coPset)) (.∈ ({[coPpick X]} : coPset))); ss.
        { ii; des. set_solver. }
        { ii; des; try set_solver. eapply elem_of_singleton in H. subst k. eapply coPpick_elem_of.
          eapply coPset_infinite_finite; ss.
        }
        { eapply cmra_update_op_l; intros k; ss. }
      }
    }
    iModIntro; iFrame.
    iSplit; eauto.
    { iPureIntro. eapply difference_infinite, singleton_finite; eauto. }
    { iExists (coPpick X); rewrite own_eq /own_def; done. }
  Qed.

  (* TODO: is this really needed? *)
  Lemma own_admin_split : own_admin -∗ own_admin ∗ own_admin.
  Proof using.
    rewrite ?own_admin_eq /own_admin_def; iIntros "[%X [%H OWN]]".
    apply coPset_split_infinite in H as [X1 [X2 [-> [H [H1 H2]]]]].
    iAssert (uPred_ownM
      ((λ i, allocs_auth (GRA_lookup i) (.∈X1)) ⋅ (λ i, allocs_auth (GRA_lookup i) (.∈X2)) : GRAUR Σ))%I
      with "[OWN]" as "O".
    { eapply eq_ind; first iExact "OWN"; f_equiv; extensionalities x.
      instantiate (1:=discrete_fun_op_instance).
      rewrite discrete_fun_lookup_op; apply allocs_auth_split_2_L; set_solver.
    }
    iDestruct "O" as "[$ $]"; done.
  Qed.
End own_admin.

(* Make a lightweight [bupd] with [own_admin] baked in, for easier allocation lemmas. *)
Section own_bupd.
  Context `{Σ : GRA}.
  Implicit Types P : iProp Σ.

  Definition own_bupd P : iProp Σ := own_admin ==∗ own_admin ∗ P.

  Lemma own_bupd_unseal :
    @bupd _ own_bupd = own_bupd.
  Proof. done. Qed.

  Lemma own_bupd_intro P : P ⊢ own_bupd P.
  Proof. iIntros "H INV". iModIntro. iFrame. Qed.

  Lemma own_bupd_mono P Q : (P ⊢ Q) → own_bupd P ⊢ own_bupd Q.
  Proof.
    iIntros (HPQ) "Upd I".
    iMod ("Upd" with "I") as "[$ P]". iModIntro.
    rewrite -HPQ. done.
  Qed.

  Lemma own_bupd_trans P : own_bupd (own_bupd P) ⊢ own_bupd P.
  Proof.
    iIntros "Upd I".
    iMod ("Upd" with "I") as "[I Upd]".
    iApply "Upd". done.
  Qed.

  Lemma own_bupd_frame_r P R : (own_bupd P) ∗ R ⊢ own_bupd (P ∗ R).
  Proof.
    ii. unfold own_bupd. iIntros "[H0 $] INV".
    iApply ("H0" with "INV").
  Qed.

  Lemma uPred_bupd_mixin_own_bupd : BiBUpdMixin (iProp Σ) own_bupd.
  Proof.
    split.
    - rewrite own_bupd_unseal /own_bupd. solve_proper.
    - exact: own_bupd_intro.
    - exact: own_bupd_mono.
    - exact: own_bupd_trans.
    - exact: own_bupd_frame_r.
  Qed.

  (* Not an instance to not contaminate search for original [bupd] *)
  Definition uPred_bi_bupd_own : BiBUpd (iProp Σ) :=
    {| bi_bupd_mixin := uPred_bupd_mixin_own_bupd |}.

  Lemma own_admin_soundness_gen (P : Prop) :
    ((uPred_ownM ((λ i, allocs_auth (@GRA_lookup Σ i) (λ _, True : Prop)) : GRAUR Σ)) ⊢ ⌜P⌝) → P.
  Proof. eapply uPred.ownM_pure_soundness; try done. Qed.

  Lemma own_admin_soundness (P : Prop) :
    (⊢ @bupd _ (@bi_bupd_bupd _ uPred_bi_bupd_own) ⌜P⌝) → P.
  Proof.
    intros Hp; apply own_admin_soundness_gen; iIntros "O".
    rewrite own_bupd_unseal in Hp.
    iMod (Hp with "[O]") as "[_ $]".
    rewrite /own_admin seal_eq; iExists ⊤; iSplit; eauto; iPureIntro; apply top_infinite.
  Qed.
End own_bupd.

(* Notation for use of [own_bupd] with [BiBUpd] lemma supports *)
Reserved Notation "o=> Q"
  (at level 99, Q at level 200, format "'[  ' o=>  '/' Q ']'").
Reserved Notation "P o==∗ Q"
  (at level 99, Q at level 200, format "'[' P  o==∗  '/' Q ']'").

Notation "o=> P" := (@bupd _ (@bi_bupd_bupd _ uPred_bi_bupd_own) P) : bi_scope.
Notation "P o==∗ Q" := (P -∗ o=> Q)%I : bi_scope.
Notation "P o==∗ Q" := (P -∗ o=> Q)%stdpp : stdpp_scope.

Global Instance elim_modal_base_own `{Σ : GRA} b (P Q : iProp Σ) :
  ElimModal True b false (|==> P) P (o=> Q) (o=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    own_bupd_unseal /own_bupd /=.
  iIntros (_) "[>P Q] O".
  iApply ("Q" with "P O").
Qed.

Lemma own_admin_alloc `{Σ : GRA} : ⊢ o=> own_admin.
Proof. rewrite own_bupd_unseal; iIntros "O"; iApply own_admin_split; done. Qed.

Section properties.
  Context `{i : !inG A Σ}.
  Implicit Types a : A.

  Local Instance iRes_singleton_ne γ : NonExpansive (@iRes_singleton A Σ _ γ).
  Proof using.
    by intros ????; apply discrete_fun_singleton_ne, allocs_frag_ne, cmra_transport_ne.
  Qed.
  Local Instance iRes_singleton_proper γ :
    Proper ((≡) ==> (≡)) (@iRes_singleton A Σ _ γ) := ne_proper _.
  Local Lemma iRes_singleton_op γ a1 a2 :
    iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
  Proof using.
    rewrite /iRes_singleton discrete_fun_singleton_op cmra_transport_op.
    f_equiv. rewrite allocs_frag_op; done.
  Qed.
  Local Lemma iRes_singleton_valid γ a : ✓ (iRes_singleton γ a) → ✓ a.
  Proof using.
    intros Ha.
    apply discrete_fun_singleton_valid, discrete_fun_singleton_valid in Ha.
    rewrite Some_valid Cinr_valid cmra_transport_valid // in Ha.
  Qed.

  (** ** Properties of [own] *)
  Global Instance own_ne γ : NonExpansive (@own A Σ _ γ).
  Proof using. rewrite !own_eq; solve_proper. Qed.
  Global Instance own_proper γ : Proper ((≡) ==> (⊣⊢)) (@own A Σ _ γ) := ne_proper _.

  Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
  Proof using. by rewrite !own_eq -ownM_op -iRes_singleton_op. Qed.
  Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
  Proof using. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

  Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own A Σ _ γ).
  Proof using. intros a1 a2. apply own_mono. Qed.

  Lemma own_valid γ a : own γ a ⊢ ⌜✓ a⌝.
  Proof using. rewrite !own_eq /own_def ownM_valid. iPureIntro. apply iRes_singleton_valid. Qed.
  Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ⌜✓ (a1 ⋅ a2)⌝.
  Proof using. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
  Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ⌜✓ (a1 ⋅ a2 ⋅ a3)⌝.
  Proof using. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
  Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ⌜✓ a⌝.
  Proof using. apply: bi.persistent_entails_r. apply own_valid. Qed.
  Lemma own_valid_l γ a : own γ a ⊢ ⌜✓ a⌝ ∗ own γ a.
  Proof using. by rewrite comm -own_valid_r. Qed.

  Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
  Proof using. rewrite !own_eq /own_def. apply _. Qed.
  Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
  Proof using. rewrite !own_eq /own_def; apply _. Qed.

  (* Note : There is no way to impose restrictions on ghost locs for now. *)
  Lemma own_alloc a : ✓ a → ⊢ o=> ∃ γ, own γ a.
  Proof using.
    rewrite own_bupd_unseal. iIntros (hwf) "●own".
    by iApply (own_admin_alloc_gen with "●own").
  Qed.

  Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
  Proof using.
    rewrite ?own_eq /own_def; intros upd.
    eapply bupd_ownM_update, discrete_fun_singleton_update, allocs_frag_update.
    destruct inG_prf. eapply cmra_update_updateP, cmra_updateP_weaken; cycle 1.
    { intros y Hy; eapply Hy. }
    { eapply cmra_transport_updateP.
      { eapply cmra_update_updateP, upd. }
      { intros y <-; eauto. }
    }
  Qed.

  Lemma own_update_2 γ a1 a2 a' :
    a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
  Proof using. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
  Lemma own_update_3 γ a1 a2 a3 a' :
    a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
  Proof using.
    intros. apply entails_wand. do 2 apply wand_intro_r. rewrite -!own_op.
    by iApply own_update.
  Qed.
End properties.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.


(** Big op class instances *)
Section big_op_instances.
  Context `{!inG (A:ucmra) Σ}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
  Proof using. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof using. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof using. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof using. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof using. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof using.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof using. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof using. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof using. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof using. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG A Σ}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof using. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof using. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof using. intros. by rewrite /FromSep -own_op -is_op. Qed.

  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof using. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.

  Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (own γ b1) (own γ b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof using.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof using.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.
(* TODO : Lemma own_unit A `{i : !inG (A:ucmra) Σ} γ : own_admin ⊢ |==> own_admin ∗ own γ (ε:A). *)


Section Own.
  Context `{Σ : GRA}.
  Implicit Types a b : Σ.

  Local Ltac unseal := rewrite Own_eq /Own_def.

  Global Instance Own_ne : NonExpansive (@Own Σ).
  Proof using. unseal. solve_proper. Qed.
  Global Instance Own_proper : Proper ((≡) ==> (⊣⊢)) (@Own Σ) := ne_proper _.

  Global Instance Own_core_persistent a : CoreId a → Persistent (@Own Σ a).
  Proof using. unseal; apply _. Qed.

  Lemma Own_unit : ⊢ Own ε.
  Proof using. unseal. iApply (ownM_unit True). done. Qed.

  Lemma Own_Upd a b (UPD : a ~~> b) : Own a ⊢ |==> Own b.
  Proof using.
    unseal; iIntros "Hr1"; iPoseProof (uPred.bupd_ownM_update with "Hr1") as "Hr2"; eauto.
  Qed.

  Lemma Own_extends (a b : Σ) (EXT : a ≼ b) : Own b ⊢ Own a .
  Proof using. unseal. apply uPred.ownM_mono. done. Qed.

  Lemma Own_op a b : Own (a ⋅ b) ⊣⊢ Own a ∗ Own b.
  Proof using. by unseal; rewrite uPred.ownM_op. Qed.

  Lemma Own_valid a : Own a ⊢ ⌜✓ a⌝.
  Proof using.
    unseal. iIntros "H". iDestruct (uPred.ownM_valid with "H") as "V". done.
  Qed.

  Lemma Own_wand_valid (a1 a2 : Σ) (WAND : Own a1 ⊢ |==> Own a2) (VALID : ✓ a1) : ✓ a2.
  Proof using.
    eapply uPred.bupd_ownM_update_2; last by exact VALID.
    move: WAND; unseal; eauto.
  Qed.

  Lemma Own_bupd_split a P Q (IMPL : Own a ⊢ |==> P ∗ Q) (VALID : ✓ a) :
    ∃ a1 a2, (Own a ⊢ |==> Own a1 ∗ Own a2) ∧ (Own a1 ⊢ P) ∧ (Own a2 ⊢ Q).
  Proof using.
    hexploit (@uPred.bupd_ownM_update_3 Σ); eauto.
    { move: IMPL; unseal; done. }
    intros [y [z [UPD [HP HQ]]]]; exists y, z; split; unseal; [done|split; done].
  Qed.

  Lemma Own_split a P Q (IMPL : Own a ⊢ P ∗ Q) (VALID : ✓ a) :
    ∃ a1 a2, a ≡ a1 ⋅ a2 ∧ (Own a1 ⊢ P) ∧ (Own a2 ⊢ Q).
  Proof using.
    uPred.unseal_in IMPL; apply IMPL in VALID;
      last (unseal; uPred.unseal; exists ε; eauto; rewrite right_id //=).
    destruct VALID as [a1 [a2 [Ha VALID]]]; des; exists a1, a2; split; eauto; split; econs; intros x wfx Own;
      rewrite Own_eq /Own_def in Own; uPred.unseal_in Own; destruct Own as [? ->]; eauto using uPred_mono.
  Qed.

  Lemma Own_bupd_update a b (UPD : Own a ⊢ |==> Own b) :
    a ~~> b.
  Proof using.
    move: UPD; repeat unseal; uPred.unseal; intros UPD.
    rewrite cmra_discrete_total_update; intros z wf.
    destruct UPD as [UPD]; exploit (UPD a); ss.
    { eauto using cmra_valid_op_l. }
    { exists ε; rewrite right_id //. }
    { intros [x' H]; exploit (H z) => //=.
      intros [wfx'z r2x']; destruct r2x' as [x Hx']; rewrite Hx' in wfx'z.
      rewrite comm assoc in wfx'z; eapply cmra_valid_op_l in wfx'z; rewrite comm //.
    }
  Qed.

  Lemma Own_pure_soundness a P (VALID : ✓ a) (DERIV : Own a ⊢ ⌜P⌝) : P.
  Proof using. move: DERIV; unseal => DERIV. eapply uPred.ownM_pure_soundness; eauto. Qed.

  Lemma Own_general_soundness a P (VALID : ✓ a) (DERIV : Own a ⊢ P) : uPred_holds P a.
  Proof using. move: DERIV; unseal=> DERIV; eapply uPred.ownM_general_soundness; eauto. Qed.

  Lemma Own_general_completeness a P (HOLDS : uPred_holds P a) : Own a ⊢ P.
  Proof using. split; unseal; uPred.unseal; i; eapply uPred_mono; eauto. Qed.

  Lemma own_core_completeness a P
    (VALID: ✓ a)
    (OWN: Own a ⊢ □ P)
    :
    Own (core a) ⊢ □ P.
  Proof.
    rewrite {1}/Own {1}seal_eq in OWN.
    eapply uPred.ownM_general_soundness in OWN; et.
    rr in OWN. rewrite seal_eq in OWN. ss. des.
    rr in OWN0. rewrite seal_eq in OWN0. ss.
    eapply Own_general_completeness.
    rr. rewrite seal_eq. s. split.
    - eapply uPred.ownM_general_soundness; et. eapply cmra_core_valid; et.
    - rr. rewrite seal_eq. s. rewrite cmra_core_idemp. et.
  Qed.

  Lemma entails_pointwise (P Q : iProp Σ) :
    (∀ res: Σ, (Own res ⊢ P) → (Own res ⊢ Q)) → P ⊢ Q.
  Proof.
    i. rr. econs. i. eapply uPred.ownM_general_soundness; et.
    eapply Own_general_completeness in H1. eapply H in H1.
    rewrite own.Own_eq in H1. et.
  Qed.

  Global Instance into_sep_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof using. intros. by rewrite /IntoSep (is_op a) Own_op. Qed.

  Global Instance into_and_Own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof using. intros. by rewrite /IntoAnd (is_op a) Own_op bi.sep_and. Qed.

  Global Instance from_sep_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof using. intros. by rewrite /FromSep -Own_op -is_op. Qed.

  (* TODO : Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 → CombineSepAs (Own b1) (Own b2) (Own a) | 60.
  Proof using. intros. by rewrite /CombineSepAs -Own_op -is_op. Qed.
  (* TODO : Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_Own (b1 b2 : Σ) :
    CombineSepGives (Own b1) (Own b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof using.
    intros. rewrite /CombineSepGives -Own_op Own_valid.
    by apply : bi.persistently_intro.
  Qed.
  Global Instance from_and_Own_persistent (a b1 b2 : Σ) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (Own a) (Own b1) (Own b2).
  Proof using.
    intros ? Hb. rewrite /FromAnd (is_op a) Own_op.
    destruct Hb; by rewrite bi.persistent_and_sep.
  Qed.

End Own.

Section own_forall.
  Context `{i : !inG A Σ}.
  Implicit Types a c : A.
  Implicit Types x z : Σ.

  Local Ltac unseal := rewrite Own_eq /Own_def.

  Local Definition iRes_project (γ : gname) (x : Σ) : option A :=
    match x (inG_id i) γ with
    | Some (Cinr a) => Some (cmra_transport (eq_sym inG_prf) a)
    | _ => None
    end.

  Local Instance iRes_project_ne γ : NonExpansive (iRes_project γ).
  Proof.
    intros n x1 x2 Hx. rewrite /iRes_project.
    specialize (Hx (inG_id i) γ).
    destruct (x1 (inG_id i) γ) as [[u1|a1|]|],
      (x2 (inG_id i) γ) as [[u2|a2|]|];
      try (by inversion Hx; subst; try inversion H1).
    inversion Hx; subst.
    inversion H1; subst. by constructor; apply cmra_transport_ne.
  Qed.

  Local Lemma iRes_project_singleton γ a :
    iRes_project γ (iRes_singleton γ a) ≡ Some a.
  Proof.
    rewrite /iRes_project /iRes_singleton discrete_fun_lookup_singleton.
    rewrite /allocs_frag discrete_fun_lookup_singleton /=.
    by rewrite cmra_transport_trans eq_trans_sym_inv_r.
  Qed.

  Local Lemma iRes_project_below γ z c :
    iRes_project γ z = Some c → iRes_singleton γ c ≼ z.
  Proof.
    rewrite /iRes_project.
    destruct (z (inG_id i) γ) as [[e|a'|]|] eqn:Hγ; try done.
    intros Hc. inversion Hc; subst c; clear Hc.
    rewrite /iRes_singleton.
    rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
    exists (discrete_fun_insert (inG_id i)
        (discrete_fun_insert γ None (z (inG_id i))) z).
    intros j. rewrite discrete_fun_lookup_op.
    destruct (decide (j = inG_id i)) as [->|]; last first.
    { rewrite discrete_fun_lookup_singleton_ne //.
      rewrite discrete_fun_lookup_insert_ne //. by rewrite left_id. }
    rewrite discrete_fun_lookup_singleton discrete_fun_lookup_insert.
    intros γ'. rewrite discrete_fun_lookup_op.
    destruct (decide (γ' = γ)) as [->|].
    - by rewrite /allocs_frag discrete_fun_lookup_singleton
        discrete_fun_lookup_insert Hγ right_id.
    - by rewrite /allocs_frag discrete_fun_lookup_singleton_ne //
        discrete_fun_lookup_insert_ne // left_id.
  Qed.

  Local Lemma iRes_singleton_included_project γ x a :
    ✓ x →
    iRes_singleton γ a ≼ x →
    ∃ c, iRes_project γ x = Some c ∧ Some a ≼ Some c.
  Proof.
    intros Hx [y Hy].
    assert (Hin :
      Some (Cinr (cmra_transport inG_prf a)) ≼ x (inG_id i) γ).
    { exists (y (inG_id i) γ).
      specialize (Hy (inG_id i)).
      etrans; first exact (Hy γ).
      rewrite discrete_fun_lookup_op /iRes_singleton
        discrete_fun_lookup_singleton /allocs_frag
        discrete_fun_lookup_op discrete_fun_lookup_singleton //. }
    move: Hx=> /(_ (inG_id i)) /(_ γ) Hx.
    rewrite /iRes_project.
    destruct (x (inG_id i) γ) as [[e|b|]|] eqn:Hγ; simpl in Hx.
    - exfalso.
      apply option_included in Hin as [|(?&?&?&?&[Heq|Hin])]; clarify.
      { inversion Heq. }
      apply csum_included in Hin as [|[(?&?&?&?&?)|(?&?&?&?&?)]]; clarify.
    - exists (cmra_transport (eq_sym inG_prf) b). split; first done.
      apply option_included in Hin as [|(?&?&?&?&[Heq|Hin])]; clarify.
      + apply option_included. right.
        exists a, (cmra_transport (eq_sym inG_prf) b).
        split_and?; try done. left.
        move: Heq=> /Cinr_inj Heq.
        by rewrite -Heq cmra_transport_trans eq_trans_sym_inv_r.
      + apply csum_included in Hin as
          [|[(?&?&?&?&?)|(b1&b2&?&?&Hin)]]; clarify.
        apply option_included. right.
        exists a, (cmra_transport (eq_sym inG_prf) b2).
        split_and?; try done. right.
        destruct Hin as [d Hin]. exists (cmra_transport (eq_sym inG_prf) d).
        by rewrite Hin cmra_transport_op cmra_transport_trans
          eq_trans_sym_inv_r.
    - done.
    - exfalso.
      by apply option_included in Hin as [|(?&?&?&?&?)]; clarify.
  Qed.

  Lemma own_forall `{!Inhabited B} γ (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ ⌜∀ b, Some (f b) ≼ Some c⌝.
  Proof.
    rewrite own_eq /own_def.
    uPred.unseal; split; intros x Hx Hown.
    destruct (iRes_singleton_included_project γ x (f inhabitant) Hx
      (Hown inhabitant)) as (c & Hc & _).
    exists c.
    destruct (iRes_project_below γ x c Hc) as [y Hy].
    exists (iRes_singleton γ c), y.
    split_and?; [done| |].
    - exists (core (iRes_singleton γ c)). by rewrite cmra_core_r.
    - intros b.
      destruct (iRes_singleton_included_project γ x (f b) Hx
        (Hown b)) as (c' & Hc' & Hincl).
      rewrite Hc in Hc'. inv Hc'. done.
  Qed.

  Lemma own_forall_total `{!CmraTotal A, !Inhabited B} γ (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ ⌜∀ b, f b ≼ c⌝.
  Proof.
    iIntros "Hown".
    iDestruct (own_forall with "Hown") as (c) "[Hown %Hincl]".
    iExists c. iFrame. iPureIntro.
    intros b. by apply Some_included_total.
  Qed.

  Lemma own_and γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢
      ∃ c, own γ c ∗ ⌜Some a1 ≼ Some c ∧ Some a2 ≼ Some c⌝.
  Proof.
    iIntros "Hown". iDestruct (own_forall γ (λ b, if b : bool then a1 else a2)
      with "[Hown]") as (c) "[$ %Hincl]".
    { rewrite and_alt.
      iIntros ([]); [iApply ("Hown" $! true)|iApply ("Hown" $! false)]. }
    iPureIntro. split; [apply (Hincl true)|apply (Hincl false)].
  Qed.
  Lemma own_and_total `{!CmraTotal A} γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ ⌜a1 ≼ c ∧ a2 ≼ c⌝.
  Proof.
    iIntros "Hown".
    iDestruct (own_and with "Hown") as (c) "[Hown %Hincl]".
    destruct Hincl as [Ha1 Ha2].
    iExists c. iFrame. iPureIntro.
    split; by apply Some_included_total.
  Qed.

  Lemma own_forall_pred {B} γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) →
    (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢
    ∃ c, own γ c ∗ ⌜∀ b, φ b → Some (f b) ≼ Some c⌝.
  Proof.
    iIntros ([b0 pb0]) "Hown".
    iAssert (∀ b : { b | φ b }, own γ (f (`b)))%I with "[Hown]" as "Hown".
    { iIntros ([b pb]). by iApply ("Hown" $! b). }
    iDestruct (@own_forall _ with "Hown") as (c) "[$ %Hincl]".
    { split. apply (b0 ↾ pb0). }
    iPureIntro. intros b pb. apply (Hincl (b ↾ pb)).
  Qed.
  Lemma own_forall_pred_total `{!CmraTotal A} {B} γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) →
    (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢
    ∃ c, own γ c ∗ ⌜∀ b, φ b → f b ≼ c⌝.
  Proof.
    iIntros (Hinh) "Hown".
    iDestruct (own_forall_pred with "Hown") as (c) "[Hown %Hincl]"; first done.
    iExists c. iFrame. iPureIntro.
    intros b Hb. by apply Some_included_total, Hincl.
  Qed.

  Lemma own_and_discrete_total `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 c :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') →
    own γ a1 ∧ own γ a2 ⊢ own γ c.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (own_and_total with "Hown") as (c') "[Hown %Hincl]".
    destruct Hincl as [Ha1 Ha2].
    iDestruct (own_valid with "Hown") as %?.
    iApply (own_mono with "Hown"); eauto.
  Qed.
  Lemma own_and_discrete_total_False `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) →
    own γ a1 ∧ own γ a2 ⊢ False.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (own_and_total with "Hown") as (c) "[Hown %Hincl]".
    destruct Hincl as [Ha1 Ha2].
    iDestruct (own_valid with "Hown") as %?; eauto.
  Qed.
End own_forall.

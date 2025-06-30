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
Definition initial_resource_own_admin {Σ : GRA} : GRAUR Σ :=
  λ i, allocs_auth (@GRA_lookup Σ i) (.∈ (⊤ ∖ {[base_γ]} : coPset)).

(** * Definitions of resource ownership - for metatheoretical uses only *)
Local Definition Own_def {Σ : GRA} (a : Σ) : iProp Σ := uPred_ownM a.
Local Definition Own_aux : seal (@Own_def). Proof using. by eexists. Qed.
Definition Own := Own_aux.(unseal).
Local Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).
Global Arguments Own {Σ} a.

Lemma make_own_admin {Σ : GRA} : Own initial_resource_own_admin ⊢ own_admin.
Proof using.
  rewrite own.own_admin_eq /own.own_admin_def.
  iIntros "H". iExists (⊤ ∖ {[base_γ]}).
  iSplit.
  { iPureIntro. eapply difference_infinite, singleton_finite. eapply top_infinite. }
  { rewrite /initial_resource_own_admin own.Own_eq /own.Own_def. iFrame. }
Qed.

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
  Local Lemma iRes_singleton_validI γ a : ✓ (iRes_singleton γ a) ⊢@{@iProp Σ} ✓ a.
  Proof using.
    rewrite /iRes_singleton /allocs_frag.
    rewrite discrete_fun_validI (forall_elim (inG_id i)) discrete_fun_lookup_singleton.
    rewrite discrete_fun_validI (forall_elim γ) discrete_fun_lookup_singleton.
    rewrite option_validI csum_validI.
    trans (✓ cmra_transport inG_prf a : @iProp Σ)%I; last by destruct inG_prf.
    done.
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

  Lemma own_valid γ a : own γ a ⊢ ✓ a.
  Proof using. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed.
  Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
  Proof using. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
  Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
  Proof using. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
  Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
  Proof using. apply: bi.persistent_entails_r. apply own_valid. Qed.
  Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
  Proof using. by rewrite comm -own_valid_r. Qed.

  Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
  Proof using. rewrite !own_eq /own_def. apply _. Qed.
  Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
  Proof using. rewrite !own_eq /own_def; apply _. Qed.

  (* TODO : Find a way to hide own_admin using fancy-update-like modalities *)
  (* Note : There is no way to impose restrictions on ghost locs for now. *)
  Lemma own_alloc a : ✓ a → own_admin ⊢ |==> own_admin ∗ ∃ γ, own γ a.
  Proof using.
    intros hwf. rewrite ?own_admin_eq /own_admin_def.
    iIntros "[%X [%INF OWN]]".
    iPoseProof (bupd_ownM_update _ 
      (((λ i, allocs_auth (@GRA_lookup Σ i) (.∈ X ∖ {[coPpick X]})) : GRAUR Σ)
      ⋅ iRes_singleton (coPpick X) a)
      with "OWN") as "> [AUTH OWN]".
    { apply discrete_fun_update; intros i'. destruct (decide ((inG_id i) = i')).
      { subst i'. rewrite discrete_fun_lookup_op. etrans.
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
    CombineSepGives (own γ b1) (own γ b2) (✓ (b1 ⋅ b2)).
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
    unseal. iIntros "H". iDestruct (uPred.ownM_valid with "H") as "V".
    iEval (rewrite uPred.discrete_valid) in "V". iFrame "V".
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

  Lemma entails_pointwise (P Q: iProp Σ):
    (∀ res: Σ, (Own res ⊢ P) → (Own res ⊢ Q)) -> P ⊢ Q.
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

(* tactics for cancellation *)
Ltac gen_eq a :=
  match a with context [?t] =>
    lazymatch t with
    | eq_refl => fail
    | _ =>
      let T := type of t in
      match (eval simpl in T) with
      | _ = _ => generalize t
      end
    end
  end.

Ltac gen_prop a :=
  match a with context [?t] =>
    let T := type of t in
    match (eval simpl in T) with
    | Prop => generalize t
    end
  end.

Ltac remove_eq_aux :=
  let e := fresh "E" in
  intros e;
  match goal with
  | H : @eq ?A ?b _ |- _ => replace H with (@eq_refl A b)
  end; last apply UIP; clear e.

Ltac remove_eq a := gen_eq a; remove_eq_aux.

Module InitRes.
  Definition nil : GRAs.nil.
  Proof using. intros i; inv i. Defined.

  Definition singleton {A : DRA} (a : option A) : GRAs.singleton A.
  Proof using.
    intros i γ. inv_fin i.
    { destruct (decide (γ = base_γ)).
      { destruct a as [a|].
        { ss. exact (Some (Cinr a)). }
        { ss. exact (Some (Cinl (Excl ()))). }
      }
      { exact None. }
    }
    { intros i. inv i. }
  Defined.

  Definition R_prf {Σ1 Σ2 : GRA} (i2 : gid Σ2) :
    @eq cmra
    (allocs.allocsUR positive (@GRA_lookup Σ2 i2))
    (allocs.allocsUR positive (@GRA_lookup (GRAs.app Σ1 Σ2) (Fin.R (@GRA_len Σ1) i2))).
  Proof using. rewrite /GRAs.app /= fin_add_inv_r; refl. Qed.

  Definition L_prf {Σ1 Σ2 : GRA} (i1 : gid Σ1) :
    @eq cmra
    (allocs.allocsUR positive (@GRA_lookup Σ1 i1))
    (allocs.allocsUR positive (@GRA_lookup (GRAs.app Σ1 Σ2) (Fin.L (@GRA_len Σ2) i1))).
  Proof using. rewrite /GRAs.app /= fin_add_inv_l; refl. Qed.

  Definition R {Σ1 Σ2 : GRA} (r2 : Σ2) : GRAs.app Σ1 Σ2.
  Proof using.
    intros i. eapply fin_add_inv with (i:=i).
    { intros i1 g. exact ε. }
    { intros i2. refine (cmra_transport (R_prf i2) (r2 i2)). }
  Defined.

  Definition L {Σ1 Σ2 : GRA} (r1 : Σ1) : GRAs.app Σ1 Σ2.
  Proof using.
    intros i. eapply fin_add_inv with (i:=i).
    { intros i1. refine (cmra_transport (L_prf i1) (r1 i1)). }
    { intros i2 g. exact ε. }
  Defined.

  Lemma R_distr {Σ1 Σ2 : GRA} (r1 r2 : Σ2) : @R Σ1 Σ2 (r1 ⋅ r2) = @R Σ1 Σ2 r1 ⋅ @R Σ1 Σ2 r2.
  Proof using.
    extensionalities i; apply fin_add_inv with (i:=i); clear i.
    { intros i1; rewrite /R ?discrete_fun_lookup_op ?fin_add_inv_l //. }
    { intros i2. rewrite /R discrete_fun_lookup_op fin_add_inv_r.
      rewrite !fin_add_inv_r cmra_transport_op //.
    }
  Qed.

  Lemma L_distr {Σ1 Σ2 : GRA} (r1 r2 : Σ1) : @L Σ1 Σ2 (r1 ⋅ r2) = @L Σ1 Σ2 r1 ⋅ @L Σ1 Σ2 r2.
  Proof using.
    extensionalities i; apply fin_add_inv with (i:=i); clear i.
    { intros i1. rewrite /L discrete_fun_lookup_op fin_add_inv_l.
      rewrite !fin_add_inv_l cmra_transport_op //.
    }
    { intros i2; rewrite /L ?discrete_fun_lookup_op ?fin_add_inv_r //. }
  Qed.

  Definition app {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2) : GRAs.app Σ1 Σ2 :=
    @L Σ1 Σ2 r1 ⋅ @R Σ1 Σ2 r2.

  Lemma singleton_some_valid {A : DRA} (a : A)
      (VALID : ✓ a) :
    ✓ (singleton (Some a) ⋅ initial_resource_own_admin).
  Proof using.
    intros i γ. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_op /singleton /initial_resource_own_admin.
      des_ifs. ss. rewrite left_id /allocs.allocs_auth; des_ifs; ss.
    }
    { intros i; inv i. }
  Qed.

  Lemma singleton_none_valid {A : DRA} :
    ✓ (@singleton A None ⋅ initial_resource_own_admin).
  Proof using.
    intros i γ. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_op /singleton /initial_resource_own_admin.
      des_ifs; ss; rewrite left_id /allocs.allocs_auth; des_ifs.
    }
    { intros i; inv i. }
  Qed.

  Definition app_valid {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2)
      (VALID1 : ✓ (r1 ⋅ initial_resource_own_admin))
      (VALID2 : ✓ (r2 ⋅ initial_resource_own_admin)) :
    ✓ (app r1 r2 ⋅ initial_resource_own_admin).
  Proof using.
    intros i; apply fin_add_inv with (i:=i).
    { intros i1. rewrite /app ?discrete_fun_lookup_op.
      rewrite /L fin_add_inv_l /R fin_add_inv_l right_id.
      rewrite /initial_resource_own_admin.
      match goal with | |- ?A => gen_eq A end.
      rewrite /GRAs.app /= fin_add_inv_l. remove_eq_aux. ss.
    }
    { intros i2. rewrite /app ?discrete_fun_lookup_op.
      rewrite /L fin_add_inv_r /R fin_add_inv_r left_id.
      rewrite /initial_resource_own_admin.
      match goal with | |- ?A => gen_eq A end.
      rewrite /GRAs.app /= fin_add_inv_r. remove_eq_aux. ss.
    }
  Qed.

  Lemma singleton_index {A : DRA} (a : A) :
    singleton (Some a) = discrete_fun_singleton 0%fin (allocs.allocs_frag base_γ a).
  Proof using.
    extensionalities i g. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_singleton //=. }
    { rewrite discrete_fun_lookup_singleton /= /allocs.allocs_frag discrete_fun_lookup_singleton_ne //. }
    { intros i; inv i. }
  Qed.

  Lemma L_index {Σ1 Σ2 : GRA} (i : fin (@GRA_len Σ1)) r :
    @L Σ1 Σ2 (discrete_fun_singleton i r)
    = discrete_fun_singleton (Fin.L (@GRA_len Σ2) i) (cmra_transport (@L_prf Σ1 Σ2 i) r).
  Proof using.
    rewrite /L. extensionalities i1.
    apply fin_add_inv with (i:=i1); cycle 1.
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_r P H1 H2 _) end.
      rewrite discrete_fun_lookup_singleton_ne; ss.
      ii. eapply Fin.L_R_neq; eauto.
    }
    { intros i2; ss.
      destruct (decide (i = i2)).
      { subst.
        match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
        rewrite ?discrete_fun_lookup_singleton //.
      }
      { match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
        rewrite ?discrete_fun_lookup_singleton_ne //.
        { match goal with | |- ?a => gen_eq a end.
          rewrite /GRAs.app /= fin_add_inv_l. remove_eq_aux. ss.
        }
        { ii. apply Fin.L_inj in H. ss. }
      }
    }
  Qed.

  Lemma R_index {Σ1 Σ2 : GRA} (i : fin (@GRA_len Σ2)) r :
    @R Σ1 Σ2 (discrete_fun_singleton i r)
    = discrete_fun_singleton (Fin.R (@GRA_len Σ1) i) (cmra_transport (@R_prf Σ1 Σ2 i) r).
  Proof using.
    rewrite /R. extensionalities i1.
    apply fin_add_inv with (i:=i1); cycle 1.
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_r P H1 H2 _) end.
      destruct (decide (i = i2)).
      { subst. rewrite ?discrete_fun_lookup_singleton //.
      }
      { rewrite ?discrete_fun_lookup_singleton_ne //.
        { match goal with | |- ?a => gen_eq a end.
          rewrite /GRAs.app /= fin_add_inv_r. remove_eq_aux. ss.
        }
        { ii. apply Fin.R_inj in H. ss. }
      }
    }
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
      rewrite discrete_fun_lookup_singleton_ne; ss.
      ii. eapply Fin.L_R_neq; eauto.
    }
  Qed.
End InitRes.
Notation "*[ ]" := InitRes.nil (format "*[ ]").
Notation "*[ Σ1 ; .. ; Σn ]" :=
  (InitRes.app (InitRes.singleton Σ1) .. (InitRes.app (InitRes.singleton Σn) InitRes.nil) ..).
Notation "**[ Σ1 ; .. ; Σn ]" := (InitRes.app Σ1 .. (InitRes.app Σn InitRes.nil) ..).
Notation "'L'" := InitRes.L (at level 50, only printing).
Notation "'R'" := InitRes.R (at level 50, only printing).

Section Lemmas.
  Context `{Σ: GRA}.

  Lemma valid_solve (a b c: Σ) :
    ✓ a -> a ≡  b ⋅ c -> ✓ b.
  Proof using.
    i. eapply cmra_valid_op_l. setoid_rewrite <- H0. eauto.
  Qed.

  Lemma valid_extends (r a b: Σ):
    b ≼ a -> ✓(r ⋅ a) -> ✓ (r ⋅ b).
  Proof using.
    i. apply cmra_mono_l with (z:=r) in H.
    eapply cmra_valid_included; eauto.
  Qed.

  Lemma Own_bupd_valid (r a b: Σ):
    (Own r ⊢|==> Own a ∗ Own b) -> ✓ r -> ✓ (a ⋅ b).
  Proof using.
    i. eapply Own_wand_valid with (a1 := r); eauto.
    iIntros "H". iApply Own_op. iStopProof. eauto.
  Qed.

End Lemmas.  

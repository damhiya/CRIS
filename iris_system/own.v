From iris.algebra Require Import proofmode_classes functions coPset.
From iris.proofmode Require Export proofmode.
From CRIS.base_logic Require Export base_logic.
From CRIS.lib Require Import allocs.
Require Import sflib.
Require Import Level.
Require Export iprop.
Import uPred.

(* Section uPredI.
  (** extra BI instances *)

  Global Instance uPredI_absorbing {M : ucmra} (P : uPredI M) : Absorbing P.
  Proof. apply _. Qed.

  Global Instance uPredI_affine {M : ucmra} (P : uPredI M) : Affine P.
  Proof. apply _. Qed.

  Global Instance uPredI_except_0 {M : ucmra} (P : uPredI M) : IsExcept0 P.
  Proof.
    rewrite /IsExcept0 /bi_except_0. uPred.unseal.
    split=> x WFn. intros [|]; done.
  Qed.

End uPredI.
(* uPredI_affine is added so that IPM can also resolve pure predicates with evars. *)
Global Hint Immediate uPredI_affine : core. *)

(* TODO : 1) refactor GRA
          2) move iProp Σ and own to a separate file *)
Local Definition iRes_singleton `{i : !inG A Σ} (γ : gname) (a : A) : Σ :=
  discrete_fun_singleton (inG_id i) (allocs_frag γ (cmra_transport inG_prf a)).
Global Instance: Params (@iRes_singleton) 4 := {}.

(** * Definitions of resource ownership with ghost locations. *)
Local Definition own_def `{!inG A Σ} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Global Arguments own {_ _ _} γ a.

(* TODO : Think later if mod_levels can be erased *)
Local Program Definition own_admin_def (Σ : GRA) : iProp Σ :=
  ∃ (X : coPset), ⌜set_infinite X⌝
    ∗ uPred_ownM ((λ i, @allocs_auth (@GRA_lookup Σ i) X) : GRAUR Σ).
Local Definition own_admin_aux : seal (@own_admin_def). Proof. by eexists. Qed.
Definition own_admin := own_admin_aux.(unseal).
Local Definition own_admin_eq : @own_admin = @own_admin_def := own_admin_aux.(seal_eq).
Global Arguments own_admin {_}.

(** * Definitions of resource ownership - for metatheoretical uses only *)
Local Definition Own_def {Σ : GRA} (a : Σ) : iProp Σ := uPred_ownM a.
Local Definition Own_aux : seal (@Own_def). Proof. by eexists. Qed.
Definition Own := Own_aux.(unseal).
Local Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).
Global Arguments Own {Σ} a.

Section properties.
  Context `{i : !inG A Σ}.
  Implicit Types a : A.

  Local Instance iRes_singleton_ne γ : NonExpansive (@iRes_singleton A Σ _ γ).
  Proof.
    by intros ????; apply discrete_fun_singleton_ne, allocs_frag_ne, cmra_transport_ne.
  Qed.
  Local Instance iRes_singleton_proper γ :
    Proper ((≡) ==> (≡)) (@iRes_singleton A Σ _ γ) := ne_proper _.
  Local Lemma iRes_singleton_op γ a1 a2 :
    iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
  Proof.
    rewrite /iRes_singleton discrete_fun_singleton_op cmra_transport_op.
    f_equiv. rewrite allocs_frag_op; done.
  Qed.
  Local Lemma iRes_singleton_validI γ a : ✓ (iRes_singleton γ a) ⊢@{@iProp Σ} ✓ a.
  Proof.
    rewrite /iRes_singleton /allocs_frag.
    rewrite discrete_fun_validI (forall_elim (inG_id i)) discrete_fun_lookup_singleton.
    rewrite discrete_fun_validI (forall_elim γ) discrete_fun_lookup_singleton.
    rewrite option_validI csum_validI.
    trans (✓ cmra_transport inG_prf a : @iProp Σ)%I; last by destruct inG_prf.
    done.
  Qed.

  (** ** Properties of [own] *)
  Global Instance own_ne γ : NonExpansive (@own A Σ _ γ).
  Proof. rewrite !own_eq; solve_proper. Qed.
  Global Instance own_proper γ : Proper ((≡) ==> (⊣⊢)) (@own A Σ _ γ) := ne_proper _.

  Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
  Proof. by rewrite !own_eq -ownM_op -iRes_singleton_op. Qed.
  Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
  Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

  Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own A Σ _ γ).
  Proof. intros a1 a2. apply own_mono. Qed.

  Lemma own_valid γ a : own γ a ⊢ ✓ a.
  Proof. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed.
  Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
  Proof. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
  Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
  Proof. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
  Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
  Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
  Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
  Proof. by rewrite comm -own_valid_r. Qed.

  Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
  Proof. rewrite !own_eq /own_def. apply _. Qed.
  Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
  Proof. rewrite !own_eq /own_def; apply _. Qed.

  (* TODO : Find a way to hide own_admin using fancy-update-like modalities *)
  (* Note : There is no way to impose restrictions on ghost locs for now. *)
  Lemma own_alloc a : ✓ a → own_admin ⊢ |==> own_admin ∗ ∃ γ, own γ a.
  Proof.
    intros hwf. rewrite ?own_admin_eq /own_admin_def.
    iIntros "[%X [%INF OWN]]".
    iPoseProof (bupd_ownM_update _
      (((λ i, allocs_auth (@GRA_lookup Σ i) (X ∖ {[coPpick X]})) : GRAUR Σ)
      ⋅ iRes_singleton (coPpick X) a)
      with "OWN") as "> [AUTH OWN]".
    { apply discrete_fun_update; intros i'; destruct (decide ((inG_id i) = i')).
      { subst i'.
        rewrite discrete_fun_lookup_op. etrans.
        { eapply (allocs_alloc (cmra_transport inG_prf a) X (coPpick X)).
          { eapply coPpick_elem_of, coPset_infinite_finite; eauto. }
          { apply cmra_transport_valid. apply hwf. }
        }
        apply cmra_update_op.
        { done. }
        { rewrite /iRes_singleton discrete_fun_lookup_singleton; done. }
      }
      { rewrite discrete_fun_lookup_op /iRes_singleton discrete_fun_lookup_singleton_ne; eauto.
        rewrite right_id.
        etrans.
        eapply (allocs_auth_split (X ∖ {[coPpick X]}) {[coPpick X]}); try set_solver.
        { set_unfold; intros x; split; intros H; des; eauto.
          { destruct (decide (x = coPpick X)); eauto. }
          { subst; eapply coPpick_elem_of, coPset_infinite_finite; eauto. }
        }
        apply cmra_update_op_l.
      }
    }
    iModIntro; iFrame.
    iSplit; eauto.
    { iPureIntro. eapply difference_infinite, singleton_finite; eauto. }
    { iExists (coPpick X); rewrite own_eq /own_def; done. }
  Qed.

  Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
  Proof.
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
  Proof. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
  Lemma own_update_3 γ a1 a2 a3 a' :
    a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
  Proof.
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
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG A Σ}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.

  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  
  Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (own γ b1) (own γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.
(* TODO : Lemma own_unit A `{i : !inG (A:ucmra) Σ} γ : own_admin ⊢ |==> own_admin ∗ own γ (ε:A). *)


Section Own.
  Context `{Σ : GRA}.
  Implicit Types a b : Σ.
  Notation iProp Σ := (iProp Σ Σ).

  Local Ltac unseal := rewrite Own_eq /Own_def.

  Global Instance Own_ne : NonExpansive (@Own Σ).
  Proof. unseal. solve_proper. Qed.
  Global Instance Own_proper : Proper ((≡) ==> (⊣⊢)) (@Own Σ) := ne_proper _.

  Global Instance Own_core_persistent a : CoreId a → Persistent (@Own Σ a).
  Proof. unseal; apply _. Qed.

  Lemma Own_Upd a b (UPD : a ~~> b) : Own a ⊢ |==> Own b.
  Proof.
    unseal; iIntros "Hr1"; iPoseProof (uPred.bupd_ownM_update with "Hr1") as "Hr2"; eauto.
  Qed.

  Lemma Own_extends (a b : Σ) (EXT : a ≼ b) : Own b ⊢ Own a .
  Proof. unseal. apply uPred.ownM_mono. done. Qed.

  Lemma Own_op a b : Own (a ⋅ b) ⊣⊢ Own a ∗ Own b.
  Proof. by unseal; rewrite uPred.ownM_op. Qed.

  Lemma Own_valid a : Own a ⊢ ⌜✓ a⌝.
  Proof.
    unseal. iIntros "H". iDestruct (uPred.ownM_valid with "H") as "V".
    iEval (rewrite uPred.discrete_valid) in "V". iFrame "V".
  Qed.

  Lemma Own_wand_valid (a1 a2 : Σ) (WAND : Own a1 ⊢ |==> Own a2) (VALID : ✓ a1) : ✓ a2.
  Proof.
    eapply uPred.bupd_ownM_update_2; last by exact VALID.
    move: WAND; unseal; eauto.
  Qed.

  Lemma Own_bupd_split a P Q (IMPL : Own a ⊢ |==> P ∗ Q) (VALID : ✓ a) :
    ∃ a1 a2, (Own a ⊢ |==> Own a1 ∗ Own a2) ∧ (Own a1 ⊢ P) ∧ (Own a2 ⊢ Q).
  Proof.
    hexploit (@uPred.bupd_ownM_update_3 Σ); eauto.
    { move: IMPL; unseal; done. }
    intros [y [z [UPD [HP HQ]]]]; exists y, z; split; unseal; [done|split; done].
  Qed.

  Lemma Own_split a P Q (IMPL : Own a ⊢ P ∗ Q) (VALID : ✓ a) :
    ∃ a1 a2, a ≡ a1 ⋅ a2 ∧ (Own a1 ⊢ P) ∧ (Own a2 ⊢ Q).
  Proof.
    uPred.unseal_in IMPL; apply IMPL in VALID;
      last (unseal; uPred.unseal; exists ε; eauto; rewrite right_id //=).
    destruct VALID as [a1 [a2 [Ha VALID]]]; des; exists a1, a2; split; eauto; split; econs; intros x wfx Own;
      rewrite Own_eq /Own_def in Own; uPred.unseal_in Own; destruct Own as [? ->]; eauto using uPred_mono.
  Qed.

  Lemma Own_bupd_update a b (UPD : Own a ⊢ |==> Own b) :
    a ~~> b.
  Proof.
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
  Proof. move: DERIV; unseal => DERIV. eapply uPred.ownM_pure_soundness; eauto. Qed.

  Lemma Own_general_soundness a P (VALID : ✓ a) (DERIV : Own a ⊢ P) : uPred_holds P a.
  Proof. move: DERIV; unseal=> DERIV; eapply uPred.ownM_general_soundness; eauto. Qed.

  Lemma Own_general_completeness a P (HOLDS : uPred_holds P a) : Own a ⊢ P.
  Proof. split; unseal; uPred.unseal; i; eapply uPred_mono; eauto. Qed.

  Global Instance into_sep_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoSep (is_op a) Own_op. Qed.

  Global Instance into_and_Own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) Own_op bi.sep_and. Qed.

  Global Instance from_sep_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /FromSep -Own_op -is_op. Qed.

  (* TODO : Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_Own (a b1 b2 : Σ) :
    IsOp a b1 b2 → CombineSepAs (Own b1) (Own b2) (Own a) | 60.
  Proof. intros. by rewrite /CombineSepAs -Own_op -is_op. Qed.
  (* TODO : Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_Own (b1 b2 : Σ) :
    CombineSepGives (Own b1) (Own b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof.
    intros. rewrite /CombineSepGives -Own_op Own_valid.
    by apply : bi.persistently_intro.
  Qed.
  Global Instance from_and_Own_persistent (a b1 b2 : Σ) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (Own a) (Own b1) (Own b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) Own_op.
    destruct Hb; by rewrite bi.persistent_and_sep.
  Qed.

End Own.
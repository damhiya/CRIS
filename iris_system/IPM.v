From iris.algebra Require Import proofmode_classes functions gmap.
From iris.proofmode Require Export proofmode.
From CRIS.base_logic Require Export base_logic.
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

(* TODO : 1) refactor GRA.t
          2) move iProp and own to a separate file *)
Local Definition iRes_singleton {A Σ} {i : inG A Σ} (γ : gname) (a : A) : Σ :=
  discrete_fun_singleton (inG_id i) {[ γ := (cmra_transport (f_equal _  inG_prf) a) ]}.
Global Instance: Params (@iRes_singleton) 4 := {}.

(** * Definitions of resource ownership with ghost locations. *)
Local Definition own_def `{!inG A Σ} (γ : gname) (a : A) : iProp := uPred_ownM (iRes_singleton γ a).
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Global Arguments own {_ _ _} γ a.

(** * Definitions of resource ownership - for metatheoretical results only *)
Local Definition Own_def {Σ : GRA} (a : Σ) : iProp := uPred_ownM a.
Local Definition Own_aux : seal (@Own_def). Proof. by eexists. Qed.
Definition Own := Own_aux.(unseal).
Local Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).
Global Arguments Own {Σ} a.

Section properties.
  Context `{i : !inG A Σ}.
  Implicit Types a : A.

  Local Instance iRes_singleton_ne γ : NonExpansive (@iRes_singleton A Σ _ γ).
  Proof. by intros ????; apply discrete_fun_singleton_ne, singleton_ne, cmra_transport_ne. Qed.
  Local Instance iRes_singleton_proper γ :
    Proper ((≡) ==> (≡)) (@iRes_singleton A Σ _ γ) := ne_proper _.
  Local Lemma iRes_singleton_op γ a1 a2 :
    iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
  Proof.
    rewrite /iRes_singleton discrete_fun_singleton_op singleton_op cmra_transport_op.
    f_equiv. apply: singletonM_proper. done.
  Qed.
  Local Lemma iRes_singleton_validI γ a : ✓ (iRes_singleton γ a) ⊢@{@iProp Σ} ✓ a.
  Proof.
    rewrite /iRes_singleton.
    rewrite discrete_fun_validI (forall_elim (inG_id i)) discrete_fun_lookup_singleton.
    rewrite singleton_validI.
    trans (✓ cmra_transport (f_equal _ inG_prf) a : @iProp Σ)%I; last by destruct inG_prf.
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

(* TODO : Stuck here *)
(** ** Allocation *)
(* Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  intros Hupd. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x',
      x = inG_unfold x' ∧ ∃ a',
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' inG_fold).
    { apply inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply inG_unfold_validN. }
    by apply cmra_transport_updateP'.
  - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]].
    rewrite -(exist_intro a'). rewrite -persistent_and_sep.
    by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
Proof.
  intros. iIntros "?".
  iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
  { by apply cmra_update_updateP. }
  done.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. apply entails_wand. do 2 apply wand_intro_r. rewrite -!own_op. by iApply own_update. Qed.
End global.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_updateP {_ _} [_] _ _ _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{i : !inG Σ (A:ucmra)} γ : ⊢ |==> own γ (ε:A).
Proof.
  rewrite /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
  apply bupd_ownM_update, discrete_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (inG_unfold (cmra_transport inG_prf ε))).
  - apply (cmra_morphism_valid _), cmra_transport_valid, ucmra_unit_valid.
  - intros x. rewrite -(inG_unfold_fold x) -(cmra_morphism_op inG_unfold).
    f_equiv. generalize (inG_fold x)=> x'.
    destruct inG_prf=> /=. by rewrite left_id.
  - done.
Qed.

(** Big op class instances *)
Section big_op_instances.
  Context `{!inG Σ (A:ucmra)}.

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
  Context `{!inG Σ A}.
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
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
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


Section iProp.
  Local Definition Own_def `{!inG (a : Σ) : iProp := uPred_ownM a.
  Local Definition Own_aux : seal (@Own_def). Proof. by eexists. Qed.
  Definition Own := Own_aux.(unseal).
  Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).

  Definition OwnM {M : ucmra} `{!inG M Σ} (γ : gname) (a : M) : iProp := Own (GRA.embed a).

  (* Global Instance iProp_bi_bupd : BiBUpd iProp := uPred_bi_bupd Σ. *)

  Definition from_upred (P : uPred Σ) : iProp := P.
  Definition to_upred (P : iProp) : uPred Σ := P.

End iProp.
Global Arguments iProp : clear implicits.
Arguments OwnM : simpl never.

Local Ltac unseal := rewrite ?Own_eq /Own_def.

Section TEST.
  Context {Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Goal forall (P Q R : iProp) (PQ : P -∗ Q) (QR : Q -∗ R), P -∗ R.
  Proof.
    iIntros (P Q R PQ QR) "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q : iProp), ((|==> P) ∗ Q) -∗ (|==> Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.
End TEST.

Section class_instances.
  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Global Instance Own_ne : NonExpansive (@Own Σ).
  Proof. unseal. solve_proper. Qed.
  Global Instance Own_proper :
    Proper ((≡) ==> (⊣⊢)) (@Own Σ) := ne_proper _.

  Global Instance Own_core_persistent a : CoreId a → Persistent (@Own Σ a).
  Proof. rewrite !Own_eq /Own_def; apply _. Qed.

  Lemma Own_Upd r1 r2 (UPD : r1 ~~> r2) :
    Own r1 ⊢ |==> Own r2.
  Proof.
    unseal; iIntros "Hr1"; iPoseProof (uPred.bupd_ownM_update with "Hr1") as "Hr2"; eauto.
  Qed.

  Lemma Own_op (a1 a2 : Σ) :
    (Own (a1 ⋅ a2)) ⊣⊢ (Own a1 ∗ Own a2).
  Proof. unseal. by rewrite uPred.ownM_op. Qed.

  Lemma Own_valid (a : Σ) :
    Own a ⊢ ⌜✓ a⌝.
  Proof.
    unseal. iIntros "H". iDestruct (uPred.ownM_valid with "H") as "V".
    iEval (rewrite uPred.discrete_valid) in "V". iFrame "V".
  Qed.

  Lemma Own_wand_valid (a1 a2 : Σ) (WAND : Own a1 ⊢ |==> Own a2) (VALID : ✓ a1) :
    ✓ a2.
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
      last (rewrite IPM.Own_eq /IPM.Own_def; uPred.unseal; exists ε; eauto; rewrite right_id //=).
    destruct VALID as [a1 [a2 [Ha VALID]]]; des; exists a1, a2; split; eauto; split; econs; intros x wfx Own;
      rewrite IPM.Own_eq /IPM.Own_def in Own; uPred.unseal_in Own; destruct Own as [? ->]; eauto using uPred_mono.
  Qed.

  Lemma Own_bupd_update r1 r2 (UPD : Own r1 ⊢ |==> Own r2) :
    r1 ~~> r2.
  Proof.
    move: UPD; unseal; uPred.unseal; intros UPD.
    rewrite cmra_discrete_total_update; intros z wf.
    destruct UPD as [UPD]; exploit (UPD r1); ss.
    { eauto using cmra_valid_op_l. }
    { exists ε; rewrite right_id //. }
    { intros [x' H]; exploit (H z) => //=.
      intros [wfx'z r2x']; destruct r2x' as [x Hx']; rewrite Hx' in wfx'z.
      rewrite comm assoc in wfx'z; eapply cmra_valid_op_l in wfx'z; rewrite comm //.
    }
  Qed.

  Lemma Own_pure_soundness x P (VALID : ✓ x) (DERIV : Own x ⊢ ⌜P⌝) : P.
  Proof. move: DERIV; unseal => DERIV. eapply uPred.ownM_pure_soundness; eauto. Qed.

  Lemma Own_general_soundness x P (VALID : ✓ x) (DERIV : Own x ⊢ P) : uPred_holds P x.
  Proof. move: DERIV; unseal=> DERIV; eapply uPred.ownM_general_soundness; eauto. Qed.

  Lemma Own_general_completeness x P (HOLDS : uPred_holds P x) : Own x ⊢ P.
  Proof. split; unseal; uPred.unseal; i; eapply uPred_mono; eauto. Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoSep (is_op a) Own_op. Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) Own_op bi.sep_and. Qed.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /FromSep -Own_op -is_op. Qed.

  (* TODO : Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → CombineSepAs (Own b1) (Own b2) (Own a) | 60.
  Proof. intros. by rewrite /CombineSepAs -Own_op -is_op. Qed.
  (* TODO : Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_own (b1 b2 : Σ) :
    CombineSepGives (Own b1) (Own b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof.
    intros. rewrite /CombineSepGives -Own_op Own_valid.
    by apply : bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent (a b1 b2 : Σ) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (Own a) (Own b1) (Own b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) Own_op.
    destruct Hb; by rewrite bi.persistent_and_sep.
  Qed.

  Lemma OwnM_op (M : ucmra) `{@GRA.inG M Σ} (a1 a2 : M) :
    (OwnM (a1 ⋅ a2)) ⊣⊢ (OwnM a1 ∗ OwnM a2).
  Proof. by rewrite /OwnM -GRA.embed_add Own_op. Qed.

  Global Instance OwnM_ne `{@GRA.inG M Σ} : NonExpansive (@OwnM Σ M _).
  Proof. solve_proper. Qed.
  Global Instance OwnM_proper (M : ucmra) `{@GRA.inG M Σ} :
    Proper ((≡) ==> (⊣⊢)) (@OwnM Σ M _) := ne_proper _.

  Global Instance OwnM_core_persistent `{@GRA.inG M Σ} (a : M) :
    CoreId a → Persistent (OwnM a).
  Proof.
    rewrite /OwnM => CORE. apply Own_core_persistent.
    rewrite core_id_total -GRA.embed_core core_id_core //.
  Qed.

  Lemma OwnM_valid (M : ucmra) `{@GRA.inG M Σ} (m : M):
    OwnM m ⊢ ⌜✓ m⌝.
  Proof.
    iIntros "H". iDestruct (Own_valid with "H") as %WF.
    iPureIntro. eapply GRA.embed_wf. done.
  Qed.


  Global Instance into_sep_ownM (M : ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoSep (is_op a) OwnM_op. Qed.

  Global Instance into_and_ownM (M : ucmra) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) OwnM_op bi.sep_and. Qed.

  Global Instance from_sep_ownM (M : ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /FromSep -OwnM_op -is_op. Qed.

  (* TODO : Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_ownM (M : ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → CombineSepAs (OwnM b1) (OwnM b2) (OwnM a) | 60.
  Proof. intros. by rewrite /CombineSepAs -OwnM_op -is_op. Qed.
  (* TODO : Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_ownM (M : ucmra) `{@GRA.inG M Σ} (b1 b2 : M) :
    CombineSepGives (OwnM b1) (OwnM b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof.
    intros. rewrite /CombineSepGives -OwnM_op OwnM_valid.
    by apply : bi.persistently_intro.
  Qed.
  Global Instance from_and_ownM_persistent (M : ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) OwnM_op.
    destruct Hb; by rewrite bi.persistent_and_sep.
  Qed.

End class_instances.



Section ILEMMAS.
  Context `{Σ : GRA.t}.


  Lemma Own_extends
        (a b : Σ)
        (EXT : a ≼ b)
    :
      Own b ⊢ Own a
  .
  Proof. unseal. apply uPred.ownM_mono. done. Qed.

  Lemma Own_persistently (r : Σ) : Own r ⊢ <pers> Own (core r).
  Proof. unseal. apply uPred.persistently_ownM_core. Qed.

  Lemma OwnM_persistently {M : ucmra} `{@GRA.inG M Σ} (r : M) : OwnM r ⊢ <pers> OwnM (core r).
  Proof. rewrite /OwnM GRA.embed_core Own_persistently //. Qed.

  Lemma Own_unit : ⊢ Own (Σ:=Σ) ε.
  Proof. unseal. rewrite /bi_emp_valid. apply (uPred.ownM_unit emp). Qed.

  Lemma OwnM_unit {M : ucmra} `{@GRA.inG M Σ} : ⊢ OwnM ε.
  Proof. rewrite /OwnM GRA.embed_unit. apply Own_unit. Qed.

  Lemma OwnM_Upd `{M : ucmra} `{@GRA.inG M Σ}
        (r1 r2 : M)
        (UPD : r1 ~~> r2)
    :
      (OwnM r1) ⊢ (|==> (OwnM r2))
  .
  Proof. apply Own_Upd, GRA.embed_updatable, UPD. Qed.

  Lemma OwnM_extends `{M : ucmra} `{@GRA.inG M Σ}
        {a b : M}
        (EXT : a ≼ b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof. revert EXT. move=> [c ->]. by rewrite OwnM_op bi.sep_elim_l. Qed.
End ILEMMAS.

(* TODO : Move this to tactics *)
Ltac iOwnWf' H :=
  iPoseProof (OwnM_valid with H) as "%".

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  iOwnWf' H;
  match goal with
  | H0 : @valid _ _ _ |- _ => rename H0 into WF
  end
. *)

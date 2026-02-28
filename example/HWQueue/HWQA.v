Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI SchTactics.
Require Import IndefiniteDescription Sorted. (* require for prophecy *)
From iris.algebra Require Import numbers excl auth list gset gmap agree csum.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.

(** * Definition of the cameras we need for queues **************************)

Canonical Structure valO : ofe := leibnizO val.

Definition prod4R A B C D E :=
  prodR (prodR (prodR (prodR A B) C) D) E.

Definition oneshotUR := optionUR $ csumR (exclR unitR) (agreeR unitR).
Definition shot     : oneshotUR := Some $ Cinr $ to_agree ().
Definition not_shot : oneshotUR := Some $ Cinl $ Excl ().

Definition per_slot :=
  prod4R
    (* Unique token for the index. *)
    (optionUR $ exclR unitR)
    (* The location stored at our index, which always remains the same. *)
    (optionUR $ agreeR valO)
    (* Possible unique name for the index, only if being helped. *)
    (optionUR $ exclR natO)
    (* One shot witnessing the transition from pending to helped. *)
    oneshotUR
    (* One shot witnessing the physical writing of the value in the slot. *)
    oneshotUR.

(** * Definition of the cameras we need for queues **************************)

Definition eltsUR := authR $ optionUR $ exclR $ listO valO.
Definition contUR := csumR (exclR unitR) (agreeR (prodO natO natO)).
Definition slotUR := authR $ gmapUR nat per_slot.
Definition backUR := authR max_natUR.

Class hwqG `{!crisG Γ Σ α β τ Hsub Hinv} :=
  HwqG {
    hwq_arG   :: inG eltsUR Γ; (** Logical contents of the queue. *)
    hwq_contG :: inG contUR Γ; (** One-shot for contradiction states. *)
    hwq_slotG :: inG slotUR Γ; (** State data for used array slots. *)
    hwq_back  :: inG backUR Γ; (** Used to show that back only increases. *)
    hwq_help  :: inG (helpingR (val * gname) val) Γ; (** Added : helping resource *)
  }.

Definition hwqΓ : HRA := #[eltsUR; contUR; slotUR; backUR; helpingR (val * gname) val].
Global Instance subG_hwqG `{!crisG Γ Σ α β τ Hsub Hinb} : subG hwqΓ Γ → hwqG.
Proof. solve_inG. Qed.

(** * The specifiaction... **************************************************)

Section herlihy_wing_queue.

Context `{!crisG Γ Σ α β τ Hsub Hinb, !memGS, !hwqG, !prophGS}.
Context (N : namespace).
Notation iProp := (iProp Σ).
Implicit Types γe γc γs : gname.
Implicit Types sz : nat.
(* Implicit Types ℓ_ar ℓ_back : loc.
Implicit Types p : proph_id. *)
Implicit Types v : val.
Implicit Types pvs : list nat.

(** Operations for the CMRA representing the logical contents of the queue. *)

Lemma new_elts l : ⊢ o=> ∃ γe, own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iMod (own_alloc (● Excl' l ⋅ ◯ Excl' l)) as (γe) "[H● H◯]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γe. iFrame.
Qed.

Lemma sync_elts γe (l1 l2 : list valO) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H".
  iDestruct (own_valid with "H") as "H".
  by iDestruct "H" as %[?%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_elts γe (l1 l2 l : list valO) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) o==∗
    own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op.
  iMod (own_update with "H") as "$"; auto.
  by apply auth_update, option_local_update, exclusive_local_update.
Qed.

(* Fragmental part, made available during atomic updates. *)
Definition hwq_cont γe (elts : list valO) : iProp :=
  own γe (◯ Excl' elts).

Lemma hwq_cont_exclusive γe elts1 elts2 :
  hwq_cont γe elts1 -∗ hwq_cont γe elts2 -∗ False.
Proof.
  iIntros "H1 H2".
  by iCombine "H1 H2" gives %?%auth_frag_op_valid_1.
Qed.

(** Operations for the CMRA used to show that back only increases. *)

Definition back_value γb n := own γb (● MaxNat n).
Definition syn_back_value {n} γb i : GTerm.t n := sown γb (● MaxNat i).

Definition back_lower_bound γb n := own γb (◯ MaxNat n).
Definition syn_back_lower_bound {n} γb i : GTerm.t n := sown γb (◯ MaxNat i).

Lemma new_back : ⊢ o=> ∃ γb, back_value γb 0.
Proof.
  iMod (own_alloc (● MaxNat 0)) as (γb) "H●".
  - by rewrite auth_auth_valid.
  - by iExists γb.
Qed.

Lemma back_incr γb n :
  back_value γb n o==∗ back_value γb (S n).
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat (S n))). simpl. lia.
Qed.

Lemma back_snapshot γb n :
  back_value γb n o==∗ back_value γb n ∗ back_lower_bound γb n.
Proof.
  iIntros "H●". rewrite -own_op. iMod (own_update with "H●") as "$"; auto.
  by apply auth_update_alloc, max_nat_local_update.
Qed.

Lemma back_le γb n1 n2 :
  back_value γb n1 -∗ back_lower_bound γb n2 -∗ ⌜n2 ≤ n1⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. iPureIntro.
  apply auth_both_valid_discrete in Hvalid as [Ha%max_nat_included _]. done.
Qed.

(* Stores a lower bound on the [i2] part of any contradiction that
   has arised or may arise in the future. *)
Definition i2_lower_bound γi n := back_value γi n.
Definition syn_i2_lower_bound {n} γi i := @syn_back_value n γi i.

(* Witness that the [i2] part of any (future or not) contradicton is
   greater than [n]. *)
Definition no_contra_wit γi n := back_lower_bound γi n.

Lemma i2_lower_bound_update γi n m :
  n ≤ m →
  i2_lower_bound γi n ==∗ i2_lower_bound γi m.
Proof.
  iIntros (?) "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat m)). simpl. lia.
Qed.

Lemma i2_lower_bound_snapshot γi n :
  i2_lower_bound γi n ==∗ i2_lower_bound γi n ∗ no_contra_wit γi n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

(** Operations for the one-shot CMRA used for contradiction states. *)

(** Element for "no contradiction yet". *)
Definition no_contra γc :=
  own γc (Cinl (Excl ())).
Definition syn_no_contra {n} γc : GTerm.t n :=
  sown γc (Cinl (Excl ())).

(** Element witnessing a contradiction [(i1, i2)]. *)
Definition contra γc (i1 i2 : nat) :=
  own γc (Cinr (to_agree (i1, i2))).
Definition syn_contra {n} γc (i1 i2 : nat) : GTerm.t n :=
  sown γc (Cinr (to_agree (i1, i2))).

Lemma new_no_contra : ⊢ o=> ∃ γc, no_contra γc.
Proof. by apply own_alloc. Qed.

Lemma to_contra i1 i2 γc : no_contra γc ==∗ contra γc i1 i2.
Proof. apply bi.entails_wand, own_update. by apply cmra_update_exclusive. Qed.

Lemma contra_not_no_contra i1 i2 γc :
  no_contra γc -∗ contra γc i1 i2 -∗ False.
Proof. iIntros "HnoC HC". iCombine "HnoC HC" gives %[]. Qed.

Lemma contra_agree i1 i2 i1' i2' γc :
  contra γc i1 i2 -∗ contra γc i1' i2' -∗ ⌜i1' = i1 ∧ i2' = i2⌝.
Proof.
  iIntros "HC HC'". iCombine "HC HC'" gives %Hwf.
  iPureIntro. apply to_agree_op_inv_L in Hwf. by inversion Hwf.
Qed.

Global Instance contra_persistent γc i1 i2 : Persistent (contra γc i1 i2).
Proof. apply own_core_persistent. by rewrite /CoreId. Qed.

(** Operations for the state data. *)

Inductive state :=
  (** Help was requested (element not committed). *)
  | Pend : nat → state
  (** Help has been provided (element committed). *)
  | Help : nat → state
  (** The enqueue operation known it has been committed. *)
  | Done :       state.

Local Instance state_inhabited : Inhabited state.
Proof. constructor. refine Done. Qed.

(** Data associated to each slot. The four components are:
     - the location that is being written in the slot,
     - a possible name for a stored proposition containing the postcondition
       of the atomic update of the enqueue happening for the slot (used only
       in case of helping),
     - state of the slot,
     - [true] if a value was physically written in the slot. *)
Definition slot_data : Type := val * state * bool.

Implicit Types slots : gmap nat slot_data.

Definition update_slot i f slots :=
  match slots !! i with
  | Some d => <[i := f d]> (delete i slots)
  | None   => slots
  end.

Definition val_of (data : slot_data) : val :=
  match data with (l, _, _) => l end.

Definition state_of (data : slot_data) : state :=
  match data with (_, s, _) => s end.

Definition name_of (data : slot_data) : option nat :=
  match state_of data with Pend γ => Some γ | Help γ => Some γ | _ => None end.

Definition was_written (data : slot_data) : bool :=
  match data with (_, _, b) => b end.

Definition was_committed (data : slot_data) : bool :=
  match state_of data with Pend _ => false | _ => true end.

Definition set_written (data : slot_data) : slot_data :=
  match data with (l, s, _) => (l, s, true) end.

Definition set_written_and_done (data : slot_data) : slot_data :=
  match data with (l, _, _) => (l, Done, true) end.

Definition to_helped (γ : nat) (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Help γ, w) end.

Definition to_done (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Done, w) end.

Definition physical_value (data : slot_data) : val :=
  match data with (l, _, w) => if w then l else Vint 0 end.

Lemma val_of_set_written d : val_of (set_written d) = val_of d.
Proof. by destruct d as [[l s] w]. Qed.

Lemma was_written_set_written d : was_written (set_written d) = true.
Proof. by destruct d as [[l s] w]. Qed.

Lemma state_of_set_written d : state_of (set_written d) = state_of d.
Proof. by destruct d as [[l s] w]. Qed.

Definition of_slot_data (data : slot_data) : per_slot :=
  match data with
  | (l, s, w) =>
    let name := match s with Pend γ => Excl' γ | Help γ => Excl' γ | Done => None end in
    let comm := if was_committed data then shot else not_shot in
    let wr := if w then shot else not_shot in
    (Excl' (), Some (to_agree l), name, comm, wr)
  end.

Lemma of_slot_data_valid d : ✓ of_slot_data d.
Proof. by destruct d as [[l []] []]. Qed.

(* The (unique) token for slot [i]. *)
Definition slot_token γs i :=
  own γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).
Definition syn_slot_token {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).

(* A witness that the location enqueued in slot [i] is [l]. *)
Definition slot_val_wit γs i l :=
  own γs (◯ {[i := (None, Some (to_agree l), None, None, None)]} : slotUR).
Definition syn_slot_val_wit {n} γs i l : GTerm.t n :=
  sown γs (◯ {[i := (None, Some (to_agree l), None, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been committed. *)
Definition slot_committed_wit γs i :=
  own γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).
Definition syn_slot_committed_wit {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).

Definition slot_name_tok γs i γ :=
  own γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).
Definition syn_slot_name_tok {n} γs i γ : GTerm.t n :=
  sown γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been written. *)
Definition slot_written_wit γs i :=
  own γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).
Definition syn_slot_written_wit {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).

(* A token proving that the enqueue in slot [i] has not been commited. *)
Definition slot_pending_tok γs i :=
  own γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).
Definition syn_slot_pending_tok {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).

(* A token proving that no value has been written in slot [i]. *)
Definition slot_writing_tok γs i :=
  own γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).
Definition syn_slot_writing_tok {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).

(* Initial slot data, with not allocated slots. *)
Lemma new_slots : ⊢ o=> ∃ γs, own γs (● ∅).
Proof.
  iMod (own_alloc (● ∅ ⋅ ◯ ∅)) as (γs) "[H● _]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γs. iFrame.
Qed.

(* Allocate a new slot with data [d] at the fresh index [i]. *)
Lemma alloc_slot γs slots (i : nat) (d : slot_data) :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := d]> slots)) : slotUR) ∗
    own γs (◯ {[i := of_slot_data d]} : slotUR).
Proof.
  iIntros (Hi) "H". rewrite -own_op fmap_insert.
  iMod (own_update with "H") as "$"; auto. apply auth_update_alloc.
  apply alloc_singleton_local_update.
  - by rewrite lookup_fmap Hi.
  - apply of_slot_data_valid.
Qed.

Lemma alloc_done_slot γs slots i l :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := (l, Done, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_committed_wit γs i ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma alloc_pend_slot γs slots i l γ :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := (l, Pend γ, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_pending_tok γs i ∗
    slot_name_tok γs i γ ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma use_val_wit γs slots i l :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i l -∗
  ⌜val_of <$> slots !! i = Some l⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ Ha] _] _] _]; simpl in Ha. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ H2] _] _] _]; simpl in H2.
    assert (Some (to_agree l) ≡ Some (to_agree dl)) as Hwf by by transitivity b2.
    apply Some_equiv_inj, to_agree_inj in Hwf. rewrite /equiv in Hwf. inv Hwf. done.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    assert (Some (to_agree l) ≼ Some (to_agree dl)) as Hb by set_solver.
    apply option_included in Hb.
    destruct Hb as [Hb|[a [b (H11 & H12 & H13)]]]; first done.
    simplify_eq. destruct H13 as [Hb|Hb].
    + by apply to_agree_inj in Hb.
    + by apply to_agree_included in Hb.
Qed.

Lemma use_name_tok γs slots i γ :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ -∗
  ⌜name_of <$> slots !! i = Some (Some γ)⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Ha.
  iPureIntro. apply auth_both_valid_discrete in Ha as [Ha%singleton_included_l _].
  destruct Ha as [ps (Hb & H2%option_included)]. rewrite lookup_fmap in Hb.
  destruct (slots !! i) as [d|]; last by inversion Hb. simpl in Hb.
  inversion_clear Hb.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into Hb end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Hb as [[[[_ _] Hb] _] _]; simpl in Hb. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] H2] _] _]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≡ Excl' γ') as Ha by by transitivity b3.
      inversion Ha as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ Excl' γ') as Ha by by transitivity b3.
      inversion Ha as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ None) as Ha by by transitivity b3.
      inversion Ha.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≼ Excl' γ') as Ha by set_solver.
      by apply Excl_included in Ha.
    + assert (Excl' γ ≼ Excl' γ') as Ha by set_solver.
      by apply Excl_included in Ha.
    + assert (Excl' γ ≼ None) as Ha by set_solver.
      exfalso. apply option_included in Ha as [Ha|Ha]; first done.
      destruct Ha as [a [b (H11 & H12 & H13)]]. by simplify_eq.
Qed.

Lemma shot_not_equiv_not_shot : shot ≢ not_shot.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_equiv_not_shot' e : shot ≢ not_shot ⋅ e.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  destruct e as [e|]; first destruct e.
  - rewrite -Some_op -Cinl_op in Ha.
    inversion Ha as [x y Habsurd|]; inversion Habsurd.
  - rewrite -Some_op in Ha. compute in Ha.
    inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
  - inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
  - inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_included_not_shot : ¬ shot ≼ not_shot.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  apply option_included in Ha. destruct Ha as [Ha|Ha]; first done.
  destruct Ha as [a [b (Ha & H2 & [H3|H3])]].
  - simplify_eq. by inversion H3.
  - simplify_eq. apply csum_included in H3.
    destruct H3 as [H3|H3]; first done. destruct H3 as [H3|H3].
    + destruct H3 as [a [b (Ha & H2 & H3)]]. by inversion Ha.
    + destruct H3 as [a [b (Ha & H2 & H3)]]. by inversion H1.
Qed.

Lemma use_committed_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_committed_wit γs i -∗
  ⌜was_committed <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with Hwf: of_slot_data d ≡ ps |- _ => rename Hwf into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ _] _] Ha]]; simpl in Ha. f_equal.
  destruct (was_committed (dl, ds, dw)); first done. exfalso.
  destruct H23 as [H3|H3].
  - destruct H3 as [[[[_ _] _] H3] _]; simpl in H3.
    apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H3 as [H3 _]; simpl in H3.
    apply prod_included in H3 as [_ H3]; simpl in H3.
    apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_written_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_written_wit γs i -∗
  ⌜was_written <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with Hwf: of_slot_data d ≡ ps |- _ => rename Hwf into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5]. destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ _] _] _] Ha]; simpl in Ha. f_equal.
  destruct dw; first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] _] H2]; simpl in H2.
    exfalso. apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [_ H2]; simpl in H2.
    exfalso. apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_writing_tok γs i slots :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i set_written slots) : slotUR) ∗
    slot_written_wit γs i.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H". rewrite -own_op.
  iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  apply Some_equiv_inj in H1_1.
  assert (w = false) as ->.
  { destruct w; [ exfalso | done ].
    apply Some_included in H1_2 as [H1_2|H1_2].
    - assert ((None, None, None, None, not_shot)
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by apply shot_not_equiv_not_shot.
    - destruct H1_2 as [f H1_2].
      assert ((None, None, None, None, not_shot) ⋅ f
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by eapply shot_not_equiv_not_shot'. }
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. eapply (singleton_local_update _ i).
  { by rewrite lookup_fmap Hi. }
  rewrite /set_written. apply prod_local_update; first done. simpl.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma writing_tok_not_written γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i -∗
    ⌜was_written <$> slots !! i = Some false⌝.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H".
  iDestruct (own_valid with "H") as %Hvalid%auth_both_valid_discrete.
  iPureIntro. destruct Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|]; last by inversion H1_1.
  apply Some_equiv_inj in H1_1. simpl. f_equal. destruct w; last done.
  exfalso. apply Some_included in H1_2 as [H1_2|H1_2].
  - assert ((None, None, None, None, not_shot)
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by apply shot_not_equiv_not_shot.
  - destruct H1_2 as [f H1_2].
    assert ((None, None, None, None, not_shot) ⋅ f
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by eapply shot_not_equiv_not_shot'.
Qed.

Lemma None_op {A : cmra} : (None : optionUR A) ⋅ None = None.
Proof. done. Qed.

Lemma use_pending_tok γs i γ slots :
  state_of <$> slots !! i = Some (Pend γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_pending_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i (to_helped γ) slots) : slotUR) ∗
    slot_committed_wit γs i.
Proof.
  iIntros (Hlookup) "Hs● Htok". iCombine "Hs● Htok" as "H".
  rewrite -own_op. iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  simpl in Hlookup. inversion Hlookup; subst s.
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. repeat rewrite pair_op.
  eapply (singleton_local_update _ i). { by rewrite lookup_fmap Hi. }
  rewrite /to_helped. repeat rewrite None_op.
  repeat apply prod_local_update; try done.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma slot_token_exclusive γs i :
  slot_token γs i -∗ slot_token γs i -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Ha. iPureIntro.
  move:Ha =>/auth_frag_valid Ha. apply singleton_valid in Ha.
  by repeat apply pair_valid in Ha as [Ha _]; simpl in Ha.
Qed.

Lemma helped_to_done_aux γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR) ∗
    own γs (◯ {[i := (None, None, None, None, None)]} : slotUR).
Proof.
  iIntros (Ha) "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. rewrite -own_op.
  iApply (own_update with "H"). apply auth_update. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:Hd; last by inversion Ha.
  rewrite insert_delete_insert fmap_insert. eapply singleton_local_update.
  { by rewrite lookup_fmap Hd /=. }
  destruct d as [[dl ds] dw]. inversion Ha; subst ds; simpl.
  repeat apply prod_local_update; try done. simpl.
  apply delete_option_local_update. apply _.
Qed.

Lemma helped_to_done γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR).
Proof.
  iIntros (?) "H1 H2". by iMod (helped_to_done_aux with "H1 H2") as "[H _]".
Qed.

Lemma val_wit_from_auth γs i l slots :
  val_of <$> slots !! i = Some l →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> slots) : slotUR) ∗
    slot_val_wit γs i l.
Proof.
  iIntros (Ha) "H". rewrite -own_op. iApply (own_update with "H").
  apply auth_update_dfrac_alloc; first apply _.
  assert (∃ d, slots !! i = Some d) as [d Hlookup].
  { destruct (slots !! i) as [d|]; inversion Ha. by exists d. }
  apply singleton_included_l. rewrite lookup_fmap. rewrite Hlookup /=.
  exists (of_slot_data d). split; first done.
  apply Some_included. right. destruct d as [[dl ds] dw]. simpl.
  repeat (apply prod_included; split; simpl);
    try by (apply option_included; left).
  apply option_included; right. exists (to_agree l), (to_agree dl).
  repeat (split; first done). left.
  rewrite Hlookup /= in Ha. by inversion Ha.
Qed.

(** * Prophecy abstractions *************************************************)
(* Fixpoint proph_extract sz (l : list (nat * bool)) (deq : gset nat) : list nat :=
  match l with
  | (i, true) :: l =>
      if (decide (i ∉ deq ∧ i < sz))
      then proph_extract sz l ({[i]} ∪ deq) ++ [i]
      else proph_extract sz l deq
  | (i, false) :: l => proph_extract sz l deq
  | [] => []
  end.

Lemma elem_of_proph_extract sz l deq i :
  i ∈ proph_extract sz l deq ↔ i < sz ∧ i ∉ deq ∧ ∃ idx, l !! idx = Some (i, true).
Proof.
  revert l i deq sz; induction l as [|[i' [|]] l]; intros i deq sz.
  { rewrite elem_of_nil; split; [ss|intros [? [? [? H1]]]]; rewrite lookup_nil // in H1. }
  { s; case_decide as H1.
    { split.
      { rewrite elem_of_app; intros [[? [? [idx Hidx]]]%IHl|?%elem_of_list_singleton].
        { splits; eauto; [set_solver|exists (S idx); ss]. }
        subst; splits; des; eauto; exists O; ss.
      }
      intros [? [? [idx Hidx]]]; destruct (decide (i = i')); subst.
      { rewrite elem_of_app; right; apply elem_of_list_singleton; auto. }
      destruct idx; ss; clarify.
      rewrite elem_of_app; left; rewrite IHl; splits; des; eauto.
      set_solver.
    }
    rewrite IHl; split; intros [? [? [idx Hidx]]]; splits; eauto; [exists (S idx); ss|].
    destruct idx; ss; clarify; first naive_solver; eauto.
  }
  s; rewrite IHl; split; intros [? [? [idx Hidx]]]; splits; eauto; [exists (S idx); ss|].
  destruct idx; ss; clarify; first naive_solver; eauto.
Qed. *)

Definition init (obs_seq : nat → (nat * bool)) (i : nat) :
  { x : option nat |
    match x with
    | Some x => obs_seq x = (i, true) ∧ ∀ (x' : nat), obs_seq x' = (i, true) → x ≤ x'
    | None => ∀ x, obs_seq x ≠ (i, true)
    end
  }.
Proof.
  apply constructive_indefinite_description.
  set (P := λ (n : nat), obs_seq n = (i, true)).
  pose proof (dec_inh_nat_subset_has_unique_least_element P) as HP.
  destruct (classic (∃ x, P x)) as [[x Hx]|Hex].
  { hexploit HP; [intros ?; eapply classic|eauto|].
    intros [y [[Hy Hu] ?]]; exists (Some y); split; eauto.
  }
  exists None; intros ??; eauto.
Defined.

Local Instance le_fst_dec : RelDecision (λ (x1 x2 : nat * nat), x1.1 ≤ x2.1).
Proof. ii; apply _. Defined.

Definition proph_full_data (obs_seq : nat → nat * bool) (l : list nat) : list nat :=
  (sorting.merge_sort (λ x1 x2, x1.1 ≤ x2.1)
    (omap
      (λ i, match init obs_seq i with | exist _ (Some x) _ => Some (x, i) | _ => None end) l)).*2.

Definition proph_data (obs_seq : nat → nat * bool) (l : list nat) (deq : gset nat) : list nat :=
  filter (.∉ deq) (proph_full_data obs_seq l).

Lemma elem_of_proph_full_data obs_seq l i :
  (∃ x, obs_seq x = (i, true)) → i ∈ l →
  i ∈ proph_full_data obs_seq l.
Proof.
  intros [x Hx] Hi. rewrite /proph_full_data sorting.merge_sort_Permutation.
  destruct (init obs_seq i) as [[m|] Hm] eqn : Hinit ; last (by exfalso; naive_solver).
  rewrite elem_of_list_fmap; exists (m, i); split; ss.
  rewrite elem_of_list_omap; exists i; split; ss; rewrite Hinit //.
Qed.

Lemma proph_data_deq obs_seq sz deq : ∀ i, i ∈ deq → i ∉ proph_data obs_seq (seq 0 sz) deq.
Proof. intros i Hideq Hiproph%elem_of_list_filter; set_solver. Qed.

Lemma proph_data_sz obs_seq sz deq : ∀ i, i ∈ proph_data obs_seq (seq 0 sz) deq → i < sz.
Proof.
  intros i; rewrite /proph_data elem_of_list_filter; intros [Hnin Hi].
  rewrite /proph_full_data sorting.merge_sort_Permutation elem_of_list_fmap in Hi.
  destruct Hi as [[x i2] [a Hi]]; ss; subst i2.
  rewrite elem_of_list_omap in Hi; destruct Hi as [x' [Hx Hx2]].
  destruct (init obs_seq x') as [[?|] ?] eqn : Hx3; clarify.
  apply elem_of_seq in Hx; lia.
Qed.

Lemma proph_data_NoDup obs_seq sz deq :
  NoDup (proph_data obs_seq (seq 0 sz) deq ++ elements deq).
Proof.
  apply NoDup_app; split.
  { apply NoDup_filter. rewrite /proph_full_data sorting.merge_sort_Permutation.
    induction sz; first (by s; apply NoDup_nil).
    rewrite seq_S /= omap_app fmap_app; apply NoDup_app; splits; ss; last first.
    { case_match; ss; auto using NoDup_singleton. by econs. }
    intros x [[i x'] [Hx' Hx]]%elem_of_list_fmap; simpl in Hx'; subst x'.
    rewrite elem_of_list_omap in Hx; destruct Hx as [i' [Hi' Hi'2]].
    repeat case_match; ss; clarify; ss; auto using not_elem_of_nil.
    apply elem_of_seq in Hi'; intros ?%elem_of_list_singleton; subst; lia.
  }
  split; last apply NoDup_elements.
  intros ? ? ?%elem_of_elements; eapply proph_data_deq; eauto.
Qed.

Lemma length_firstn {X} (obs_seq : nat → X) n : length (Prophecy.firstn obs_seq n) = n.
Proof. induction n; ss; lia. Qed.

Program Definition hwq_prophecy : Prophecy.t := {|
  Prophecy.Pro := nat → (nat * bool);
  Prophecy.Obs := nat * bool;
  Prophecy.consistent := λ l p, l = Prophecy.firstn p (length l);
  Prophecy.obs_default := inhabitant;
|}.
Next Obligation.
  intros obs_seq; exists obs_seq; intros i.
  rewrite length_firstn //.
Qed.

(* Wrapper for the Iris [proph] proposition, using our data abstraction. *)
Definition hwq_proph (blk : nat) sz (deq : gset nat) pvs :=
  (∃ p rs, has_proph ("hwq", (Vptr (blk, 0%Z))↑↑) (existT hwq_prophecy (p, rs)) ∗
  ⌜pvs = proph_data p (seq 0 sz) deq⌝)%I.
Definition syn_hwq_proph {n} (blk : nat) sz (deq : gset nat) pvs : GTerm.t n :=
  (∃ (p : τ{nat -> nat * bool}) (rs : τ{list (nat * bool)}),
    syn_has_proph ("hwq", (Vptr (blk, 0%Z))↑↑) (existT hwq_prophecy (p, rs)) ∗
    ⌜pvs = proph_data p (seq 0 sz) deq⌝)%SAT.

  (* Fixpoint proph_data sz (deq : gset nat) (rs : list (val * val)) : list nat :=
  match rs with
  | (PairV _ #true , LitV (LitInt i)) :: rs =>
    if decide (0 ≤ i < sz)%Z then
      let i := Z.to_nat i in
      if decide (i ∈ deq) then
        []
      else
        i :: proph_data sz ({[i]} ∪ deq) rs
    else []
  | (PairV _ #false, LitV (LitInt i)) :: rs =>
    if decide (0 ≤ i < sz)%Z then
      proph_data sz deq rs
    else
      []
  | _                               => []
  end. *)

Definition block  : Type := nat * list nat.
Definition blocks : Type := list block.

(* A block is valid if it follows the structure described above. *)
Definition block_valid slots (b : block) :=
  slots !! b.1 = None ∧
  ∀ i, i ∈ b.2 → was_committed <$> (slots !! i) = Some false.

Fixpoint glue_blocks (b : block) (i : nat) (bs : blocks) : blocks :=
  match bs with
  | []               => [b]
  | (j, pends) :: bs => if decide (i = j) then (b.1, b.2 ++ i :: pends) :: bs
                        else b :: glue_blocks (j, pends) i bs
  end.

Fixpoint flatten_blocks bs : list nat :=
  match bs with
  | []               => []
  | (i, pends) :: bs => i :: pends ++ flatten_blocks bs
  end.

Lemma blocks_elem1 b blocks :
  b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros Ha. induction blocks as [|b' blocks IH]; first by inversion Ha.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. by apply elem_of_list_here.
  - destruct b' as [b'_u b'_bs]. simpl.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH. apply elem_of_cons in Ha as [Ha|Ha]; last done.
    by rewrite Ha in Hb_not_b'.
Qed.

Lemma blocks_elem2 b blocks :
  b ∈ blocks → ∀ i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros Ha. induction blocks as [|b' blocks IH]; first by inversion Ha.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. intros i Hi. simpl in *.
    apply elem_of_list_further. apply elem_of_app. by left.
  - destruct b' as [b'_u b'_bs]. simpl. intros i Hi.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH; last done. apply elem_of_cons in Ha as [Ha|Ha]; last done.
    by rewrite Ha in Hb_not_b'.
Qed.

Lemma glue_blocks_valid slots i b_unused b_pendings blocks l γ :
  slots !! i = None →
  b_unused ≠ i →
  NoDup (b_unused :: b_pendings ++ flatten_blocks blocks) →
  (∀ b : block, b ∈ (b_unused, b_pendings) :: blocks → block_valid slots b) →
  ∀ b, b ∈ glue_blocks (b_unused, b_pendings) i blocks → block_valid (<[i:=(l, Pend γ, false)]> slots) b.
Proof using Type*.
  intros Hi. revert b_unused b_pendings.
  induction blocks as [|[b_u b_ps] blocks IH];
    intros b_unused b_pendings Hb_unused_not_i HND Hblocks_valid [b_u' b_ps'] Hb.
  - apply Hblocks_valid in Hb as Hvalid.
    apply elem_of_list_singleton in Hb. simplify_eq.
    destruct Hvalid as (Hvalid1 & Hvalid2). split.
    + by rewrite lookup_insert_ne.
    + simpl in *. intros k Hk. specialize (Hvalid2 _ Hk) as Hvalid_k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      * by rewrite lookup_insert.
      * by rewrite lookup_insert_ne.
  - simpl in Hb. destruct (decide (i = b_u)) as [->|Hi_not_b_u].
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2).
        assert ((b_u, b_ps) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid'%Hblocks_valid by set_solver.
        destruct Hvalid' as (Hvalid1' & Hvalid2').
        split; simpl.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. apply elem_of_app in Hk as [Hk|Hk].
           *** assert (k ≠ b_u) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & HND & _). apply HND in Hk.
                 simpl in Hk. by apply not_elem_of_cons in Hk as (Hk & _). }
               rewrite lookup_insert_ne; last done. by apply Hvalid2.
           *** apply elem_of_cons in Hk as [->|Hk]; first by rewrite lookup_insert.
               assert (b_u ≠ k) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
                 apply NoDup_cons in HND as (HND & _).
                 apply not_elem_of_app in HND as (HND & _).
                 intros ->. apply HND, Hk. }
               rewrite lookup_insert_ne; last done. by apply Hvalid2'.
      * assert ((b_u', b_ps') ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). rewrite /block_valid.
        assert (b_u ≠ b_u') as HNeq1.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by apply blocks_elem1 in Hb. }
        rewrite lookup_insert_ne; last done. split; first done.
        intros k Hk. simpl in Hk.
        assert (b_u ≠ k) as HNeq2.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by eapply blocks_elem2 in Hb. }
        rewrite lookup_insert_ne; last done. by apply Hvalid2.
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). split.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. simpl in *.
           assert (k ≠ i) as HNEq.
           { intros ->. apply Hvalid2 in Hk. rewrite Hi in Hk. by inversion Hk. }
           rewrite lookup_insert_ne; last done. by apply Hvalid2.
      * eapply IH; last done; first done.
        { apply NoDup_cons in HND as (_ & HND).
          by apply NoDup_app in HND as (_ & _ & HND). }
        intros b' Hb'.
        assert (b' ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hb'_valid%Hblocks_valid by set_solver. done.
Qed.

(* Contradiction status: either there is a contradiction going on with
   the given indices, or there is no contradiction. In the latter case
   the prophecy has well-formed pending blocks as a suffix. *)
Inductive cont_status :=
  | WithCont : nat → nat → cont_status
  | NoCont   : blocks    → cont_status.

Local Instance cont_status_inhabited : Inhabited cont_status.
Proof. constructor. refine (NoCont []). Qed.

Lemma initial_block_valid b pvs :
  b ∈ map (λ i : nat, (i, [])) pvs → block_valid ∅ b.
Proof.
  intros Ha. induction pvs as [|i pvs IH].
  - by inversion Ha.
  - simpl in Ha. apply elem_of_cons in Ha as [->|Ha].
    + split; first by apply lookup_empty. intros k Hk. by inversion Hk.
    + apply IH, Ha.
Qed.

Lemma flatten_blocks_initial pvs :
  pvs = flatten_blocks (map (λ i : nat, (i, [])) pvs).
Proof.
  induction pvs as [|i pvs IH]; first done.
  simpl. f_equal. by apply IH.
Qed.

Lemma flatten_blocks_glue b bs i :
  flatten_blocks (b :: bs) = flatten_blocks (glue_blocks b i bs).
Proof.
  revert b.
  induction bs as [|[b_u' b_ps'] bs IH]; intros [b_u b_ps]; first done.
  simpl. destruct (decide (i = b_u')) as [->|HNEq]; simpl.
  - by rewrite -app_assoc.
  - by rewrite -IH.
Qed.

Lemma flatten_blocks_mem1 blocks :
  ∀b, b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  apply elem_of_cons in Hb as [->|Hb]; first by apply elem_of_list_here.
  simpl. apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

Lemma flatten_blocks_mem2 blocks :
  ∀b, b ∈ blocks → ∀i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  intros k Hk. apply elem_of_cons in Hb as [->|Hb]; simpl.
  - apply elem_of_list_further. apply elem_of_app. by left.
  - apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

(** * Some definitions and lemmas about array content manipulation **********)

Definition array_get slots (deqs : gset nat) i :=
  match slots !! i with
  | None   => Vint 0
  | Some d => if decide (i ∈ deqs) then Vint 0
              else physical_value d
  end.

Fixpoint array_content n slots deqs :=
  match n with
  | 0 => []
  | S n   => array_content n slots deqs ++ [array_get slots deqs n]
  end.

Lemma length_array_content sz slots deqs :
  length (array_content sz slots deqs) = sz.
Proof.
  induction sz as [|sz IH]; first done.
  by rewrite /= length_app Nat.add_comm /= IH.
Qed.

Lemma array_content_lookup sz slots deqs i :
  i < sz →
  array_content sz slots deqs !! i = Some (array_get slots deqs i).
Proof.
  intros ?. induction sz as [|sz IH]; first lia.
  destruct (decide (i = sz)) as [->|Hi_not_sz]; simpl.
  - rewrite lookup_app_r length_array_content; last done.
    by rewrite Nat.sub_diag /=.
  - rewrite lookup_app_l; first (apply IH; by lia).
    rewrite length_array_content. lia.
Qed.

Lemma array_content_empty sz :
  array_content sz ∅ ∅ = replicate sz (Vint 0).
Proof.
  induction sz as [|sz IH]; first done.
  rewrite replicate_S_end /= IH. done.
Qed.

Lemma array_content_NONEV sz i d slots deqs :
  physical_value d = Vint 0 → slots !! i = None → i ∉ deqs →
  array_content sz (<[i:=d]> slots) deqs = array_content sz slots deqs.
Proof.
  intros Ha H2 H3. induction sz as [|sz IH]; first done.
  rewrite /= /array_get. destruct (decide (i = sz)) as [->|Hi_not_sz].
  - rewrite lookup_insert H2 decide_False; last done. by rewrite IH Ha.
  - rewrite lookup_insert_ne; last done. by rewrite IH.
Qed.

Lemma array_content_is_Some sz i slots deqs :
  i < sz →
  is_Some (array_content sz slots deqs !! i).
Proof.
  intros ?. apply lookup_lt_is_Some. by rewrite length_array_content.
Qed.

Lemma array_content_ext sz slots1 slots2 deqs :
  (∀ i, i < sz → array_get slots1 deqs i = array_get slots2 deqs i) →
  array_content sz slots1 deqs = array_content sz slots2 deqs.
Proof.
  induction sz as [|sz IH]; intros Ha; first done.
  simpl. rewrite Ha; last by lia. f_equal. apply IH.
  intros i Hi. apply Ha. by lia.
Qed.

Lemma array_content_more_deqs sz slots deqs i :
  sz ≤ i →
  array_content sz slots ({[i]} ∪ deqs) = array_content sz slots deqs.
Proof.
  intros ?. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
  destruct (decide (sz ∈ deqs)) as [Helem|Hnot_elem].
  - rewrite decide_True; [ done | by set_solver ].
  - rewrite decide_False; [ done | .. ].
    apply not_elem_of_union. split; last done.
    apply not_elem_of_singleton. by lia.
Qed.

Lemma array_content_update_slot_ge sz slots deqs f i :
  sz ≤ i →
  array_content sz slots deqs = array_content sz (update_slot i f slots) deqs.
Proof.
  intros ?. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get /update_slot.
  destruct (slots !! i) as [d|]; last done.
  rewrite insert_delete_insert. rewrite lookup_insert_ne; [ done | by lia ].
Qed.

Lemma array_content_dequeue sz i slots deqs :
  i < sz →
  i ∉ deqs →
  array_content sz slots ({[i]} ∪ deqs) = <[i:=(Vint 0)]> (array_content sz slots deqs).
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i ? H2; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0 (Vint 0)).
    rewrite /= /array_get. destruct (slots !! i) as [d|].
    + rewrite decide_True; last by set_solver. f_equal.
      rewrite array_content_more_deqs; [ done | by lia ].
    + f_equal. rewrite array_content_more_deqs; [ done | by lia ].
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done ]. f_equal.
    rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
    destruct (decide (sz ∈ deqs)) as [?|?].
    * rewrite decide_True; [ done | by set_solver ].
    * rewrite decide_False; [ done | by set_solver ].
Qed.

Lemma array_content_set_written sz i (l : val) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written slots) deqs.
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i ? H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

(* FIXME similar to previous lemma. Share stuff? *)
Lemma array_content_set_written_and_done sz i (l : val) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written_and_done slots) deqs.
Proof.
  revert i. induction sz as [|sz IH]; intros i ? H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

Lemma update_slot_lookup i f slots :
  update_slot i f slots !! i = f <$> slots !! i.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  by rewrite lookup_insert.
Qed.

Lemma update_slot_lookup_ne i k f slots :
  i ≠ k →
  update_slot i f slots !! k = slots !! k.
Proof.
  intros ?. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  rewrite lookup_insert_ne; last done.
  by rewrite lookup_delete_ne.
Qed.

Lemma update_slot_update_slot i f g slots :
  update_slot i f (update_slot i g slots) = update_slot i (f ∘ g) slots.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite lookup_insert. repeat rewrite insert_delete_insert.
    rewrite insert_insert. done.
  - rewrite HEq. done.
Qed.

Definition get_value slots (deqs : gset nat) i : val :=
  match slots !! i with
  | None   => inhabitant
  | Some d => val_of d
  end.

Definition map_get_value_not_in_pref i d pref slots deqs :
  was_written d = false →
  i ∉ pref →
  map (get_value (<[i:=d]> slots) deqs) pref = map (get_value slots deqs) pref.
Proof.
  intros Hd. induction pref as [|k pref IH]; intros Hi; first done.
  rewrite /= IH; last by set_solver. f_equal. rewrite /get_value.
  rewrite lookup_insert_ne; first done. set_solver.
Qed.

(** * Definition of the main ************************************************)

(*
When a contradiction is going on, we have [cont = WithCont i1 i2] where:
 - [i1] is the index reserved by the enqueue operation the initiated the
   contradiction,
 - [i2] is the first index in the prophecy that was not yet reserved for
   an enqueue operation (when the contradiction was initiated).
*)

Definition per_slot_own γe γs i d :=
  (slot_val_wit γs i (val_of d) ∗
  (if was_written d then slot_written_wit γs i else emp) ∗
  match state_of d with
  (* | Pend γ => slot_pending_tok γs i ∗
              ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ enqueue_AU γe (val_of d) Q *)
  | Pend γ => slot_pending_tok γs i ∗ helping_token γ (val_of d, γe)
  (* | Help γ => slot_committed_wit γs i ∗ ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ ▷ Q *)
  | Help γ => slot_committed_wit γs i ∗ helping_done γ Vundef
  | Done   => slot_committed_wit γs i ∗ slot_token γs i
  end)%I.
Definition syn_per_slot_own {n} γe γs i d : GTerm.t n :=
  (syn_slot_val_wit γs i (val_of d) ∗
  (if was_written d then syn_slot_written_wit γs i else emp) ∗
  match state_of d with
  (* | Pend γ => syn_slot_pending_tok γs i ∗
              ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ enqueue_AU γe (val_of d) Q *)
  | Pend γ => syn_slot_pending_tok γs i ∗ syn_helping_token _ γ (val_of d, γe)
  (* | Help γ => syn_slot_committed_wit γs i ∗ ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ ▷ Q *)
  | Help γ => syn_slot_committed_wit γs i ∗ syn_helping_done _ γ Vundef
  | Done   => syn_slot_committed_wit γs i ∗ syn_slot_token γs i
  end)%SAT.
Instance per_slot_own_red {n} γe γs i d :
  SLRed n (syn_per_slot_own γe γs i d) (per_slot_own γe γs i d).
Proof. solve_sl_red. Qed.

Definition syn_inv_hwq
    {n} (sz : nat) (γb γi γe γc γs : gname) blk : GTerm.t n :=
  (∃ X : τ{gmap nat _}, syn_helping_auth _ (1/2) X)%SAT ∨
  (∃ (back  : τ{nat})                (** Physical value of [q.back]. *)
     (pvs   : τ{list nat})           (** Full contents of the prophecy. *)
     (pref  : τ{list nat})           (** Commit prefix of the prophecy *)
     (rest  : τ{list val})           (** Logical queue after commit prefix. *)
     (cont  : τ{cont_status})        (** Contradiction or prophecy suffix. *)
     (slots : τ{gmap nat slot_data}) (** Per-slot data for used indices. *)
     (deqs  : τ{gset nat}),          (** Dequeued indices. *)
  (** Physical data. *)
  (blk, 0%Z) ↦ Vint sz ∗ (blk, 1%Z) ↦ Vint back ∗
  ([∗ list] i ↦ v ∈ array_content sz slots deqs, (blk, i + 2)%Z ↦ v) ∗
  (** Logical contents of the queue and prophecy contents. *)
  syn_back_value γb back ∗
  syn_i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  sown γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  sown γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  syn_hwq_proph blk sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, syn_per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => syn_no_contra γc | WithCont i1 i2 => syn_contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = Vint 0) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ Vint 0 ∧
     pref ++ [i2] `prefix_of` pvs
  end⌝)%SAT.

Definition inv_hwq `{!inG (helpingR (val * gname) val) Γ}
    (sz : nat) (γb γi γe γc γs : gname) blk : iProp :=
  (∃ X, helping_auth (1/2) X) ∨
  (∃ (back  : nat)                (** Physical value of [q.back]. *)
     (pvs   : list nat)           (** Full contents of the prophecy. *)
     (pref  : list nat)           (** Commit prefix of the prophecy *)
     (rest  : list val)           (** Logical queue after commit prefix. *)
     (cont  : cont_status)        (** Contradiction or prophecy suffix. *)
     (slots : gmap nat slot_data) (** Per-slot data for used indices. *)
     (deqs  : gset nat),          (** Dequeued indices. *)
  (** Physical data. *)
  (blk, 0%Z) ↦ Vint sz ∗ (blk, 1%Z) ↦ Vint back ∗
  ([∗ list] i ↦ v ∈ array_content sz slots deqs, (blk, i + 2)%Z ↦ v) ∗
  (** Logical contents of the queue and prophecy contents. *)
  back_value γb back ∗
  i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  own γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  own γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  hwq_proph blk sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => no_contra γc | WithCont i1 i2 => contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = Vint 0) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ Vint 0 ∧
     pref ++ [i2] `prefix_of` pvs
  end⌝)%I.

Global Instance inv_hwq_red {n} sz γb γi γe γc γs blk :
  SLRed n (syn_inv_hwq sz γb γi γe γc γs blk) (inv_hwq sz γb γi γe γc γs blk).
Proof. solve_sl_red. Qed.

(* Definition inv_hwq sz γb γi γe γc γs ℓ_ar ℓ_back p : iProp :=
  (∃ (back  : nat)                (** Physical value of [q.back]. *)
     (pvs   : list nat)           (** Full contents of the prophecy. *)
     (pref  : list nat)           (** Commit prefix of the prophecy *)
     (rest  : list loc)           (** Logical queue after commit prefix. *)
     (cont  : cont_status)        (** Contradiction or prophecy suffix. *)
     (slots : gmap nat slot_data) (** Per-slot data for used indices. *)
     (deqs  : gset nat),          (** Dequeued indices. *)
  (** Physical data. *)
  ℓ_back ↦ #back ∗ ℓ_ar ↦∗ (array_content sz slots deqs) ∗
  (** Logical contents of the queue and prophecy contents. *)
  back_value γb back ∗
  i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  own γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  own γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  hwq_proph p sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => no_contra γc | WithCont i1 i2 => contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = NONEV) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ NONEV ∧
     pref ++ [i2] `prefix_of` pvs
  end⌝)%I.
 *)

Definition is_hwq (n : nat) sz γe v : iProp :=
  ∃ γb γi γc γs blk, ⌜v = Vptr (blk, 0%Z)⌝ ∗ inv n N (syn_inv_hwq sz γb γi γe γc γs blk).
  (* (∃ γb γi γc γs ℓ_ar ℓ_back p,
    ⌜v = (#sz, #ℓ_ar, #ℓ_back, #p)%V⌝ ∗
    inv N (inv_hwq sz γb γi γe γc γs ℓ_ar ℓ_back p))%I. *)

(** * Some useful instances *************************************************)

Local Instance blocks_match_persistent (bs : blocks) γc i1 :
  Persistent (match bs with
              | []           => True
              | (i2, _) :: _ => contra γc i1 i2
              end)%I.
Proof. destruct bs as [|[i2 _] _]; apply _. Qed.

Local Instance cont_match_persistent cont γc :
  Persistent (match cont with
              | NoCont _       => True
              | WithCont i1 i2 => contra γc i1 i2
              end)%I.
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

Local Instance contra_timeless cont γc :
  Timeless (match cont with
            | NoCont _       => no_contra γc
            | WithCont i1 i2 => contra γc i1 i2
            end).
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

(** * Some important lemmas for the specification of [enqueue] **************)

Definition get_values (slots : gmap nat slot_data) (p : list nat) :=
  fold_right (λ i acc, match val_of <$> slots !! i with
                       | None   => acc
                       | Some l => l :: acc end) [] p.

Definition get_values_not_in n ps d s :
  n ∉ ps → get_values (<[n:=d]> s) ps = get_values s ps.
Proof.
  intros ?. induction ps as [|p ps IH]; first done. simpl.
  assert (n ≠ p) as Hn_not_p by set_solver.
  rewrite lookup_insert_ne; last done.
  rewrite IH; first done. set_solver.
Qed.

Definition helped (p : list nat) (i : nat) d :=
  match state_of d with
  | Pend γ => if decide (i ∈ p) then
                Some (val_of d, Help γ, was_written d)
              else
                Some d
  | _      => Some d
  end.

Lemma is_Some_helped (p : list nat) i d : is_Some (helped p i d).
Proof.
  rewrite /helped. destruct (state_of d); try by eexists.
  destruct (decide (i ∈ p)); by eexists.
Qed.

Lemma map_imap_helped_nil slots : map_imap (helped []) slots = slots.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite /helped /= HEq. by destruct (state_of d).
  - by rewrite /= HEq.
Qed.

Lemma annoying_lemma_1 slots deqs pref i l b_pendings :
  (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧ k ∉ deqs) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) pref =
  map (get_value slots deqs) pref.
Proof.
  intros Hpref HND.
  induction pref as [|pref_hd pref IH]; first done.
  assert (NoDup (pref ++ i :: b_pendings)) as HND_IH.
  { simpl in HND. apply NoDup_cons in HND as [_ HND]. done. }
  assert (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧
                          k ∉ deqs) as Hpref_IH.
  { intros k Hk. by apply Hpref, elem_of_list_further, Hk. }
  rewrite /= IH; try done. clear IH HND_IH Hpref_IH. f_equal.
  assert (i ≠ pref_hd) as Hi_not_pref_hd.
  { simpl in HND. apply NoDup_cons in HND as (HND & _).
    apply not_elem_of_app in HND as (_ & HND).
    by apply not_elem_of_cons in HND as (HND & _). }
  rewrite /get_value map_lookup_imap lookup_insert_ne; last done.
  destruct (slots !! pref_hd) as [[[lp sp] wp]|]; last done.
  destruct sp; try done. rewrite /= /helped /=.
  rewrite decide_False; first done.
  simpl in HND. apply NoDup_cons in HND as (HND & _).
  apply not_elem_of_app in HND as (_ & HND).
  by apply not_elem_of_cons in HND as (_ & HND).
Qed.

Lemma annoying_lemma_2 slots deqs pref i l b_pendings :
  block_valid slots (i, b_pendings) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) b_pendings =
  get_values (<[i:=(l, Done, false)]> slots) b_pendings.
Proof.
  intros (Hvalid_1 & Hvalid_2) HND.
  induction b_pendings as [|p ps IH]; first done. simpl in *.
  assert (i ≠ p) as Hi_not_p.
  { intros ->. apply NoDup_app in HND as (_ & _ & HND).
    apply NoDup_cons in HND as (HND & _). by set_solver +HND. }
  rewrite lookup_insert_ne; last done.
  assert (p ∈ p :: ps) as Hcomm%Hvalid_2 by set_solver.
  destruct (slots !! p)
    as [[[lp sp] wp]|] eqn:Hslots_p; [ f_equal | by inversion Hcomm ].
  - rewrite /= map_imap_insert /helped /= /get_value.
    rewrite lookup_insert_ne; last done. rewrite map_lookup_imap Hslots_p /=.
    destruct sp; try done. rewrite decide_True; [ done | by set_solver ].
  - rewrite -IH; first last; try done.
    { apply NoDup_app in HND as (HND1 & HND2 & HND3).
      apply NoDup_app. split; first done. split.
      - intros e He. apply HND2 in He. apply not_elem_of_cons.
        split; by set_solver +He.
      - apply NoDup_cons in HND3 as (HND3_1 & HND3_2).
        apply NoDup_cons. split; first by set_solver +HND3_1.
        apply NoDup_cons in HND3_2 as (HND3_2_1 & HND3_2_2). done. }
    { intros k Hk. by apply Hvalid_2, elem_of_list_further, Hk. }
    apply map_ext_in. intros k Hk.
    rewrite /get_value map_lookup_imap map_lookup_imap.
    assert (i ≠ k) as Hi_not_k.
    { intros ->. apply NoDup_app in HND as (_ & _ & HND).
      apply NoDup_cons in HND as (HND & _).
      apply not_elem_of_cons in HND as (_ & HND).
      by apply HND, elem_of_list_In, Hk. }
    rewrite lookup_insert_ne; last done.
    assert (k ∈ p :: ps) as Hk_p_ps
      by by apply elem_of_list_further, elem_of_list_In.
    specialize (Hvalid_2 _ Hk_p_ps) as Hcomm_k.
    destruct (slots !! k) as [[[lk sk] wk]|]; last by inversion Hcomm_k.
    destruct sk; try done. rewrite /= /helped /=.
    rewrite decide_True; last done.
    rewrite decide_True; [ done | by apply elem_of_list_In ].
Qed.
End herlihy_wing_queue.

(* Specification of the queue operations *)
Module HWQA. Section HWQA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !memGS, !prophGS, !hwqG}.
  Context (N : namespace).

  Definition scopes : list string := [].

  Definition new_queue : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition new_queue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, sz) : nat * nat),
        ((λ arg, ⌜arg = [Vint sz]↑ ∧ 0 < 8 * (2 + sz) < Z.to_nat modulus_64⌝),
         (λ ret, ∃ (q : val) (γq : gname), ⌜ret = (q↑)⌝ ∗ is_hwq N n sz γq q ∗ hwq_cont γq []))))%I.

  Definition enqueue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, sz, γq, q, l) : nat * nat * gname * val * val),
        ((λ arg, ∃ blk ofs, ⌜l = Vptr (blk, ofs) ∧ arg = [q; l]↑⌝ ∗ is_hwq N n sz γq q),
         (λ ret, True))))%I.

  Definition dequeue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, q, γq) : nat * val * gname),
        ((λ arg, ⌜arg = [q]↑⌝),
         (λ ret, True))))%I.

  Definition enqueue : Any.t → itree crisE Any.t :=
    atomic_body enqueue_spec
      (λ '(_, (_, γq, _, l)) _,
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        trigger (Guarantee (hwq_cont γq (ls ++ [l])));;;
        Ret Vundef↑).

  Definition dequeue : Any.t → itree crisE Any.t :=
    atomic_body dequeue_spec
      (λ '(_, (_, γq)) _, 
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        l <- trigger (Choose valO);;
        trigger (Guarantee (∃ ls', ⌜ls = l :: ls'⌝ ∗ hwq_cont γq ls'));;;
        Ret (l↑)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (fsp_some new_queue_spec, cfunU new_queue));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End HWQA. End HWQA.

Module HWQM. Section HWQM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (N : namespace) (mn : string).

  Notation jobID := (val * gname)%type. (* idx * gname *)
  Notation retID := val.

  Definition jobCode : jobID → itree crisE retID :=
    λ '(v, γq),
      ls <- trigger (Take (list valO));;
      trigger (Assume (hwq_cont γq ls));;;
      trigger (Guarantee (hwq_cont γq (ls ++ [v])));;;
      Ret Vundef.

  Definition scopes : list string := [].

  Definition enqueue : Any.t → itree crisE Any.t :=
    atomic_body (HWQA.enqueue_spec N)
      (λ '(_, (_, γq, _, l)) _,
        ret <- trigger (Call (Helping.run mn) (l, γq)↑);;
        ITree.iter (λ _,
          'b : bool <- trigger (Choose bool);;
          if b 
          then trigger (Call (Helping.help mn) (()↑));;; Ret (inl ()) 
          else Ret (inr ())) ();;;
        Ret ret).

  Definition dequeue : Any.t → itree crisE Any.t :=
    atomic_body (HWQA.dequeue_spec N)
      (λ '(_, (_, γq)) _, 
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        l <- trigger (Choose valO);;
        trigger (Guarantee (∃ ls', ⌜ls = l :: ls'⌝ ∗ hwq_cont γq ls'));;;
        Ret (l↑)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (fsp_some (HWQA.new_queue_spec N), cfunU (HWQA.new_queue)));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod (SchA.sp ∅ (↑N)) Mod.
End HWQM. End HWQM.

Module HWQPM. Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !hwqG, !memGS, !prophGS}.
  Context (mn : string).
  Context (N : namespace) (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (IstHelp mn st_src st_tgt ∗
    ∃ (X : gset val),
      free_id (λ x, (x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type) ∗
      [∗ set] x ∈ X,
        □ ∃ blk ofs nx, ⌜x = Vptr (blk, ofs)⌝ ∗
          ∀ X, helping_auth 1 X =| nx, ↑N |={↑N, ∅}=∗ ∃ v, (blk, ofs) ↦ v)%I.
  Definition IstFull : ist_type Σ :=
    IstProd (IstSB (Mod.scopes (HWQP.t mn) ++ Mod.scopes (HelpingDummy.t mn)) Ist) IstEq.
  Lemma Ist_help : Ist_helping mn IstFull.
  Proof.
    iIntros (??) "[% [% [% [% [[-> ->] [[%Ha [[% [[-> ->] ?]] ?]] ->]]]]]]".
    iModIntro; iExists _, _; iFrame; iSplit; auto.
    iIntros (?) "$ !>"; iExists _, _, _, _; repeat iSplit; eauto.
    iPureIntro. set_solver.
  Qed.

  Notation sp := (SchA.sp ∅ (↑N)).
  Notation HWQM := (HWQM.t N mn).
  Notation HWQP := (HWQP.t mn).
  Notation HelpOn := (HelpingOn.t mn HWQM.jobCode sp).
  Notation HelpDummy := (HelpingDummy.t mn).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mn ∅).

  Lemma simF_new_queue : 
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.new_queue).
  Proof.
    iStartSim. s.
    steps_l. destruct _q as [[mtid stid] [n sz]]; s.
    iDestruct "ASM" as "[TID [-> [-> %Hsz]]]".
    steps_l. steps_r.
    rewrite /HWQP.new_queue /HWQA.new_queue.
    steps_r. sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    iApply wsim_mem_alloc; [try by simpl_map|ss|try lia|].
    replace (Z.to_nat (2 + sz)) with (2 + sz) by lia.
    iIntros (blk); rewrite replicate_add big_sepL_app; iIntros "[[sz [back _]] ar]". steps_r.
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    store_r "sz". sch_yield_ir "IST" "TID".
    store_r "back". sch_yield_ir "IST" "TID".
    replace sz with ((sz - sz) + sz) at 1 by lia. rewrite replicate_add.
    replace (replicate (sz - sz) Vundef) with (replicate (sz - sz) (Vint 0))
      by rewrite Nat.sub_diag //=.
    rewrite -[X in ITree.iter _ X](Nat.sub_diag sz).
    assert (sz ≤ sz) as Hle by lia; revert Hle.
    generalize sz at 1 4 5 10 as i; intros i Hle.
    iInduction i as [|i] forall (Hle st_src st_tgt).
    { rewrite Nat.sub_0_r /= app_nil_r.
      unfold_iter_r. steps_r. sch_yield_ir "IST" "TID".
      rewrite Nat2Z.id Nat.ltb_irrefl. steps_r. sch_yield_ir "IST" "TID".
      iDestruct "IST" as "[% [% [% [% [[-> ->] [[% IST] ->]]]]]]".
      iDestruct "IST" as "[IST [%X [free alloc]]]".
      destruct (decide (Vptr (blk, 0%Z) ∈ X)) as [HblkX|HblkX].
      { iPoseProof (big_sepS_elem_of_acc with "alloc") as "[#acc _]"; auto using HblkX.
        iDestruct "acc" as "[% [% [% [% acc]]]]"; clarify.
        iDestruct "IST" as "[% [? IST]]".
        iMod ("acc" with "IST") as "[% acc2]".
        by iPoseProof (mem_points_to_singleton_valid with "acc2 sz") as "%".
      }
      iMod (free_id_split _ ("hwq", ((Vptr (blk, 0%Z))↑↑)) with "free") as "[tok free]".
      { split; ss. rewrite SAny.upcast_downcast //. }
      steps_r. inline_r. force_r (_, hwq_prophecy). forces_r. iSplitL "tok".
      { repeat iSplit; first iPureIntro; ss. }
      steps_r. iDestruct "GRT" as "[-> [%p [-> Proph]]]".
      (* invariant construction *)
      iMod new_back as (γb) "Hb●".
      iMod new_back as (γi) "Hi●". (* FIXME not about back. *)
      iMod (new_elts []) as (γe) "[He● He◯]".
      iMod new_no_contra as (γc) "HC".
      iMod new_slots as (γs) "Hs●".
      iMod (inv_alloc (syn_inv_hwq sz γb γi γe γc γs blk) (n:=n) (S n) _ _ N
        with "[ar sz back Proph Hb● Hi● He● HC Hs●]") as "#InvN"; auto.
      { pose (pvs := proph_data p (seq 0 sz) ∅).
        pose (cont := NoCont (map (λ i, (i, [])) pvs)).
        rewrite inv_hwq_red. iRight.
        iExists 0, pvs, [], [], cont, ∅, ∅.
        rewrite array_content_empty fmap_empty /=.
        iFrame. iSplitL "ar".
        { iApply (big_sepL_impl with "ar"); iModIntro; iIntros (k?).
          replace (k + 2)%Z with (Z.of_nat (S (S k))) by lia. iIntros "% ? //=".
        }
        repeat (iSplit; first done). iPureIntro.
        repeat split_and; try done.
        - intros i. split; intros Hi; [ by lia | by inversion Hi].
        - intros e He. set_solver.
        - apply proph_data_NoDup.
        - apply proph_data_sz.
        - intros b. apply initial_block_valid.
        - simpl. apply flatten_blocks_initial. }
      sch_yield_l. force_l (Vptr (blk, 0%Z)). forces_l. iFrame.
      repeat iSplit; first auto.
      { iExists _; iSplit; first auto. iExists _, _, _, _, _; iSplit; eauto. }
      iIst "IST" with "[-]".
      { iExists _, _, _, _. repeat iSplit; des; eauto.
        iFrame "IST". iExists (X ∪ {[Vptr (blk, 0%Z)]}). 
        iSplitL "free".
        { iApply (free_id_iff with "free").
          intros i; case_decide; subst; ss.
          { rewrite SAny.upcast_downcast; split; ss.
            rewrite elem_of_union; intros [_ a]; apply a; right; set_solver+.
          }
          split; intros [? ?]; split; try done.
          { case_match; set_solver. }
          case_match; auto. rewrite elem_of_union; intros [|?%elem_of_singleton].
          { set_solver. }
          subst; destruct i; ss; hss.
        }
        rewrite big_sepS_union; last set_solver.
        iFrame. rewrite big_sepS_singleton; iModIntro.
        iExists _, _, (S n); iSplit; eauto.
        clear. iIntros (X) "X".
        iInv "InvN" as "[[% X2]|[% [% [% [% [% [% [% [$ ?]]]]]]]]]" "close".
        { iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
        iApply fupd_mask_intro; eauto. solve_ndisj.
      }
      step. iFrame. auto.
    }
    (* inductive case *)
    unfold_iter_r. steps_r. sch_yield_ir "IST" "TID".
    destruct Nat.ltb eqn : Hltb; first clear Hltb; last first.
    { apply Nat.ltb_ge in Hltb; lia. }
    rewrite length_replicate.
    iPoseProof (big_sepL_insert_acc _ _ (sz - (S i)) with "ar") as "[↦ ar]".
    { rewrite lookup_app_r length_replicate // Nat.sub_diag //=. }
    steps_r.
    replace (0 + 2 + (sz - S i)%nat)%Z with (Z.of_nat (2 + (sz - S i))) by lia.
    store_r "↦". iPoseProof ("ar" with "↦") as "ar".
    replace (sz - S i) with (length (replicate (sz - S i) (Vint 0)) + 0) at 1
      by (rewrite length_replicate; lia).
    rewrite insert_app_r /=.
    replace (S (sz - S i)) with (sz - i) by lia.
    iApply ("IHi" with "[] [ar] sz back IST TID"); first (iPureIntro; lia).
    replace (sz - i) with ((sz - S i) + 1) by lia; rewrite replicate_add /=.
    rewrite -(assoc app) //=.
  Qed.

  Lemma big_lemma γe γs (ls : list val) slots (p : list nat)
    msks mtid stid n sz blk γc γi γb fl_s fl_t r g ps pt st_src st_tgt :
  fl_s !! fid (Helping.help mn) =
    Some (Some (SB.sandbox_body
      (msk_scp (HelpingOn.scopes mn) msk_true,
      (SModTr.trans_fnsem (SchA.sp ∅ (↑N))
        (None, HelpingOn.help mn HWQM.jobCode (SchA.sp ∅ (↑N))))))) →
  NoDup p →
  (∀ i, i ∈ p → was_committed <$> slots !! i = Some false) →
  (□ inv n N (syn_inv_hwq sz γb γi γe γc γs blk)) -∗
  (∀ reqmap, helping_auth (1/2) reqmap o==∗ IstFull st_src st_tgt) -∗
  Tid mtid stid -∗
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) -∗
  own γe (● (Excl' ls)) -∗
    wsim fl_s fl_t IstFull (↑N, ↑N) r g unit unit
      (λ rs rt, winv (↑N, ↑N) ∗
        own γs (● (of_slot_data <$> map_imap (helped p) slots) : slotUR) ∗
        ([∗ map] i ↦ d ∈ map_imap (helped p) slots, per_slot_own γe γs i d) ∗
        own γe (● (Excl' (ls ++ get_values slots p))) ∗
        Tid mtid stid ∗ (∀ reqmap, helping_auth (1/2) reqmap o==∗ IstFull rs.1 rt.1))
      ps pt 
      (st_src, SB.sandbox msks (SModTr.trans (SchA.sp ∅ (↑N))
        (ITree.iter (λ _,
          'b : bool <- trigger (Choose bool);;
          if b 
          then trigger (Call (Helping.help mn) (()↑));;; Ret (inl ()) 
          else Ret (inr ())) ())))
      (st_tgt, Ret ()).
  Proof.
    intros Hf. revert p. iIntros (p).
    iInduction p as [|e p] "IH" forall (st_src st_tgt ps pt slots ls);
      iIntros (HNoDup Ha) "#Hinv Hist TID Hs● Hbig He●".
    { unfold_iter_l. norm_l. case_match; steps_l; ss.
      force_l false. steps_l. step.
      rewrite /= app_nil_r map_imap_helped_nil. iFrame.
    }
    unfold_iter_l. norm_l. case_match; steps_l; ss. force_l true. steps_l.
    destruct orb; ss. destruct msks; steps_l; ss.
    inline_l. steps_l.
    assert (∀ i : nat, i ∈ p → was_committed <$> slots !! i = Some false) as Ha1.
    { intros i Hi. apply Ha. apply elem_of_list_further, Hi. }
    assert (was_committed <$> slots !! e = Some false) as Ha2.
    { apply Ha, elem_of_list_here. }
    assert (∃ ln γn wn, slots !! e = Some (ln, Pend γn, wn)) as Hn.
    { destruct (slots !! e) as [[[ln sn] wn]|]; last by inversion Ha2.
      (destruct sn as [γn|γn|]; last by idtac); by exists ln, γn, wn. }
    apply NoDup_cons in HNoDup. destruct HNoDup as [Hn_not_in_ps HNoDup].
    destruct Hn as [l [γ [w Hn]]].
    assert (slots = <[e:=(l, Pend γ, w)]> (delete e slots)) as Hs.
    { by rewrite insert_delete_insert insert_id //. }
    rewrite [in ([∗ map] _ ↦ _ ∈ slots, _)%I]Hs.
    iDestruct (big_sepM_insert with "Hbig") as "[Hbig_n Hbig]"; first by apply lookup_delete.
    iDestruct "Hbig_n" as "[Hval_wit_n [Hwritten_n [Hpending_tok_n H]]]".
    iApply (wsim_helping_help2 with "TID H"); [exact Ist_help|ss|..].
    iExists (S n). iInv "Hinv" as "Inv" "Close".
    iDestruct "Inv" as "[[% ●Help] | [% [% [% [% [% [% [% [_ [_ [_ [_ [_ [_ [He●2 _]]]]]]]]]]]]]]]";
      last first.
    { iCombine "Hs● He●2" gives %WF%auth_auth_op_valid; ss. }
    iMod ("Hist" with "●Help") as "$".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "_"].
    steps_l. iRename "ASM" into "He◯".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (ls ++ [l]) with "He● He◯") as "[He● He◯]".
    force_l; iFrame "He◯". steps_l. step. iFrame. iSplit; first done.
    clear_st. iIntros (st_src2 st_tgt2) "Done IST".
    iMod (Ist_help with "IST") as "[%st_src' [%reqmap [-> [Help● HelpClose]]]]".
    iPoseProof (helping_auth_split (1/2) with "Help●") as "[Help● Help●2]"; first done.
    iMod ("Close" with "[Help●]") as "_"; first iFrame. { set_solver. }
    iApply fupd_mask_intro; first solve_ndisj; iIntros "_ TID". steps_l.
    iMod (use_pending_tok with "Hs● Hpending_tok_n")
      as "[Hs● Hcommitted_wit_n]"; first by rewrite Hn.
    iDestruct (big_sepM_insert _ (delete e slots) e (l, Help γ, w)
      with "[Done Hval_wit_n Hwritten_n Hcommitted_wit_n Hbig]")
      as "Hbig"; first by apply lookup_delete.
    { iClear "IH". iFrame "Hbig". rewrite /per_slot_own /=. iFrame. }
    rewrite insert_delete_insert /update_slot Hn insert_delete_insert.
    assert (∀ i : nat, i ∈ p → was_committed <$> <[e:=(l, Help γ, w)]> slots !! i = Some false) as HHH.
    { intros i Hi. rewrite lookup_insert_ne; [ by apply Ha1 | by set_solver ]. }
    iSpecialize ("IH" $! _ st_tgt2 true false _ _ HNoDup HHH with "Hinv [Help●2 HelpClose]").
    { iIntros (?) "A"; iPoseProof ("Help●2" with "A") as "Help●".
      iApply "HelpClose"; iFrame.
    }
    iPoseProof ("IH" with "TID Hs● Hbig He●") as "IH".
    add_ret_l; add_ret_r. iApply wsim_bind. iSplitL "IH"; first iApply "IH". s.
    iIntros (????) "[W [Hs● [Hbig [He● [TID ?]]]]]". step.
    assert (map_imap (helped p) (<[e:=(l, Help γ, w)]> slots)
            = map_imap (helped (e :: p)) slots) as Heq.
    { apply map_eq. intros i. destruct (decide (i = e)) as [->|Hi_not_n].
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert Hn /=.
        rewrite /helped /=. rewrite decide_True; first done. set_solver.
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_ne; last done.
        destruct (slots !! i) as [[[li si] wi]|]; last done. simpl.
        rewrite /helped /=. destruct si; try done.
        destruct (decide (i ∈ e :: p)).
        + rewrite decide_True; first done. set_solver.
        + rewrite decide_False; first done. set_solver. }
    rewrite Heq. iFrame. rewrite -app_assoc /= get_values_not_in //; iFrame.
  Qed.

  Lemma simF_enqueue : 
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.enqueue).
  Proof.
    iStartSim.
    rewrite /HWQM.enqueue /HWQI.enqueue /atomic_body.
    steps_l. destruct _q as [[mtid stid] [[[[n sz] γq] q] v]].
    iDestruct "ASM" as "[TID [_ [%vblk [%vofs [[-> ->] #INV]]]]]". steps_r.
    iDestruct "INV" as (γb γi γc γs blk ->) "#Inv".
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    (* Open the invariant to perform the increment. *)
    iInv "Inv" as "[[% X2]|HInv]" "Close".
    { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
      iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz Hinv]".
    load_r "H_sz". iMod ("Close" with "[H_sz Hinv]") as "_".
    { iRight. iFrame. }
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    rewrite /MemHdr.faa. steps_r.
    clear pvs pref rest slots deqs back cont.
    iInv "Inv" as "[[% X2]|HInv]" "Close".
    { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
      iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    load_r "H_back". store_r "H_back".
    assert (back + 1 = S back)%Z as -> by lia.
    iMod (back_incr with "Hb●") as "Hb●".
    iAssert (i2_lower_bound γi match cont with
                              | WithCont _ i2 => i2
                              | NoCont _ => back `min` sz
                              end -∗ |==>
              i2_lower_bound γi match cont with
                                | WithCont _ i2 => i2
                                | NoCont _      => (S back) `min` sz
                                end)%I as "Hup".
    { destruct cont as [i1 i2|bs]; iIntros "Hi●"; first done.
      iMod (i2_lower_bound_update with "Hi●") as "$"; [ lia | done ]. }
    iMod ("Hup" with "Hi●") as "Hi● {Hup}".
    (* We first handle the case where there is no more space in the queue. *)
    destruct (decide (back < sz)%Z) as [Hback_sz|Hback_sz]; last first.
    { iMod ("Close" with "[- IST TID]") as "_".
      { iRight. iExists (S back), pvs, pref, rest, cont, slots, deqs.
        assert (S back `min` sz = back `min` sz) as -> by lia.
        iFrame. iPureIntro. repeat split_and; try done.
        destruct cont as [i1 i2|bs]; last done.
        destruct Hcont as ((Ha1 & Ha2) & Ha3 & Ha4).
        by repeat (split; first lia).
      }
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      destruct Z.ltb eqn: Hlt.
      { apply Z.ltb_lt in Hlt; lia. }
      steps_r. sch_yield_ir "IST" "TID".
      iApply wsim_reset. iStopProof. revert st_src. combine_quant st_tgt.
      eapply wsim_coind. iIntros (? ? CIH [st_src st_tgt]) "[? [IST TID]]". destruct_quant CIH.
      unfold_iter_r. norm_r. sch_yield_ir "IST" "TID". by_coind CIH. iFrame.
    }
    (* We now have a reserved slot [i], which is still free. *)
    pose (i := back). pose (elts := map (get_value slots deqs) pref ++ rest).
    assert (slots !! back = None) as Hi_free.
    { destruct (Hslots i) as [Ha1 Ha2]. rewrite min_l in Ha1; last by lia.
      assert (¬ is_Some (slots !! back)). { intro Ha. apply Ha2 in Ha. lia. }
      apply eq_None_not_Some. eauto. }
    (* Useful fact: our index was not yet dequeued. *)
    assert (i ∉ deqs) as Hi_not_in_deq.
    { intros Ha. apply Hdeqs in Ha as (Ha & _). rewrite Hi_free in Ha. inversion Ha. }
    (* We then handle the case where there is a contradiction going on. *)
    destruct cont as [i1 i2|bs].
    { (* We access the atomic update and commit the element. *)
      sch_yield_l. steps_l.
      iApply (wsim_helping_run with "IST"); [exact Ist_help|by simpl_map|].
      clear_st. iIntros (st_src req_id) "IST Tok".
      sch_yield_l. norm_l.
      iApply (wsim_helping_pend_try_run with "Tok IST"); [exact Ist_help|].
      steps_l. iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [Vptr (vblk, vofs)]) with "He● He◯") as "[He● He◯]".
      force_l; iFrame "He◯". steps_l. step.
      iSplit; auto; iFrame.
      clear_st. iIntros (st_src st_tgt) "Done IST".
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i (Vptr (vblk, vofs)) Hi_free with "Hs●")
        as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* We also remember that we had contradiciton states. *)
      iDestruct "Hcont" as "#cont_wit".
      (* And we can close the invariant. *)
      iMod ("Close" with "[- IST TID Hwriting_tok_i]") as "_".
      { iRight. iExists (S back), pvs, pref, (rest ++ [Vptr (vblk, vofs)]), (WithCont i1 i2).
        iExists (<[i := (Vptr (vblk, vofs), Done, false)]> slots), deqs.
        rewrite fmap_insert /= array_content_NONEV; try done. iFrame.
        iFrame. iSplitL "He●".
        { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
          intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
        iSplitL "Hbig Htok_i".
        { iApply big_sepM_insert.
          + apply eq_None_not_Some. intros Ha. apply Hslots in Ha. lia.
          + iFrame "Hbig". repeat (iSplit; first done). done. }
        iFrame "cont_wit".
        destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
        iPureIntro. repeat split_and; try done; try by lia.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk. by lia.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|HNeq].
          + split; first by rewrite lookup_insert. split; first done.
            intros ->. apply Hpref in Hk as (_ & _ & ?). done.
          + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite /array_get. rewrite lookup_insert_ne; last done.
            apply Hdeqs in Hk as (? & ? & Ha). repeat (split; first done).
            rewrite /array_get in Ha.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + by rewrite lookup_insert.
          + by rewrite lookup_insert_ne.
        - rewrite /array_get lookup_insert_ne; first done. lia.
        - rewrite /array_get lookup_insert_ne; last by lia.
          destruct (slots !! i1) as [[[li1 si1] wi2]|] eqn : Hli1; last by inversion HC4.
          rewrite /array_get Hli1 // in HC7. }
      (* Let's clean up the context a bit. *)
      clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz.
      clear elts pvs pref rest slots deqs. subst i. rename back into i.
      (* We can now move to the store. *)
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). steps_r.
      sch_yield_ir "IST" "TID".
      (* We open the invariant again for the store. *)
      iInv "Inv" as "[[% X2]|HInv]" "Close".
      { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
        iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
      }
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* We also show that the same contradiction ist still going on. *)
      destruct cont as [i1' i2'|bs]; last first.
      { by iDestruct (contra_not_no_contra with "Hcont cont_wit") as %Absurd. }
      iDestruct (contra_agree with "cont_wit Hcont") as %[-> ->].
      destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      store_r "↦".
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      pose (new_slots := update_slot i set_written slots).
      iMod ("Close" with "[- IST TID]") as "_".
      { iRight. iExists back, pvs, pref, rest, (WithCont i1 i2), new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete //. }
          rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        destruct Hslots_i as [[[li si] wi] Hslots_i].
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup. split; intros ?; last done.
            rewrite Hslots_i. by eexists.
          + rewrite update_slot_lookup_ne; last done. by apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup Hslots_i /=. split; intros ?.
            * exfalso. rewrite Hslots_i in Hval_commit_i.
              destruct si as [γ|γ|]; try by inversion Hval_commit_i.
            * done.
          + rewrite update_slot_lookup_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /=. repeat split.
            * rewrite Hslots_i in Hval_commit_i.
              destruct si; try by inversion Hval_commit_i.
            * intros Hi%Hdeqs. destruct Hi as [Ha _].
              rewrite Hnot_written_i in Ha. inversion Ha.
            * by apply Hpref in Hk as (_ & _ & ?).
          + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /update_slot /=.
            rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
            rewrite decide_True; last done. repeat split; try done.
            destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
          + rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite update_slot_lookup Hslots_i /=.
            rewrite Hslots_i in HC4. by inversion HC4.
          + by rewrite update_slot_lookup_ne.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite /array_get update_slot_lookup Hslots_i /=.
            destruct (decide (i ∈ deqs)) as [Ha|Ha]; last done.
            exfalso. apply Hdeqs in Ha as (Ha1 & ? & ?).
            rewrite Hnot_written_i in Ha1. inversion Ha1.
          + by rewrite /array_get update_slot_lookup_ne.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite /array_get update_slot_lookup Hslots_i /=.
            rewrite Hslots_i in HC5. inversion HC5; subst wi.
            rewrite /array_get Hslots_i // in HC7.
          + rewrite /array_get update_slot_lookup_ne; last done.
            destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn : Hi1; last by inversion HC4.
            rewrite /array_get Hi1 // in HC7. }
      sch_yield_ir "IST" "TID". sch_yield_l. steps_l. unfold_iter_l. steps_l. force_l false.
      steps_l. sch_yield_l. force_l. iFrame. iSplit; auto.
      step. iFrame. eauto.
    }
    (* There is no [Contra1]/[Contra2], first assume the prophecy is trivial. *)
    destruct bs as [|b blocks].
    { (* We access the atomic update and commit the element. *)
      sch_yield_l. steps_l.
      iApply (wsim_helping_run with "IST"); [exact Ist_help|try by simpl_map|].
      clear_st. iIntros (st_src req_id) "IST Tok".
      sch_yield_l. norm_l.
      iApply (wsim_helping_pend_try_run with "Tok IST"); [exact Ist_help|].
      steps_l. iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [Vptr (vblk, vofs)]) with "He● He◯") as "[He● He◯]".
      force_l; iFrame "He◯". steps_l. step. iFrame.
      iSplit; first done. clear_st; iIntros (st_src st_tgt) "Done IST".
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i (Vptr (vblk, vofs)) Hi_free with "Hs●")
        as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* And we can close the invariant. *)
      iMod ("Close" with "[- IST TID Hwriting_tok_i]") as "_".
      { iRight. iExists (S back), pvs, pref, (rest ++ [Vptr (vblk, vofs)]), (NoCont []).
        iExists (<[i := (Vptr (vblk, vofs), Done, false)]> slots), deqs.
        rewrite array_content_NONEV //. iFrame.
        iFrame. iSplitL "He●".
        { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
          intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
        iSplitL "Hbig Htok_i".
        { iApply big_sepM_insert.
          + apply eq_None_not_Some. intros ?%Hslots. lia.
          + iFrame "Hbig". repeat (iSplit; first done). done. }
        destruct Hcont as (HC1 & HC2 & HC3).
        iPureIntro. repeat split_and; try done; try by lia.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk. by lia.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite /array_get. rewrite lookup_insert_ne; last done.
            apply Hdeqs in Hk as (? & ? & Ha3). repeat (split; first done).
            rewrite /array_get in Ha3.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
        - intros b Hb. by inversion Hb. }
      (* Let's clean up the context a bit. *)
      clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz.
      clear pvs pref rest slots deqs elts. subst i. rename back into i.
      (* We can now move to the store. *)
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). steps_r.
      sch_yield_ir "IST" "TID".
      (* We open the invariant again for the store. *)
      iInv "Inv" as "[[% X2]|HInv]" "Close".
      { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
        iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
      }
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      store_r "↦".
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      pose (new_slots := update_slot i set_written slots).
      iMod ("Close" with "[- IST TID]") as "_".
      { iRight. iExists back, pvs, pref, rest, cont, new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete_insert. by rewrite insert_id. }
          rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        destruct Hslots_i as [[[li si] wi] Hslots_i].
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup. split; intros ?; last done.
            rewrite Hslots_i. by eexists.
          + rewrite update_slot_lookup_ne; last done. by apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup Hslots_i /=. split; intros ?.
            * exfalso. rewrite Hslots_i in Hval_commit_i.
              destruct si as [γ|γ|]; try by inversion Hval_commit_i.
            * by inversion H.
          + rewrite update_slot_lookup_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /=. repeat split.
            * rewrite Hslots_i in Hval_commit_i.
              destruct si; try by inversion Hval_commit_i.
            * by intros Hi%Hpref.
            * by apply Hpref in Hk as (_ & _ & ?).
          + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /update_slot /=.
            rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
            rewrite decide_True; last done. repeat split; try done.
            destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
          + rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct cont as [i1 i2|bs].
          + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6). split; first done.
            destruct (decide (i1 = i)) as [->|Hi1_not_i].
            * rewrite /array_get update_slot_lookup Hslots_i /=.
              repeat split_and; try done.
              ** rewrite Hslots_i in Hval_commit_i. destruct si; try done.
              ** rewrite /array_get Hslots_i // in HC5. case_match; clarify.
            * rewrite /array_get update_slot_lookup_ne; last done.
              rewrite /array_get in HC3. done.
          + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
            intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
            * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
              ** rewrite -Hb1_is_i in Hslots_i. by rewrite Hslots_i in Hb1.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                by rewrite lookup_insert_ne.
            * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
              ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
                rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
                destruct (was_committed (li, si, true)); last done.
                exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
                destruct si; try done.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                rewrite lookup_insert_ne; last done. apply Hb2, Hk.
      }
      sch_yield_ir "IST" "TID".
      sch_yield_l. steps_l. unfold_iter_l. force_l false. steps_l.
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iFrame. done.
    }
    (* There is no [Contra1]/[Contra2], and the prophecy is non-trivial. *)
    destruct Hcont as (Hblocks & Hrest & Hpvs).
    assert (rest = []) as -> by by apply Hrest.
    rewrite app_nil_r in elts. rewrite app_nil_r.
    destruct b as [b_unused b_pendings].
    (* We compare our index with the unused element of the prophecy. *)
    destruct (decide (b_unused = i)) as [->|b_unused_not_i].
    + (* We are the non-committed element of the prophecy: commit the block. *)
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i (Vptr (vblk, vofs)) Hi_free with "Hs●")
        as "[Hs● [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* We then commit at our index. *)
      sch_yield_l. steps_l.
      iApply (wsim_helping_run with "IST"); [exact Ist_help|try by simpl_map|].
      clear_st. iIntros (st_src req_id) "IST Tok".
      sch_yield_l. norm_l.
      iApply (wsim_helping_pend_try_run with "Tok IST"); [exact Ist_help|].
      steps_l. iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [Vptr (vblk, vofs)]) with "He● He◯") as "[He● He◯]".
      force_l; iFrame "He◯". step. iFrame. iSplit; first auto.
      clear_st; iIntros (st_src st_tgt) "#Done IST". steps_l. sch_yield_l. steps_l.
      (* Our prophecy block must be valid. *)
      assert (block_valid slots (i, b_pendings))
        as Hb_valid by apply Hblocks, elem_of_list_here.
      rewrite /block_valid /= in Hb_valid.
      destruct Hb_valid as [Hb_valid1 Hb_valid2].
      (* We also need to commit for all indices in in [p_pendings] *)
      assert (NoDup (i :: b_pendings)) as Hblock_ND.
      { apply NoDup_app in Hpvs_ND as (Ha & _ & _). subst pvs.
        apply NoDup_app in Ha as (_ & _ & Ha). simpl in Ha.
        rewrite app_comm_cons in Ha. by apply NoDup_app in Ha as (Ha & _ & _). }
      apply NoDup_cons in Hblock_ND as (Hi & HNoDup).
      iAssert (per_slot_own γq γs i (Vptr (vblk, vofs), Done, false)) with "[Htok_i]" as "Hi".
      { rewrite /per_slot_own /=. eauto with iFrame. }
      iDestruct (big_sepM_insert (per_slot_own γq γs) slots i (Vptr (vblk, vofs), Done, false)
              with "[Hi Hbig]") as "Hbig"; [ done | by iFrame | .. ].
      iMod (Ist_help with "IST") as "[% [% [-> [X XClose]]]]".
      iPoseProof (helping_auth_split (1/2) with "X") as "[X X2]"; first done.
      iMod ("Close" with "[$]") as "_".
      add_ret_r tt. iApply wsim_bind. iSplitL "Hs● Hbig He● TID XClose X2".
      { iApply (big_lemma with "Inv [X2 XClose] TID Hs● Hbig He●");
          [by simpl_map|apply HNoDup|..].
        { intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + exfalso. apply Hi, Hk.
          + rewrite lookup_insert_ne; last done. apply Hb_valid2, Hk. }
        iIntros (?) "A"; iApply "XClose"; iApply "X2"; done.
      }
      clear_st. iIntros (st_src [] st_tgt []) "[? [Hs● [Hbig [He● [TID XClose]]]]]".
      iApply wsim_fold; iFrame.
      iInv "Inv" as "HInv" "Close".
      iDestruct "HInv" as "[[% ●Help] | [% [% [% [% [% [% [% [_ [_ [_ [_ [_ [_ [He●2 _]]]]]]]]]]]]]]]";
        last first.
      { iCombine "Hs● He●2" gives %WF%auth_auth_op_valid; ss. }
      iMod ("XClose" with "●Help") as "IST". steps_l.
      (* And then we can close the invariant. *)
      iMod ("Close" with "[- Hwriting_tok_i IST TID]") as "_".
      { pose (new_pref := pref ++ i :: b_pendings).
        pose (new_slots := map_imap (helped b_pendings) (<[i:=(Vptr (vblk, vofs), Done, false)]> slots)).
        iRight.
        iExists (S back), pvs, new_pref, [], (NoCont blocks), new_slots, deqs.
        iFrame. iSplitL "H_ar".
        { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
          apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
          rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
          - by rewrite lookup_insert Hb_valid1 /helped /= decide_False.
          - rewrite lookup_insert_ne; last done.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done.
            rewrite /helped /=. destruct ds as [dγ|dγ|].
            + destruct dw; try done; by destruct (decide (k ∈ b_pendings)).
            + by destruct dw.
            + by destruct dw. }
          iSplitL "He●".
          { rewrite app_nil_r /new_pref /elts map_app map_cons.
            rewrite [in get_value new_slots deqs i]/get_value.
            rewrite [in new_slots !! i]/new_slots.
            rewrite map_lookup_imap lookup_insert /= -app_assoc cons_middle.
            assert (NoDup (pref ++ i :: b_pendings)) as HND.
            { apply NoDup_app in Hpvs_ND as (HND & _ & _).
              rewrite cons_middle app_assoc.
              rewrite Hpvs /= in HND. rewrite cons_middle in HND.
              rewrite app_assoc app_assoc in HND.
              by apply NoDup_app in HND as (HND & _ & _). }
            rewrite annoying_lemma_1 //; last first.
            { intros k Hk. by apply Hpref in Hk as (? & ? & _). }
            assert (map (get_value new_slots deqs) b_pendings
                  = get_values (<[i:=(Vptr (vblk, vofs), Done, false)]> slots) b_pendings) as ->.
            - rewrite /new_slots. by eapply annoying_lemma_2.
            - done. }
          iPureIntro. repeat split_and; try done.
          - intros k. rewrite /new_slots map_lookup_imap. split; intros Hk.
            + destruct (decide (k = i)) as [->|Hk_not_i].
              * rewrite lookup_insert /helped /=. by eexists.
              * rewrite lookup_insert_ne; last done.
                assert (is_Some (slots !! k)) as [d ->] by (apply Hslots; lia).
                by apply is_Some_helped.
            + destruct (decide (k = i)) as [->|Hk_not_i]; first by lia.
              rewrite lookup_insert_ne in Hk; last done.
              assert (k < back `min` sz) as ?; last by lia.
              apply Hslots. destruct (slots !! k) as [d|]; first by exists d.
              by inversion Hk.
          - intros k. rewrite /new_slots map_lookup_imap.
            destruct (decide (k = i)) as [->|Hk_not_i];
              first by rewrite lookup_insert /helped /=.
            rewrite lookup_insert_ne; last done. split; intros Hk.
            + destruct (slots !! k) as [d|] eqn:HEq; last done.
              assert (was_committed <$> Some d ≫= helped b_pendings k = was_committed <$> Some d) as HEq1.
              { destruct d as [[dl []] dw]; simpl; simpl in Hk; by rewrite Hk. }
              rewrite HEq1 -HEq in Hk. apply Hstate in Hk. rewrite HEq in Hk.
              assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq2.
              { destruct d as [[dl []] []]; simpl; simpl in Hk; try by inversion Hk.
                rewrite /helped /=. destruct (decide (k ∈ b_pendings)); done. }
              rewrite HEq2. by inversion Hk.
            + destruct (slots !! k) as [d|] eqn:HEq; last done.
              assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq1.
              { by destruct d as [[dl []] dw]; rewrite /helped; destruct (decide (k ∈ b_pendings)). }
              rewrite HEq1 -HEq in Hk. apply Hstate in Hk. done.
          - intros k Hk. subst new_pref new_slots. apply elem_of_app in Hk as [Hk|Hk].
            { apply Hpref in Hk as (Ha1 & ?). split; last done.
              rewrite map_imap_insert /=. destruct (decide (k = i)) as [->|Hk_not_i].
              - by rewrite lookup_insert.
              - rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
                destruct (slots !! k) as [[[dl ds] dw]|]; last by inversion Ha1.
                rewrite /= /helped. destruct ds as [dγ|dγ|]; try done. }
            apply elem_of_cons in Hk as [Hk|Hk].
            { subst k. split; last done. by rewrite map_imap_insert /= lookup_insert. }
            apply Hb_valid2 in Hk as Hb_valid2_k. split.
            + rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
              * by rewrite lookup_insert /=.
              * rewrite lookup_insert_ne; last done.
                destruct (slots !! k) as [[[kl ks] kw]|]; last by inversion Hb_valid2_k.
                rewrite /= /helped. destruct ks; try done. by rewrite /= decide_True.
            + apply Hstate in Hb_valid2_k. apply Hstate in Hb_valid2_k. done.
          - intros k Hk. subst new_slots. rewrite /array_get map_lookup_imap.
            assert (k ≠ i) as Hk_not_i. { intros ->. apply Hi_not_in_deq, Hk. }
            rewrite lookup_insert_ne; last done. dup Hk; apply Hdeqs in Hk as (Ha1 & ? & Ha3).
            destruct (slots !! k) as [[[lk sk] wk]|] eqn:HEq; last by inversion Ha1.
            inversion Ha1; subst wk. rewrite /=. repeat split_and; try by destruct sk.
            destruct sk; try done; simpl.
            + rewrite decide_True; first done.
              rewrite /array_get HEq in Ha3. simpl in Ha3.
              destruct (decide (k ∈ deqs)); first done. by inversion H3.
            + rewrite decide_True; first done.
              rewrite /array_get HEq in Ha3. simpl in Ha3.
              destruct (decide (k ∈ deqs)); first done. by inversion Ha3.
          - intros b Hk. subst new_slots. rewrite map_imap_insert /=.
            assert (b ∈ (i, b_pendings) :: blocks) as Ha by set_solver +Hk.
            assert (NoDup (i :: b_pendings ++ flatten_blocks blocks)) as HND.
            { subst pvs. apply NoDup_app in Hpvs_ND as (HND & _ & _).
              apply NoDup_app in HND as (_ & _ & HND). done. }
            apply flatten_blocks_mem1 in Hk as Hk1.
            apply Hblocks in Ha as (Ha1 & Ha2). split.
            + assert (b.1 ≠ i) as Hb1_not_i.
              { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
                rewrite -HEq. apply elem_of_app. by right. }
              rewrite lookup_insert_ne; last done. by rewrite map_lookup_imap Ha1.
            + intros j Hj. assert (j ≠ i) as Hj_not_i.
              { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
                rewrite -HEq. apply elem_of_app. right.
                apply (flatten_blocks_mem2 _ _ Hk _ Hj). }
              rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
              apply Ha2 in Hj as Hcomm.
              destruct (slots !! j) as [[[lj sj] wj]|]; last by inversion Hj.
              rewrite /= /helped. destruct sj; try done. simpl.
              assert (j ∉ b_pendings); last by rewrite decide_False.
              intros Hj_contra. apply NoDup_cons in HND as [_ HND].
              apply NoDup_app in HND. destruct HND as (HND1 & HND2 & HND3).
              apply (HND2 _ Hj_contra). apply (flatten_blocks_mem2 _ _ Hk _ Hj).
          - by rewrite Hpvs /= /new_pref app_comm_cons app_assoc.
      }

      clear Hslots Hstate Hpref Hdeqs Hpvs Hrest Hblocks Hi_free Hi_not_in_deq.
      clear Hpvs_ND Hpvs_sz Hb_valid1 Hb_valid2 HNoDup Hi elts pvs pref slots deqs.
      clear blocks b_pendings. subst i. rename back into i.
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). steps_r.
      sch_yield_ir "IST" "TID".
      
      (* We open the invariant again for the store. *)
      iInv "Inv" as "[[% X2]|HInv]" "Close".
      { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
        iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
      }
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      store_r "↦".
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      iMod ("Close" with "[- IST TID]") as "_".
      { pose (new_slots := update_slot i set_written slots). iRight.
        iExists back, pvs, pref, rest, cont, new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete //. }
          rewrite {1} HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup. split; intros Hk; last by lia.
            by apply fmap_is_Some.
          + rewrite update_slot_lookup_ne; last done. apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup. split; intros Hk; exfalso.
            * destruct (slots !! i) as [[[li si] wi]|]; last by inversion Hk.
              inversion_clear Hnot_written_i. destruct si; inversion Hk.
              inversion Hval_commit_i.
            * destruct (slots !! i) as [[[li si] wi]|]; by inversion Hk.
          + rewrite update_slot_lookup_ne; last done. by apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup /=. split.
            * destruct (slots !! i) as [[[li si] wi]|]; first done.
              by inversion Hval_wit_i.
            * apply Hpref, Hk.
          + rewrite update_slot_lookup_ne; last done. by apply Hpref.
        - intros k Hk. assert (k ≠ i) as Hk_not_i.
          { intros ->. dup Hk; apply Hdeqs in Hk as (Ha1 & ? & Ha3).
            apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
            destruct Hslots_i as [[[li si] wi] Hslots_i].
            rewrite Hslots_i decide_False in Ha3; last done.
            rewrite Hslots_i in Ha1. inversion Ha1; subst wi. set_solver. }
          rewrite /array_get update_slot_lookup_ne; last done.
          apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct cont as [i1 i2|bs].
          + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
            split; first done. repeat split_and; try done.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|]; first done.
                by inversion Hval_wit_i.
              ** by rewrite update_slot_lookup_ne.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite /array_get update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
              ** by rewrite /array_get update_slot_lookup_ne.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite /array_get update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
                inversion  HC3; subst wi. done.
              ** rewrite /array_get update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn:HEq; try done.
                rewrite /array_get HEq // in HC5.
          + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
            destruct Hslots_i as [[[li si] wi] Hslots_i].
            intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
            * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
              ** rewrite -Hb1_is_i in Hslots_i. rewrite Hb1 in Hslots_i.
                by inversion Hslots_i.
              ** by rewrite /update_slot Hslots_i insert_delete_insert lookup_insert_ne.
            * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
              ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
                rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
                destruct (was_committed (li, si, true)) eqn:Ha; last done.
                exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
                destruct si; try done.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                rewrite lookup_insert_ne; last done. apply Hb2, Hk.
      }
      sch_yield_ir "IST" "TID". sch_yield_l. forces_l. iFrame. repeat iSplit; auto. step.
      iFrame. done.
    + (* We are not the first non-done element, we will give away our AU. *)
      sch_yield_l. steps_l.
      iApply (wsim_helping_run with "IST"); [exact Ist_help|by simpl_map|..].
      clear_st; iIntros (st_src req_id) "IST Tok".
      iMod (alloc_pend_slot γs slots i (Vptr (vblk, vofs)) req_id Hi_free with "Hs●")
        as "[Hs● [Htok_i [#val_wit_i [Hpend_tok_i [Hname_tok_i Hwriting_tok_i]]]]]".
      (* We close the invariant, storing our AU. *)
      iMod ("Close" with "[-Htok_i Hname_tok_i Hwriting_tok_i IST TID]") as "_".
      { pose (new_bs := glue_blocks (b_unused, b_pendings) i blocks).
        pose (new_slots := <[i:=(Vptr (vblk, vofs), Pend req_id, false)]> slots). iRight.
        iExists (S back), pvs, pref, [], (NoCont new_bs), new_slots, deqs.
        rewrite app_nil_r. iFrame. iSplitL "H_ar".
        { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
          apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - by rewrite Hi_free lookup_insert decide_False.
          - rewrite lookup_insert_ne; last done. destruct (slots !! k) as [d|]; last done.
            destruct d as [[dl ds] dw]. rewrite /helped /=.
            destruct ds as [dγ|dγ|]; destruct dw; try done. }
        iSplitL "He●".
        { erewrite map_ext_in; first done. subst new_slots.
          intros k Hk%elem_of_list_In. rewrite /get_value.
          assert (k ≠ i); last by rewrite lookup_insert_ne.
          intros ->. apply Hpref in Hk as (Ha1 & ?).
          rewrite Hi_free in Ha1. inversion Ha1. }
        iSplitL "Hbig Hpend_tok_i Tok".
        { iApply big_sepM_insert; first done. iFrame "#∗". }
        iPureIntro. subst new_slots. repeat split_and; try done.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk.  by lia.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. rewrite lookup_insert_ne; first by apply Hpref, Hk.
          intros HEq. subst k. apply Hpref in Hk as [Ha _].
          rewrite Hi_free in Ha. inversion Ha.
        - intros k Hk. rewrite /array_get lookup_insert_ne.
          + apply Hdeqs in Hk. by rewrite /array_get in Hk.
          + intros <-. apply Hdeqs in Hk as [Hk _]. rewrite Hi_free in Hk. done.
        - intros b Hb. subst new_bs. rewrite Hpvs in Hpvs_ND.
          apply NoDup_app in Hpvs_ND as (HND & _ & _).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          by eapply glue_blocks_valid.
        - subst pvs new_bs. f_equal. apply flatten_blocks_glue.
      }
      clear Hslots Hstate Hpref Hdeqs Hblocks Hrest Hpvs Hi_free Hi_not_in_deq.
      clear Hpvs_ND Hpvs_sz b_unused b_unused_not_i elts blocks pvs pref slots.
      clear deqs b_pendings. subst i. rename back into i.
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). steps_r.
      sch_yield_ir "IST" "TID".
      (* We open the invariant again for the store. *)
      iInv "Inv" as "[[% X2]|HInv]" "Close".
      { iMod (Ist_help with "IST") as "[% [% [-> [X ?]]]]".
        iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
      }
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      store_r "↦".
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We now look at the state of our cell. *)
      destruct Hslots_i as [[[l' s] w] Hi].
      rewrite Hi in Hval_wit_i. simpl in Hval_wit_i.
      inversion Hval_wit_i; subst l'.
      destruct s as [γs_i'|γs_i'|].
      - (* We are still in the pending state: contradiction. *)
        (* We need to run our atomic update ourselves, we recover it. *)
        rewrite -[in X in ([∗ map] _ ↦ _ ∈ X, _)%I](insert_id _ _ _ Hi).
        rewrite -insert_delete_insert.
        iDestruct (big_sepM_insert with "Hbig") as "[Hbig_i Hbig]"; first by apply lookup_delete.
        iDestruct "Hbig_i" as "[_ [_ [Hcommit_tok_i HAU]]]".
        sch_yield_l. steps_l.
        (* We use the name token to show that γs_i and γs_i' are equal. *)
        iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
        assert (γs_i' = req_id) as Hγs_i; last subst γs_i'.
        { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
        iApply (wsim_helping_pend_try_run with "HAU IST"); first apply Ist_help.
        (* We run our atomic update ourself. *)
        steps_l. iRename "ASM" into "He◯".
        pose (elts := map (get_value slots deqs) pref ++ rest).
        iDestruct (sync_elts with "He● He◯") as %<-.
        iMod (update_elts _ _ _ (elts ++ [Vptr (vblk, vofs)]) with "He● He◯") as "[He● He◯]".
        iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
        iMod (use_pending_tok with "Hs● Hcommit_tok_i") as "[Hs● #commit_wit_i]".
        { by rewrite update_slot_lookup Hi /=. }
        iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●".
        { by rewrite update_slot_lookup update_slot_lookup Hi. }
        force_l; iFrame "He◯". step. iFrame. iSplit; first done. clear_st.
        iIntros (??) "Done IST".
        (* We now act according ot the contradiction status. *)
        destruct cont as [i1 i2|bs].
        * (* A contradiction has arised from somewhere else, we keep it. *)
          iMod ("Close" with "[- IST TID]") as "_".
          { iRight. iExists back, pvs, pref, (rest ++ [Vptr (vblk, vofs)]), (WithCont i1 i2).
            iExists (update_slot i set_written_and_done slots), deqs.
            subst elts. rewrite app_assoc. iFrame. iSplitL "H_ar".
            { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
            iSplitL "He●".
            { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
              rewrite /get_value /update_slot Hi insert_delete_insert.
              destruct (decide (k = i)) as [->|Hk_not_i].
              - by rewrite lookup_insert Hi.
              - by rewrite lookup_insert_ne. }
            iSplitL "Hs●".
            { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
            iSplitL.
            {  rewrite /update_slot Hi.
              iApply big_sepM_insert; first by rewrite lookup_delete.
              iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
              iSplit; first done. iSplit; done. }
            iPureIntro.
            destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
            repeat split_and; try lia; try done.
            - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
              + rewrite update_slot_lookup_ne; last done. apply Hslots.
            - intros k. split; intros Hk.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne; last done.
                rewrite update_slot_lookup_ne in Hk; last done.
                by apply Hstate.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
            - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi /=. split; [ done | by apply Hpref, Hk ].
              + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
            - intros k Hk. assert (k ≠ i) as Hk_not_i.
              { intros ->. apply Hdeqs in Hk as (Ha1 & ? & Ha3).
                apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
                rewrite Hi decide_False in Ha3; last done.
                rewrite Hi in Ha1. inversion Ha1; subst w. set_solver. }
              rewrite /array_get update_slot_lookup_ne; last done.
              apply Hdeqs in Hk. rewrite /array_get in Hk. done.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite update_slot_lookup Hi.
              + by rewrite update_slot_lookup_ne.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite update_slot_lookup Hi /=.
              + rewrite update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|]; last by inversion HC4.
                inversion HC5; subst wi1. done.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite /array_get update_slot_lookup Hi /= decide_False.
              + rewrite /array_get update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn : Hli1 ; last by inversion HC4.
                rewrite /array_get Hli1 // in HC7.
          }
          sch_yield_ir "IST" "TID". sch_yield_l. steps_l.
          unfold_iter_l. force_l false. steps_l. sch_yield_l. force_l; iFrame.
          repeat iSplit; auto. step. iFrame. done.
        * (* No contradiction yet, make it ours if the prophecy is non-trivial. *)
          iAssert (match bs with
                 | [] => i2_lower_bound γi (back `min` sz)
                 | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                 end -∗ |==>
                   match bs with
                   | []           => True
                   | (i2, _) :: _ => contra γc i i2
                   end ∗
                   match bs with
                   | []           => i2_lower_bound γi (back `min` sz)
                   | (i2, _) :: _ => i2_lower_bound γi i2
                   end)%I as "Hup".
          { destruct bs as [|[i2 ps] bs]; first (iIntros "Hi●"; by iFrame).
            iIntros "[Hcont Hi●]". iMod (to_contra i i2 with "Hcont") as "$".
            iMod (i2_lower_bound_update _ _ i2 with "Hi●") as "$"; last done.
            assert (block_valid slots (i2, ps)) as [Hvalid _].
            { destruct Hcont as (Hblocks & _ & _). apply Hblocks, elem_of_list_here. }
            assert (¬ (i2 < back `min` sz)) as ?%not_lt; last by lia.
            eapply iffRLn.
            - apply Hslots.
            - intros Ha. rewrite Hvalid in Ha. by inversion Ha. }
          iAssert (match bs with
                  | [] => i2_lower_bound γi (back `min` sz)
                  | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                  end ∗
                  match bs with
                  | [] => no_contra γc
                  | _  => True
                  end)%I with "[Hcont Hi●]" as "[HNC_triv HNC_non_triv]".
          { destruct bs; by iFrame. }
          iMod ("Hup" with "HNC_triv") as "[#HC_triv Hi●]".
          (* We can now close the invariant. *)
          iMod ("Close" with "[- IST TID]") as "_".
          { pose (new_slots := update_slot i set_written_and_done slots).
            pose (cont := match bs with [] => NoCont [] | (i2, _) :: _ => WithCont i i2 end).
            pose (l := Vptr (vblk, vofs)).
            iRight. iExists back, pvs, pref, (rest ++ [l]), cont, new_slots, deqs.
            subst new_slots elts cont. rewrite app_assoc. iFrame. iSplitL "H_ar".
            { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
            iSplitL "Hi●".
            { destruct bs as [|[b_u b_ps] bs]; by iFrame. }
            iSplitL "He●".
            { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
              rewrite /get_value /update_slot Hi insert_delete_insert //.
              destruct (decide (k = i)) as [->|Hk_not_i].
              - simpl. by rewrite lookup_insert Hi.
              - by rewrite lookup_insert_ne. }
            iSplitL "Hs●".
            { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
            iSplitR "HNC_non_triv".
            { rewrite /update_slot Hi.
              iApply big_sepM_insert; first by rewrite lookup_delete.
              iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
              iSplit; first done. iSplit; done. }
            iSplitL "HNC_non_triv"; first by destruct bs as [|[i2 ps] bs].
            iPureIntro. repeat split_and.
            - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
              + rewrite update_slot_lookup_ne; last done. apply Hslots.
            - intros k. split; intros Hk.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne; last done.
                rewrite update_slot_lookup_ne in Hk; last done.
                by apply Hstate.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
            - intros k Hk. apply Hpref in Hk as (Ha1 & ? & _). repeat split; try done.
              + destruct (decide (k = i)) as [->|Hk_not_i].
                * by rewrite update_slot_lookup Hi.
                * by rewrite update_slot_lookup_ne.
              + destruct bs as [|[b_u b_ps] bs]; first done.
                intros ->. rewrite Hi in Ha1. by inversion Ha1.
            - intros k Hk. assert (k ≠ i) as Hk_not_i.
              { intros ->. apply Hdeqs in Hk as (Ha1 & ? & Ha3).
                apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
                rewrite Hi decide_False in Ha3; last done.
                rewrite Hi in Ha1. inversion Ha1; subst w. inversion Ha3. }
              rewrite /array_get update_slot_lookup_ne; last done.
              apply Hdeqs in Hk. rewrite /array_get in Hk. done.
            - done.
            - done.
            - destruct Hcont as (HC1 & HC2 & HC3).
              destruct bs as [|[i2 ps] bs].
              + repeat split_and; try done. intros. by set_solver.
              + repeat split_and; try lia.
                * assert (i < back `min` sz)
                    as Hi_lt by (apply Hslots; by eexists).
                  assert (block_valid slots (i2, ps))
                    as Hvalid by apply HC1, elem_of_list_here.
                  assert (slots !! i2 = None)
                    as Hi2_None by by destruct Hvalid as (? & _).
                  assert (¬ i2 < back `min` sz) as Hi2_ge; last by lia.
                  intros Ha%Hslots. rewrite Hi2_None in Ha. by inversion Ha.
                * apply Hpvs_sz. subst pvs. apply elem_of_app. right. simpl.
                  by apply elem_of_list_here.
                * by rewrite update_slot_lookup Hi /=.
                * by rewrite update_slot_lookup Hi /=.
                * by apply Hstate.
                * rewrite /array_get update_slot_lookup Hi /=.
                  rewrite decide_False; first done. apply Hstate. done.
                * rewrite HC3 /=. exists (ps ++ flatten_blocks bs).
                  by rewrite cons_middle app_assoc.
          }
          sch_yield_ir "IST" "TID". sch_yield_l. steps_l.
          unfold_iter_l. force_l false. steps_l. sch_yield_l. force_l; iFrame.
          repeat iSplit; eauto; step; iFrame; done.
      - (* We have moved to the helped state. *)
        pose (l := Vptr (vblk, vofs)).
        assert (slots = <[i := (l, Help γs_i', w)]> (delete i slots))
          as Hslots_i by by rewrite insert_delete_insert insert_id.
        rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I]Hslots_i.
        (* We recover our postcondition. *)
        iDestruct (big_sepM_insert with "Hbig")
          as "[Hbig_i Hbig]"; first by apply lookup_delete.
        iDestruct "Hbig_i" as "[_ [_ [Hcommit_wit_i Hpost]]]".
        sch_yield_l. steps_l.
        (* We use the name token to show that γs_i and γs_i' are equal. *)
        iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
        assert (γs_i' = req_id) as Hγs_i; last subst γs_i'.
        { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
        iApply (wsim_helping_done_try_run with "Hpost IST"); first exact Ist_help.
        iIntros "IST".
        (* We need to move from helped to done. *)
        iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●". { by rewrite Hi. }
        (* We perform some updates. *)
        iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
        iMod ("Close" with "[- TID IST]") as "_".
        { pose (new_slots := update_slot i set_written_and_done slots).
          iRight. iExists back, pvs, pref, rest, cont, new_slots, deqs.
          subst new_slots. iFrame. iSplitL "H_ar".
          { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
          iSplitL "He●".
          { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
            rewrite /get_value /update_slot Hi insert_delete_insert.
            destruct (decide (k = i)) as [->|Hk_not_i].
            - by rewrite lookup_insert Hi.
            - by rewrite lookup_insert_ne. }
          iSplitL "Hs●".
          { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
          iSplitL.
          { rewrite /update_slot Hi.
            iApply big_sepM_insert; first by rewrite lookup_delete.
            iFrame "Hbig". rewrite /per_slot_own /=. iFrame. iSplit; done. }
          iPureIntro. repeat split_and; try done.
          - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
            + rewrite update_slot_lookup_ne; last done. apply Hslots.
          - intros k. split; intros Hk.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne; last done.
              rewrite update_slot_lookup_ne in Hk; last done.
              by apply Hstate.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
          - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; first done. apply Hpref, Hk.
            + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
          - intros k Hk. assert (k ≠ i) as Hk_not_i.
            { intros ->. apply Hdeqs in Hk as (Ha1 & Ha2 & Ha3).
              apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
              rewrite Hi decide_False in Ha3; last done.
              rewrite Hi in Ha1. inversion Ha1; subst w. inversion Ha3. }
            rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
          - destruct cont as [i1 i2|bs].
            + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
              split; first done. repeat split_and; try done.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite update_slot_lookup Hi.
                ** by rewrite update_slot_lookup_ne.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite /array_get update_slot_lookup Hi /=.
                ** rewrite /array_get update_slot_lookup_ne; last done.
                  rewrite /array_get in HC3. done.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite /array_get update_slot_lookup Hi decide_False.
                ** rewrite /array_get update_slot_lookup_ne; last done.
                  rewrite /array_get in HC3. done.
            + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
              intros b Hb. apply HC1 in Hb as (Ha1 & Ha2). split.
              ** assert (b.1 ≠ i) as Hb1_not_i.
                { intros Ha. rewrite Ha in Ha1. by rewrite Hi in Ha1. }
                by rewrite update_slot_lookup_ne.
              ** intros k Hk. assert (k ≠ i) as Hb1_not_i.
                { intros ?. subst k. apply Ha2 in Hk. rewrite Hi in Hk.
                  by inversion Hk. }
                rewrite update_slot_lookup_ne; last done. by apply Ha2.
        }
        sch_yield_ir "IST" "TID". sch_yield_l. steps_l.
        unfold_iter_l; force_l false; steps_l.
        sch_yield_l. force_l; iFrame; repeat iSplit; auto; step.
        iFrame. done.
      - (* We are in the done state: contradiction. *)
        iDestruct (big_sepM_lookup _ _ i with "Hbig")
          as "[_ [_ H]]"; first done; simpl.
        iDestruct "H" as "[_ Htok_i']".
        by iDestruct (slot_token_exclusive with "Htok_i Htok_i'") as "H".
  Qed.

  Lemma ctxr :
    ctx_refines
      ((HWQM.t N mn ★ HelpingOn.t mn (HWQM.jobCode) sp) ★ MemA.t sp_mem ★ ProphecyA.t mn ∅, emp)%I
      ((HWQP.t mn   ★ HelpingDummy.t mn)                ★ MemA.t sp_mem ★ ProphecyA.t mn ∅, emp)%I.
  Proof.
    eapply main_adequacy with (Ist := IstFull).
    eapply ISim_reflR.
    { intros fn Hfn; rewrite Mod.dom_fnsems_add in Hfn; set_unfold in Hfn; des; subst.
      { apply simF_new_queue. }
      { apply simF_enqueue. }
      { admit. }
      { iStartSim. steps_r; ss. }
      { iStartSim. steps_r; ss. }
    }
    { (refl||eauto using submseteq_nil_l). }
    { (refl||eauto using submseteq_nil_l). }
    { rewrite !Mod.dom_fnsems_add; try set_solver. }
    { mod_tac. }
    { admit. }
  Admitted.
End HWQPM. End HWQPM.

Module HWQIA. Section HWQIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !hwqG, !memGS, !prophGS}.

  Lemma ctxr (ctx : Mod.t) (N : namespace) (sp_user sp sp_mem : specmap) csl genv :
    SchA.sp sp_user (↑N) ⊆ sp →
    real_mod ctx →
    refines
      (HWQA.t N sp ★ MemA.t sp_mem   ★ SchI.t ★ ctx, MemA.init_cond csl genv ∗ ProphecyA.initial_cond)%I
      (HWQI.t      ★ MemI.t csl genv ★ SchI.t ★ ctx, emp%I).
  Proof.
    intros Hsch Hreal.
    eapply helping_prophecy_refines; eauto.
    { apply HWQIP.ctxr. }
    { intros mn; etrans; cycle 1.
      { rewrite assoc; apply HWQPM.ctxr. }
      rewrite assoc; refl.
    }
    { intros mn; eapply main_adequacy.
      admit. (* erasure of helping - HWQMA *) 
    }
    { intros mn; rewrite /real_mod.
      let real_tac :=
        (split; ss; intros ??; destruct excluded_middle_informative; ss) in
      mod_tac real_tac.
    }
  Admitted.
End HWQIA. End HWQIA.

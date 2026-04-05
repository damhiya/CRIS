Require Import CRIS.
Require Import ProphecyHeader Ensembles.
From iris.algebra Require Import auth excl functions.

Definition ProphInst : Type :=
  { P : Prophecy.t & (P.(Prophecy.Pro) * list P.(Prophecy.Obs))%type }.
Canonical Structure ProphInstO := leibnizO ProphInst.

Definition ProphRA : ucmra := Prophecy.ID -d> excl_authUR ProphInstO.
Definition IdRA : ucmra := Prophecy.ID -d> excl_authUR unitO.
Class prophGpreS `{!crisG Γ Σ α β τ _I _S} := {
  #[local] proph_inG :: inG ProphRA Γ;
  #[local] id_inG :: inG IdRA Γ;
}.
Class prophGS `{!crisG Γ Σ α β τ _I _S} := {
  #[local] prophGS_prophGpreS :: prophGpreS;
  proph_name : gname;
  id_name : gname;
}.
Definition prophΓ : HRA := #[ProphRA; IdRA].
Global Instance subG_prophG `{!crisG Γ Σ α β τ _I _S} : subG prophΓ Γ → prophGpreS.
Proof. solve_inG. Defined.

Section ProphecyRA.
  Context `{!crisG Γ Σ α β τ _I _S, !prophGS}.

  Definition dummy_proph : Prophecy.t :=
    {| Prophecy.Pro := ();
       Prophecy.Obs := ();
       Prophecy.consistent := λ _ _, True;
       Prophecy.obs_default := ();
       Prophecy.coverage := λ _, ex_intro _ () (λ _, Logic.I); |}.

  Definition dummy_prophinst : ProphInst.
  Proof using Type.
    econs. instantiate (1:=dummy_proph). simpl. exact (tt, []).
  Qed.

  Definition has_proph_r (id : Prophecy.ID) (v : ProphInst) : ProphRA :=
    discrete_fun_singleton id (◯E v).
  Definition has_proph (id : Prophecy.ID) (v : ProphInst) : iProp Σ :=
    own proph_name (has_proph_r id v).
  Definition syn_has_proph {n} (id : Prophecy.ID) (v : ProphInst) : GTerm.t n :=
    sown proph_name (has_proph_r id v).
  Global Instance has_proph_red {n} id v : SLRed n (syn_has_proph id v) (has_proph id v).
  Proof. solve_sl_red. Qed.

  Definition has_proph_auth_r (P : Prophecy.ID → Prop) (map : Prophecy.ID -> ProphInst) : ProphRA :=
    λ id,
      if excluded_middle_informative (P id)
      then ●ε
      else ●E (map id).

  Definition has_proph_auth (P : Prophecy.ID → Prop) (map : Prophecy.ID -> ProphInst) : iProp Σ :=
    own proph_name (has_proph_auth_r P map).

  (* initial resource should have no prophecy value *)
  Definition proph_ir : DRA_mk ProphRA :=
    has_proph_auth_r (Ensembles.Full_set _) (const dummy_prophinst).

  Definition free_id_r (P : Prophecy.ID → Prop) : IdRA :=
     λ i, if (excluded_middle_informative (P i)) then ◯E () else ε.
  Definition free_id (P : Prophecy.ID → Prop) : iProp Σ :=
    own id_name (free_id_r P).

  Lemma free_id_r_split P Q R :
    (∀ i, P i <-> Q i ∨ R i) →
    (¬ ∃ i, Q i ∧ R i) →
    free_id_r P ≡ free_id_r Q ⋅ free_id_r R.
  Proof using Type.
    intros IFF DISJ. rewrite /free_id_r. ii.
    rewrite discrete_fun_lookup_op.
    destruct excluded_middle_informative.
    - rewrite IFF in p. des.
      + destruct excluded_middle_informative; clarify.
        destruct excluded_middle_informative; clarify.
        exfalso. apply DISJ. et.
      + destruct (excluded_middle_informative (R x)); clarify.
        destruct excluded_middle_informative; clarify.
        exfalso. apply DISJ. et.
    - des_ifs; exfalso; apply n; rewrite IFF; et.
  Qed.

  Lemma free_id_split_singleton P i :
    P i →
    free_id P -∗ free_id (.=i) ∗ free_id (λ x, if (decide (x = i)) then False else P x)%type.
  Proof using Type.
    iIntros (Pi) "F". rewrite /free_id free_id_r_split; first iDestruct ("F") as "[$ $]".
    { ii; split; des_ifs; ii; ss; eauto; des; clarify. }
    { ii; des; subst; des_ifs; ss. }
  Qed.

  Lemma free_id_split (P Q : Prophecy.ID → Prop) `{∀ x, Decision (Q x)} :
    free_id P -∗ free_id (P /1\ Q) ∗ free_id (λ x, P x ∧ ¬ Q x)%type.
  Proof.
    rewrite /free_id -own_op -free_id_r_split.
    { iIntros "$". }
    { intros i; split.
      { intros HP; destruct (decide (Q i)); [left|right]; ss. }
      intros [[? ?]|[? ?]]; ss.
    }
    intros [? [? [? ?]]]; naive_solver.
  Qed.

  Lemma free_id_iff P Q :
    (∀ i, P i ↔ Q i) →
    free_id P ⊣⊢ free_id Q.
  Proof using Type.
    intros Hi; rewrite /free_id. eapply eq_ind; first reflexivity.
    f_equal. rewrite /free_id_r. f_equal. extensionalities i; des_ifs; ss; exfalso; naive_solver.
  Qed.

  Lemma free_id_incl P Q (INCL : Q <1= P) : free_id P ⊢ free_id Q.
  Proof using Type.
    unfold free_id, free_id_r. apply own_mono.
    exists (λ i, if excluded_middle_informative (P i ∧ (¬ Q i)) then ◯E () else ε).
    ii. discrete_fun_tac. des_ifs; try tauto. exfalso. et.
  Qed.

  Lemma free_id_sep_or P Q : free_id P ∗ free_id Q ⊢ free_id (P \1/ Q).
  Proof using Type.
    unfold free_id, free_id_r. rewrite -own_op. apply own_mono.
    exists (λ i, if excluded_middle_informative (P i ∧ Q i) then ◯E () else ε).
    ii. do 2 discrete_fun_tac. des_ifs; tauto.
  Qed.

  Lemma free_id_sep_or_iff P Q (EXCL : forall x, P x -> Q x -> False) : free_id P ∗ free_id Q ⊣⊢ free_id (P \1/ Q).
  Proof using Type.
    iSplit. iApply free_id_sep_or. iIntros. unfold free_id, free_id_r. rewrite -own_op. 
    iStopProof. apply own_mono. exists ε. ii. do 2 discrete_fun_tac. des_ifs; try tauto.
    exfalso. et.
  Qed.

  Lemma free_id_sepL {A} (l : list A) (ND : NoDup l) P
      (EXCL : forall a b, a <> b -> (forall x, P a x -> P b x -> False)) :
    ([∗ list] x ∈ l, free_id (P x))%I ⊣⊢
      match l with
      | [] => emp%I
      | _ => free_id (λ i, exists x (IN : x ∈ l), P x i)
      end.
  Proof using Type.
    iSplit; iIntros; iStopProof.
    - clear ND. induction l; ss. iIntros "[A B]". rewrite IHl. des_ifs.
      + iClear "B". iStopProof. rewrite free_id_iff; first et. i. split; i.
        * exists a. eexists. econs. et.
        * des. inv IN; et. inv H3.
      + iPoseProof (free_id_sep_or with "[$A $B]") as "C". rewrite free_id_iff; first et.
        i. split; i; des.
        * exists a. eexists. econs. et.
        * exists x. eexists. econs; et. et.
        * inv IN; et.
    - induction ND; ss. rewrite -IHND. des_ifs; iIntros "A".
      + iSplit; et. rewrite free_id_iff; first et. i. split; i.
        * des. inv IN; et. inv H4.
        * exists x. eexists. econs. et.
      + rewrite free_id_sep_or_iff; cycle 1.
        { i. des. apply H0. destruct (classic (x = x1)); subst; et. exfalso. eapply EXCL; et. }
        rewrite free_id_iff; first et. i. split; i.
        * des. inv IN; et.
        * des. { exists x. eexists. econs. et. } { exists x0. eexists. econs. et. et. }
  Qed.

  Definition free_id_auth_r (P : Prophecy.ID → Prop) : IdRA :=
    λ i, if (excluded_middle_informative (P i)) then ●E() else ●ε.
  Definition free_id_auth (P : Prophecy.ID → Prop) : iProp Σ :=
    own id_name (free_id_auth_r P).
End ProphecyRA.

Lemma proph_alloc `{!crisG Γ Σ α β τ _I _S, !prophGpreS} :
  ⊢ o=> ∃ (_ : prophGS),
    has_proph_auth (Full_set _) (const dummy_prophinst) ∗
    free_id_auth (Full_set _) ∗
    free_id (Full_set _).
Proof.
  iMod (own_alloc (has_proph_auth_r (Ensembles.Full_set _) (const dummy_prophinst))) as "[%γp ?]".
  { rewrite /has_proph_auth_r; ii; des_ifs; apply auth_auth_valid; ss. }
  iMod (own_alloc (free_id_auth_r (Ensembles.Full_set _) ⋅ free_id_r (Ensembles.Full_set _)))
    as "[%γi ?]".
  { rewrite /free_id_r /free_id_auth_r; intros i; rewrite discrete_fun_lookup_op; case_match; ss.
    { apply auth_both_valid_discrete; split; ss. }
    { rewrite right_id auth_auth_valid //. }
  }
  by iExists (Build_prophGS _ _ _ _ _ _ _ _ _ γp γi); rewrite own_op; iFrame.
Qed.

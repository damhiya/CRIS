Require Import CRIS.
Require Import ProphecyHeader Ensembles.
From iris.algebra Require Import auth excl functions.

Set Implicit Arguments.

Definition ProphInst : Type :=
  { P : Prophecy.t & (P.(Prophecy.Pro) * list P.(Prophecy.Obs))%type }.
Canonical Structure ProphInstO := leibnizO ProphInst.

Section RA.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.

  Definition ProphRA : ucmra := Prophecy.ID -d> excl_authUR ProphInstO.
  Definition IdRA : ucmra := Prophecy.ID -d> excl_authUR unitO.
  
  Class prophG := {
    proph_inG :: inG ProphRA Γ;
    id_inG :: inG IdRA Γ;
  }.
  Definition prophΓ : HRA := #[ProphRA; IdRA].
  Global Instance subG_prophG : subG prophΓ Γ → prophG.
  Proof. solve_inG. Defined.

End RA.
Hint Unfold subG_prophG proph_inG id_inG : GRA_index.

Section ProphecyRA.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_prophG: !prophG}.

  Definition has_proph_r (id : Prophecy.ID) (v : ProphInst) : ProphRA :=
     discrete_fun_singleton id (◯E v).
  Definition has_proph (id : Prophecy.ID) (v : ProphInst) : iProp Σ :=
    own base_γ (has_proph_r id v).

  Definition has_proph_auth_r (P : Prophecy.ID → Prop) (map : Prophecy.ID -> ProphInst) : ProphRA :=
       ((λ id,
          if excluded_middle_informative (P id)
          then ●ε
          else ●E (map id))).

  Definition has_proph_auth (P : Prophecy.ID → Prop) (map : Prophecy.ID -> ProphInst) : iProp Σ := own base_γ (has_proph_auth_r P map).

  Definition free_id_r (P : Prophecy.ID → Prop) : IdRA :=
     λ i, if (excluded_middle_informative (P i)) then ◯E () else ε.
  Definition free_id (P : Prophecy.ID → Prop) : iProp Σ :=
    own base_γ (free_id_r P).

  Lemma free_id_r_split P Q R :
    (∀ i, P i <-> Q i ∨ R i) →
    (¬ ∃ i, Q i ∧ R i) →
    free_id_r P ≡ free_id_r Q ⋅ free_id_r R.
  Proof using Type.
    intros IFF DISJ. rewrite /free_id_r. ii. discrete_fun_tac.
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

  Lemma free_id_split P i :
    P i →
    free_id P ==∗ free_id (.=i) ∗ free_id (λ x, if (decide (x = i)) then False else P x)%type.
  Proof using Type.
    iIntros (Pi) "F". iMod (own_update with "F") as "[$ $]"; [|done].
    rewrite -free_id_r_split; first refl.
    { ii; split; des_ifs; ii; ss; eauto; des; clarify. }
    { ii; des; subst; des_ifs; ss. }
  Qed.

  Lemma free_id_iff P Q :
    (∀ i, P i ↔ Q i) →
    free_id P ⊣⊢ free_id Q.
  Proof using Type.
    intros Hi; rewrite /free_id. eapply eq_ind; first reflexivity.
    f_equal. rewrite /free_id_r. f_equal. extensionalities i; des_ifs; ss; exfalso; naive_solver.
  Qed.

  Definition free_id_auth_r (P : Prophecy.ID → Prop) : IdRA :=
    λ i, if (excluded_middle_informative (P i)) then ●E() else ●ε.
  Definition free_id_auth (P : Prophecy.ID → Prop) : iProp Σ :=
    own base_γ (free_id_auth_r P).

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

End ProphecyRA.

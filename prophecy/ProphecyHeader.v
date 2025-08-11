Require Import Common.
Require Import Ensembles String.
From stdpp Require Import base.

Set Implicit Arguments.

Module Prophecy.
  Definition ID : Type := string * SAny.t.
  Global Instance ID_dec : EqDecision ID.
  Proof.
    intros x y; destruct (excluded_middle_informative (x = y)).
    { constructor 1; eauto. }
    { constructor 2; eauto. }
  Qed.

  Fixpoint firstn {Obs} (rs : nat → Obs) (n : nat) : list Obs :=
    match n with
    | 0 => nil
    | S n' => rs n' :: firstn rs n'
    end.

  Fixpoint consistent_until {Pro Obs} consistent (obs_seq : list Obs) (p : Pro) : Prop :=
    consistent obs_seq p /\
    match obs_seq with
    | nil => True
    | _ :: obs_tl => consistent_until consistent obs_tl p
    end.

  Structure t := {
    Pro :> Type;
    Obs : Type;
    consistent : list Obs → Pro → Prop;
    obs_default : Obs;

    coverage :
      ∀ (obs_seq : nat → Obs),
        ∃ p, ∀ i, consistent (firstn obs_seq i) p;
    }.

  Lemma prophecy_consistent_until (proph : t) :
    ∀ obs_seq, ∃ p, ∀ i, consistent_until proph.(consistent) (firstn obs_seq i) p.
  Proof.
    i. destruct (proph.(coverage) obs_seq) as [p ?].
    exists p. i. remember (firstn obs_seq i) as obsl. revert i Heqobsl.
    induction obsl; i; s.
    - split; eauto. apply (H 0).
    - rewrite Heqobsl. split; eauto.
      destruct i; depdes Heqobsl. eauto.
  Qed.
End Prophecy.

Module ProphecyName.
  Definition new := "Prophecy.new".
  Definition resolve := "Prophecy.resolve".
  Definition close := "Prophecy.close".
End ProphecyName.
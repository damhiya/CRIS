Require Import Setoid.
Require Import Paco.paco.
Require Import IndefiniteDescription.
Require Import FunctionalExtensionality.
Require Import List.
Require Import Program.

(***

Manually-constructed Exco library for stream

**)

Section Stream.

Variable T: Type.

Variant _stream B : Type :=
| scons (t:T) (s: B)
.
Arguments scons {B}.

CoInductive stream :=
| sfold (s: _stream stream)
.

CoFixpoint sfix {X} (f: X -> _stream X) (x: X) : stream :=
  match f x with
  | scons t x' => sfold (scons t (sfix f x'))
  end.

Lemma stream_unfold
    (s: stream):
  s = match s with sfold s => sfold s end.
Proof. destruct s. eauto. Qed.

Lemma sfix_unfold
    X (f:X -> _stream X) (x: X):
  sfix f x = match f x with scons t x' => sfold (scons t (sfix f x')) end.
Proof.
  rewrite (stream_unfold (sfix f x)). simpl.
  destruct (f x). eauto.
Qed.

Variant _sclos {X} (R: X -> _stream X -> Prop) (self: X -> stream -> Prop) : X -> stream -> Prop :=
| sclos_intro
    x t x' s
    (REL: R x (scons t x'))
    (INF: self x' s):
  _sclos R self x (sfold (scons t s))
.
Hint Constructors _sclos: paco.

Definition sclos {X} R x s := paco2 (@_sclos X R) bot2 x s.

Lemma sclos_mon X R:
  monotone2 (@_sclos X R).
Proof.
  red. intros. inversion IN; subst.
  econstructor; eauto.
Qed.

Hint Unfold sclos: paco.
Hint Resolve sclos_mon: paco.

Definition sclos_fix {X} {ur: X -> _stream X -> Prop}
  (STEP: forall x, {ux | ur x ux}) (x: X) : stream
  :=
  sfix (fun x => proj1_sig (STEP x)) x.

Program Definition sclos_coind {X} {ur: X -> _stream X -> Prop}
  (STEP: forall x, {ux | ur x ux}) (x: X) : {s | sclos ur x s}
  :=
  exist _ (sclos_fix STEP x) _.
Next Obligation.
  revert x. pcofix CIH. intros. pstep.
  destruct (STEP x) as [ux REL] eqn: EQ.
  unfold sclos_fix. rewrite sfix_unfold. rewrite EQ. simpl.
  destruct ux; eauto using _sclos.
Qed.

End Stream.

Hint Constructors _sclos: paco.
Hint Unfold sclos: paco.
Hint Resolve sclos_mon: paco.

Arguments scons {T B}.
Arguments sfold {T}.


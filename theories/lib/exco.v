Require Import Setoid.
Require Import Paco.paco.
Require Import IndefiniteDescription.
Require Import FunctionalExtensionality.
Require Import List.
Require Import Program.
From stdpp Require Import fin.

(***

Indexed Construction

**)

Module SPF.

  Class t: Type := {
    I: Type;
    shp: I -> Type;
    deg: forall i, shp i -> (I -> Type);
  }.

End SPF.

Module ExCo.
Section ExCo.
  
Context `{C: SPF.t}.

Notation "X >-> Y" := (forall i, X i -> Y i) (at level 100).
Notation "X ~~ Y" := (forall i, X i -> Y i -> Prop) (at level 100).

Variant _co {self: SPF.I -> Type} {i: SPF.I} : Type :=
  | ccons (op: SPF.shp i) (args: SPF.deg i op >-> self)
.
Arguments _co self: clear implicits.

CoInductive co : SPF.I -> Type :=
| cfold {i} (c: _co co i): co i
.

CoFixpoint cfix {X} (f: X >-> _co X) {i} (x: X i) : co i :=
  match f i x with
  | ccons op args => cfold (ccons op (fun _ idx => cfix f (args _ idx)))
  end.

Lemma cunfold
  {i} (c: co i)
  :
  c = match c with cfold c => cfold c end.
Proof. destruct c. eauto. Qed.

Lemma cfix_unfold
  X (f: X >-> _co X) i (x: X i)
  :
  cfix f x = match f i x with ccons op args => cfold (ccons op (fun _ idx => cfix f (args _ idx))) end.
Proof.
  rewrite (cunfold (cfix f x)). simpl.
  destruct (f _ x). eauto.
Qed.

Variant _cclos {X} (R: X ~~ _co X) (self: X ~~ co) : X ~~ co :=
| cclos_intro
    i x op xs args
    (REL: R i x (ccons op xs))
    (INF: forall j idx, self j (xs j idx) (args j idx))
  :
  _cclos R self i x (cfold (ccons op args))
.
Hint Constructors _cclos: paco.

Definition cclos {X} R i x c := paco3 (@_cclos X R) bot3 i x c.

Lemma cclos_mon X R:
  monotone3 (@_cclos X R).
Proof.
  red. intros. dependent destruction IN.
  econstructor; eauto.
Qed.

Hint Unfold cclos: paco.
Hint Resolve cclos_mon: paco.

Definition clos_fix {X} {ur: X ~~ _co X}
  (STEP: forall i x, {ux | ur i x ux}) i (x: X i) : co i
  :=
  cfix (fun i x => proj1_sig (STEP i x)) x.

Program Definition clos_coind {X} {ur: X ~~ _co X}
  (STEP: forall i x, {ux | ur i x ux}) i (x: X i) : { c: co i | cclos ur i x c }
  :=
  exist _ (clos_fix STEP i x) _.
Next Obligation.
  intros. revert i x. pcofix CIH. intros. pstep.
  destruct (STEP i x) as [ux REL] eqn: EQ.
  unfold clos_fix. rewrite cfix_unfold. rewrite EQ. simpl.
  destruct ux; eauto using _cclos.
Qed.

End ExCo.
End ExCo.

Hint Constructors ExCo._cclos: paco.
Hint Unfold ExCo.cclos: paco.
Hint Resolve ExCo.cclos_mon: paco.

Arguments ExCo._co {C} self.
Arguments ExCo.ccons {C self i} op args.
Arguments ExCo.cfold {C i} c.

(***

Non-Indexed Construction

**)

Module SPFU.

  Class t: Type := {
    shp: Type;
    deg: shp -> Type;
  }.

End SPFU.

Module ExCoU.
Section ExCoU.

Context `{C: SPFU.t}.

Variant _co {self: Type} : Type :=
  | ccons (op: SPFU.shp) (args: SPFU.deg op -> self)
.
Arguments _co self: clear implicits.

CoInductive co : Type :=
| cfold (c: _co co): co
.

CoFixpoint cfix {X} (f: X -> _co X) (x: X) : co :=
  match f x with
  | ccons op args => cfold (ccons op (fun idx => cfix f (args idx)))
  end.

Lemma cunfold
  (c: co)
  :
  c = match c with cfold c => cfold c end.
Proof. destruct c. eauto. Qed.

Lemma cfix_unfold
  X (f: X -> _co X) (x: X)
  :
  cfix f x = match f x with ccons op args => cfold (ccons op (fun idx => cfix f (args idx))) end.
Proof.
  rewrite (cunfold (cfix f x)). simpl.
  destruct (f x). eauto.
Qed.

Variant _cclos {X} (R: X -> _co X -> Prop) (self: X -> co -> Prop) : X -> co -> Prop :=
| cclos_intro
    x op xs args
    (REL: R x (ccons op xs))
    (INF: forall idx, self (xs idx) (args idx))
  :
  _cclos R self x (cfold (ccons op args))
.
Hint Constructors _cclos: paco.

Definition cclos {X} R x c := paco2 (@_cclos X R) bot2 x c.

Lemma cclos_mon X R:
  monotone2 (@_cclos X R).
Proof.
  red. intros. dependent destruction IN.
  econstructor; eauto.
Qed.

Hint Unfold cclos: paco.
Hint Resolve cclos_mon: paco.

Definition clos_fix {X} {ur: X -> _co X -> Prop}
  (STEP: forall x, {ux | ur x ux}) (x: X) : co
  :=
  cfix (fun x => proj1_sig (STEP x)) x.

Program Definition clos_coind {X} {ur: X -> _co X -> Prop}
  (STEP: forall x, {ux | ur x ux}) (x: X) : { c: co | cclos ur x c }
  :=
  exist _ (clos_fix STEP x) _.
Next Obligation.
  intros. revert x. pcofix CIH. intros. pstep.
  destruct (STEP x) as [ux REL] eqn: EQ.
  unfold clos_fix. rewrite cfix_unfold. rewrite EQ. simpl.
  destruct ux; eauto using _cclos.
Qed.

End ExCoU.
End ExCoU.

Hint Constructors ExCoU._cclos: paco.
Hint Unfold ExCoU.cclos: paco.
Hint Resolve ExCoU.cclos_mon: paco.

Arguments ExCoU._co {C} self.
Arguments ExCoU.ccons {C self} op args.
Arguments ExCoU.cfold {C} c.

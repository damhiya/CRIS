Require Import Coqlib.
Require Import String.
Require Import Any.
Require Import ITreelib.
Require Import Events.
Require Import IModL.

Set Implicit Arguments.

Inductive obsE: Type -> Type :=
| obs_io
    (fn: string)
    (I: Type)
    (O: Type)
    (args: I)
    (rv: O)
 : obsE unit.

Module Tr.
  CoInductive t: Type :=
  | done (retv: Any.t)
  | spin
  | cons (hd: obsE unit) (tl: t)
  .

  Fixpoint app (pre: list (obsE unit)) (bh: t): t :=
    match pre with
    | [] => bh
    | hd :: tl => cons hd (app tl bh)
    end
  .
  Lemma fold_app
        s pre tl
    :
      (Tr.cons s (Tr.app pre tl)) = Tr.app (s :: pre) tl
  .
  Proof. reflexivity. Qed.

  Definition prefix (pre: list (obsE unit)) (bh: t): Prop :=
    exists tl, <<APP: app pre tl = bh>>
  .

End Tr.


Module Beh.

Definition t : Type := Tr.t -> Prop.
Definition improves (src tgt : t) : Prop := tgt <1= src.

Section BEHAVES.

Local Notation L := (itree coreE Any.t).

Variant _state_spin (state_spin: L -> Prop) : L -> Prop :=
  | state_spin_tau t
      (SPIN: state_spin t)
    : _state_spin state_spin (tau;; t)

  | state_spin_choose X k
      (SPIN: exists x, state_spin (k x))
    : _state_spin state_spin (x <- trigger (Choose X);; k x)
                  
  | state_spin_take X k
      (SPIN: forall x, state_spin (k x))
    : _state_spin state_spin (x <- trigger (Take X);; k x)
.

  Definition state_spin : _ -> Prop := paco1 _state_spin bot1.

Lemma state_spin_mon: monotone1 _state_spin.
Proof.
  ii. inv IN; try (by econs; eauto).
  des. econs; et.
Qed.

Hint Constructors _state_spin.
Hint Unfold state_spin.
Hint Resolve state_spin_mon: paco.
Hint Resolve cpn1_wcompat: paco.

Variant _of_itreeF (coself self: L -> Tr.t -> Prop) : L -> Tr.t -> Prop :=
| sb_final
    retv
  : _of_itreeF coself self (Ret retv) (Tr.done retv)
            
| sb_spin
    t
    (SPIN: state_spin t)
  : _of_itreeF coself self t (Tr.spin)

| sb_tau
    t evs
    (STEP: self t evs)
  :
  _of_itreeF coself self (tau;; t) evs

| sb_vis
    I O fn args r evs k
    (TL: coself (k r) evs)
  :
  _of_itreeF coself self (r <- trigger (@IO I O fn args);; k r) (Tr.cons (obs_io fn args r) evs)

| sb_choose
    X k evs
    (STEP: exists x, self (k x) evs)
  :
  _of_itreeF coself self (x <- trigger (Choose X);; k x) evs

| sb_take
    X k evs
    (STEP: forall x, self (k x) evs)
  :
  _of_itreeF coself self (x <- trigger (Take X);; k x) evs
.

Inductive _of_itree coself t evs : Prop :=
| _of_itree_intro (REL: _of_itreeF coself (_of_itree coself) t evs)
.

Definition of_itree: _ -> _ -> Prop := paco2 _of_itree bot2.

Theorem of_itree_tarski coself rel
  (FIX: _of_itreeF coself rel <2= rel)
  :
  _of_itree coself <2= rel.
Proof.
  fix IH 3.
  i. destruct PR.
  destruct REL; apply FIX; econs; des; esplits; try apply IH; try eassumption.
  apply STEP.
Qed.

Lemma of_itree_mon: monotone2 _of_itree.
Proof.
  ii. eapply of_itree_tarski, IN.
  i. destruct PR; eauto using _of_itree, _of_itreeF.
Qed.

Hint Constructors _of_itree.
Hint Unfold of_itree.
Hint Resolve of_itree_mon: paco.
Hint Resolve cpn1_wcompat: paco.

Lemma of_itree_ind
  (P: itree coreE Any.t -> Tr.t -> Prop)
  (SIM: _of_itreeF of_itree (of_itree /2\ P) <2= P)
  :
  of_itree <2= P.
Proof.
  i. punfold PR. revert x0 x1 PR.
  fix IH 3. i.
  destruct PR, REL; try by eapply SIM; pclearbot; des; econs; esplits; eauto.
Qed.

End BEHAVES.

End Beh.
Hint Unfold Beh.improves.
Hint Constructors Beh._state_spin.
Hint Unfold Beh.state_spin.
Hint Resolve Beh.state_spin_mon: paco.
Hint Resolve cpn1_wcompat: paco.
Hint Resolve cpn2_wcompat: paco.
Hint Constructors Beh._of_itree.
Hint Unfold Beh.of_itree.
Hint Resolve Beh.of_itree_mon: paco.

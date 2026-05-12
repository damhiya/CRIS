(** * Theorems about State effects *)

(* begin hide *)
From Stdlib Require Import Program.Tactics Morphisms Program.

From Paco Require Import paco.

From ITreeS Require Import
     Basics
     ITreeDefinition
     Sum
     Interp
     InterpFacts
     State
     Eqit
     EqitFacts
     EqAxiom.

Import ITreeNotations.

Local Open Scope itree_scope.

Import Monads.

(* end hide *)

Section state_facts.

Context {E F: iEvent} {S: Type} {R: Type}.

Definition _interp_state
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  (ot : itreeF E R (itree E R))
  : Monads.stateT S (itree F) R
  := fun (s: S) =>
  match ot with
  | RetF r => Ret (s, r)
  | TauF t => Tau (interp_state f t s)
  | VisF e k => f _ e s >>= (fun sx => Tau (interp_state f (k (snd sx)) (fst sx)))
  end.

Lemma unfold_interp_state (t : itree E R) s
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  :
  (interp_state f t s) = (_interp_state f (observe t) s).
Proof.
  unfold interp_state, interp, Basics.iter, MonadIter_stateT, Basics.iter, MonadIter_itree; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite bind_map, bind_bind. simpl.
    f_equal. extensionality r.
    rewrite bind_ret_l. f_equal.
Qed.

Lemma interp_state_ret
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  (s : S) (r : R)
  :
  (interp_state f (Ret r) s) = (Ret (s, r)).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_vis
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  {T: Type} (e : E T) (k : T -> itree E R) (s : S)
  :
  interp_state f (Vis e k) s
  = f T e s >>= fun sx => Tau (interp_state f (k (snd sx)) (fst sx)).
Proof.
  rewrite unfold_interp_state. reflexivity.
Qed.

Lemma interp_state_tau
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  (t : itree E R) (s : S)
  : interp_state f (Tau t) s = Tau (interp_state f t s).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

End state_facts.

Lemma interp_state_trigger
  {E F: iEvent} {S: Type}
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  {T: Type} (e : E T) (s : S)
  :
  interp_state f (ITree.trigger e) s = f _ e s >>= fun x => Tau (Ret x).
Proof.
  unfold ITree.trigger.
  rewrite interp_state_vis.
  f_equal. extensionality r.
  do 2 f_equal. rewrite interp_state_ret. destruct r. reflexivity.
Qed.

Lemma interp_state_bind
  {E F: iEvent} {S: Type}
  (f : forall T: Type, E T -> Monads.stateT S (itree F) T)
  {A B} (t : itree E A) (k : A -> itree E B) (s : S)
  :
  (interp_state f (t >>= k) s)
  =
  (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
Proof.
  eapply bisim_is_eq.
  revert t k s.
  ginit. gcofix CIH.
  intros t k s.
  rewrite unfold_bind.
  rewrite (unfold_interp_state t s f).
  destruct (observe t); simpl.
  - rewrite !bind_ret_l. simpl.
    gfinal. right. eapply paco2_mon_bot; eauto. eapply eq_is_bisim. eauto.
  - rewrite !bind_tau, interp_state_tau.
    gstep. econstructor. gbase. apply CIH.
  - rewrite interp_state_vis.
    rewrite bind_bind.
    guclo @eqit_clo_bind. econstructor.
    intros []. rewrite bind_tau.
    gstep; constructor.
    gfinal. left. eapply CIH.
Qed.

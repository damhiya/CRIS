(** * Theorems about [interp] *)

(** Main facts:
    - [unfold_interp]: Unfold lemma.
    - [interp_bind]: [interp] is a monad morphism.
    - [interp_trigger]: Events are interpreted using a handler.
 *)

(* begin hide *)
From Stdlib Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITreeS Require Import
     Basics
     CategoryOps
     ITreeDefinition
     Sum
     Interp
     TranslateFacts
     Eqit
     EqitFacts
     EqAxiom
     .

Import ITreeNotations.

(* end hide *)

Section interp_facts.

Context {E F: iEvent} {R: Type}.
Context (f: forall T:Type, E T -> itree F T).

(** Unfolding of [interp]. *)
Definition _interp (ot : itreeF E R _) : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f t)
  | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
  end.

(** Unfold lemma. *)
Lemma unfold_interp (t : itree E R) :
  interp f t = (_interp (observe t)).
Proof.
  unfold interp, Basics.iter, MonadIter_itree. rewrite unfold_iter.
  destruct (observe t); cbn;
    rewrite ?bind_ret_l, ?bind_map. all: try reflexivity.
Qed.

(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Lemma interp_ret (x: R):
  interp f (Ret x) = Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau (t: itree E R):
  interp f (Tau t) = Tau (interp f t).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis (U: Type) (e: E U) (k: U -> itree E R) :
  interp f (Vis e k) =
    ITree.bind (f _ e) (fun x => Tau (interp f (k x))).
Proof. rewrite unfold_interp. reflexivity. Qed.

End interp_facts.

#[global] Hint Rewrite @interp_ret : itree.
#[global] Hint Rewrite @interp_vis : itree.

(** ** [interp] properness *)

(* Proof of
   [interp f (t >>= k) ~ (interp f t >>= fun r => interp f (k r))]

   "By coinduction", case analysis on t:

    - [t = Ret r] or [t = Vis e k] (...)

    - [t = Tau t]:
          interp f (Tau t >>= k)
        = interp f (Tau (t >>= k))
        = Tau (interp f (t >>= k))
        { by "coinductive hypothesis" }
        ~ Tau (interp f t >>= fun ...)
        = Tau (interp f t) >>= fun ...
        = interp f (Tau t) >>= fun ...
        (QED)

 *)

Lemma interp_bind {E F: iEvent} {R S: Type}
      (f: E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  = ITree.bind (interp f t) (fun r => interp f (k r)).
Proof.
  eapply bisim_is_eq.
  revert t k. ginit. gcofix CIH; intros.
  rewrite (itree_eta t). destruct (observe t) eqn: EQ.
  - rewrite interp_ret, !bind_ret_l.
    gfinal. right. eapply paco2_mon_bot; eauto. apply eq_is_bisim. eauto.
  - rewrite !bind_tau, !interp_tau, !bind_tau.
    gstep. econstructor. eauto with paco.
  - rewrite !bind_vis, !interp_vis.
    rewrite !bind_bind.
    guclo @eqit_clo_bind; econstructor; try reflexivity. intros; subst.
    rewrite bind_tau. gstep; constructor; eauto with paco.
Qed.

#[global] Hint Rewrite @interp_bind : itree.

(** ** Composition of [interp] *)

Theorem interp_interp {E F G: iEvent}
  (f : E ~> itree F) (g : F ~> itree G) {R: Type} (t : itree E R):
    interp g (interp f t)
  = interp (fun _ e => interp g (f _ e)) t.
Proof.
  eapply bisim_is_eq.
  revert t. ginit. gcofix CIH. intros t.
  rewrite !(unfold_interp _ t).
  destruct (observe t); cbn.
  - rewrite interp_ret. gstep. constructor.
  - rewrite interp_tau. gstep. constructor. auto with paco.
  - rewrite interp_bind.
    guclo @eqit_clo_bind. econstructor. intros.
    rewrite interp_tau.
    gstep; constructor. auto with paco.
Qed.

Lemma interp_translate {E: iEvent} {F: iEvent} {G: iEvent} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g (translate f t) =
    interp (fun _ e => g _ (f _ e)) t.
Proof.
  eapply bisim_is_eq.
  revert t. ginit. gcofix CIH. intros t.
  rewrite unfold_translate.
  rewrite !unfold_interp. unfold _interp, translateF.
  destruct (observe t); cbn.
  - gfinal. right. unshelve eapply reflexivity.
    intros x. eapply paco2_mon_bot; eauto. apply eq_is_bisim. eauto.
  - gstep. constructor. gbase. apply CIH.
  - guclo @eqit_clo_bind; econstructor.
    intros ?. gstep; constructor; auto with paco.
Qed.

Lemma interp_iter' {E F: iEvent} (f : E ~> itree F) {I A: Type}
      (t1 : I -> itree E (I + A)%type)
      (t2 : I -> itree F (I + A)%type)
      (EQ_t : forall i, t2 i = interp f (t1 i))
  : forall (i: I),
    interp f (ITree.iter t1 i)
  = ITree.iter t2 i.
Proof.
  intros. eapply bisim_is_eq. revert i.
  ginit. gcofix CIH; intros i.
  rewrite !unfold_iter.
  rewrite !interp_bind.
  guclo @eqit_clo_bind. rewrite EQ_t. econstructor.
  intros [].
  - rewrite interp_tau; gstep; constructor; auto with paco.
  - rewrite interp_ret. gstep; constructor; auto.
Qed.

Lemma interp_iter {E F: iEvent} (f : E ~> itree F) {A B: Type}
      (t : A -> itree E (A + B)%type) a0 :
  interp f (ITree.iter t a0) = ITree.iter (fun a => interp f (t a)) a0.
Proof.
  apply interp_iter'. reflexivity.
Qed.

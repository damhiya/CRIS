(** * Theorems about [Interp.translate] *)

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
     Subevent
     Eqit
     EqAxiom
     EqitFacts
     Sum
     Interp.

Import ITreeNotations.

(* end hide *)

Section TranslateFacts.
Context {E : iEvent}.
Context {F : iEvent}.
Context {R : Type}.
Context (h : forall (T: Type), E T -> F T).

Local Notation translate := translate.

Lemma unfold_translate (t : itree E R) :
  (translate h t) = (translateF h (fun t => translate h t) (observe t)).
Proof.
  rewrite (itree_eta (translate _ _)). simpl.
  setoid_rewrite <-itree_eta. reflexivity.
Qed.

Lemma translate_ret : forall (r:R), translate h (Ret r) = Ret r.
Proof.
  intros r. rewrite unfold_translate, itree_eta. cbn. reflexivity.
Qed.

Lemma translate_tau : forall (t : itree E R), translate h (Tau t) = Tau (translate h t).
Proof.
  intros t. rewrite unfold_translate, itree_eta. cbn. reflexivity.
Qed.

Lemma translate_vis : forall (X: Type) (e:E X) (k : X -> itree E R),
    translate h (Vis e k) = Vis (h _ e) (fun x => translate h (k x)).
Proof.
  intros X e k. rewrite unfold_translate, itree_eta. cbn. reflexivity.
Qed.

Lemma translate_bind {S: Type} (t : itree E S) (k : S -> itree E R)
  :
  (translate h (x <- t ;; k x)) = (x <- translate h t;; translate h (k x))%itree.
Proof.
  eapply bisim_is_eq. revert S t k.
  ginit. gcofix CIH. intros s t k.
  gstep. red. simpl. destruct (observe t); cbn.
  - eapply Reflexive_eqitF. intros ?.
    gfinal. right. eapply paco2_mon_bot; eauto. eapply eq_is_bisim. eauto.
  - constructor. eauto with paco.
  - constructor. eauto with paco itree.
Qed.

(** Inversion principles *)

Lemma translate_Vis_inv {X: Type} (t: itree E R) (e': F X) k':
  translate h t = Vis e' k' ->
  exists (e: E X) k, t = Vis e k /\ e' = h _ e /\ (forall x, k' x = translate h (k x)).
Proof.
  intros. eapply eq_is_bisim in H.
  rewrite (itree_eta t) in H. setoid_rewrite (itree_eta t).
  desobs t Ht.
  { punfold H; inversion H. }
  { punfold H; inversion H; inversion CHECK. }
  { punfold H. red in H. simpl in *.
    inversion H. subst u. subst X0.
    dependent destruction H. dependent destruction H6.
    pclearbot. eexists _, _. split; eauto. split; eauto.
    intros. symmetry. eapply bisim_is_eq. apply REL.
  }
Qed.

End TranslateFacts.

Lemma translate_trigger {E F: iEvent} {G: iEvent} `{E -< F}
  (X: Type) (e: E X) (h: F ~> G)
  :
  translate h (trigger e) = trigger (h _ (subevent _ e)).
Proof.
  unfold trigger; rewrite translate_vis.
  do 2 f_equal. extensionality x. rewrite translate_ret. eauto.
Qed.

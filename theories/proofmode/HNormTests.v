From CRIS.common Require Import Common.
From CRIS.modules Require Import Sandbox.
From CRIS.proofmode Require Import HNormClasses HNorm HNormInstances.

(** Regression cases for the typeclass-based head normalizer. *)
Module HNormTests.

Local Ltac check_tactic_argument normalize :=
  lazymatch goal with
  | |- ?G =>
      let H := fresh "HNORM" in
      assert (H : G) by normalize; clear H; normalize
  end.

Section CORE.
  Context {E : Type -> Type} {A B C X : Type}.

  Example bind_ret (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. hnorm_itr. Qed.

  Example tactic_argument (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. check_tactic_argument ltac:(hnorm_itr). Qed.

  Example bind_tau (t : itree E A) (k : A -> itree E B) :
    (Tau t >>= k) = Tau (t >>= k).
  Proof. hnorm_itr. Qed.

  Example bind_vis (e : E X) (k : X -> itree E A)
      (l : A -> itree E B) :
    (Vis e k >>= l) = (ITree.trigger e >>= fun x => k x >>= l).
  Proof. hnorm_itr. Qed.

  Example nested_stuck_bind (t : itree E A) (k : A -> itree E A) :
    (((t >>= k) >>= k) >>= k) =
    (t >>= fun x => (k x >>= k) >>= k).
  Proof. hnorm_itr. Qed.

  (* Ordinary simplification is allowed inside a continuation; itree
     normalization must leave the inner Ret/bind redex untouched. *)
  Example beta_let_under_vis (e : E A) (k : A -> itree E B) :
    Vis e (fun x => let y := (fun z => z) x in Ret y >>= k) =
    (ITree.trigger e >>= fun x => Ret x >>= k).
  Proof. hnorm_itr. Qed.

  Example beta_after_reduce (x : A) (k : A -> itree E B) :
    (Ret x >>= fun y => let z := (fun u => u) y in Ret z >>= k) =
    k x.
  Proof. hnorm_itr. Qed.

  Example existential_rhs (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. etransitivity; [hnorm_itr|reflexivity]. Qed.

  Example existential_argument (x : A) (k : A -> itree E B) :
    exists y, (Ret y >>= k) = k x.
  Proof. eexists. hnorm_itr. Qed.

  Example evar_continuation (e : E A) (k : A -> itree E B) :
    Vis e k = (ITree.trigger e >>= k).
  Proof.
    evar (g : A -> itree E B).
    assert (H : Vis e g = (ITree.trigger e >>= g)) by hnorm_itr.
    let body := eval unfold g in g in is_evar body.
    instantiate (g := k). exact H.
  Qed.

  (* Conversion during typeclass search can unfold a local definition. *)
  Example local_function_definition (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof.
    pose (f := fun y : A => (Ret y : itree E A)).
    change ((f x >>= k) = k x). hnorm_itr.
  Qed.
End CORE.

Definition wrapped_ret {E A} (x : A) : itree E A := Ret x.
Arguments wrapped_ret {E A} x : simpl never.
Typeclasses Opaque wrapped_ret.

#[local] Instance HNormExpand_wrapped_ret {E A} (x : A) :
  HNormExpand (@wrapped_ret E A x) (Ret x).
Proof. constructor. reflexivity. Qed.

Example extension_expand {E A B} (x : A) (k : A -> itree E B) :
  (wrapped_ret x >>= k) = k x.
Proof. hnorm_itr. Qed.

Example local_expand {E A B} (t : itree E A) (x : A)
    (H : HNormExpand t (Ret x)) (k : A -> itree E B) :
  (t >>= k) = k x.
Proof. hnorm_itr. Qed.

Example local_context {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) K t)
    (x : A) (k : A -> itree E A) :
  K (Ret x >>= k) = K (k x).
Proof. hnorm_itr. Qed.

(* This context equality is not a conversion: its witness is essential. *)
Example local_context_nondef {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) (fun u => u) t)
    (x : A) (k : A -> itree E A) :
  K (Ret x >>= k) = k x.
Proof. hnorm_itr. Qed.

(* The selected child is not an argument of K x.  Its continuation has
   never been simplified by simplifying the original input. *)
Example local_context_constructed_child {E A B X}
    (K : A -> itree E B) (e : E X) (k : A -> itree E B)
    (HC : forall x,
      HNormContext (K x) (fun u => u)
        (Vis e (fun y => let p := (x, y) in Ret (fst p) >>= k))) x :
  K x = (ITree.trigger e >>= fun _ => Ret x >>= k).
Proof.
  etransitivity; [hnorm_itr|].
  lazymatch goal with
  | |- ?lhs = _ =>
      let expected := constr:(ITree.trigger e >>= fun _ => Ret x >>= k) in
      constr_eq lhs expected
  end.
  reflexivity.
Qed.

Example local_reduce {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) K t)
    (HR : forall x, HNormReduce K (Ret x) (Ret x) false) (x : A) :
  K (Ret x) = Ret x.
Proof. hnorm_itr. Qed.

(* Typeclass matching uses conversion, including function eta. *)
Example local_context_eta {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) (fun u => K u) t)
    (HR : forall x, HNormReduce K (Ret x) (Ret x) false) (x : A) :
  K (Ret x) = Ret x.
Proof. hnorm_itr. Qed.

Definition wrapped_state {E A B X} (e : E X) (x : A)
    (k : A -> itree E B) : itree E B :=
  Vis e (fun y => let p := (x, y) in Ret (fst p) >>= k) >>=
    fun u => Ret u.
Arguments wrapped_state {E A B X} e x k : simpl never.
Typeclasses Opaque wrapped_state.

#[local] Instance HNormExpand_wrapped_state {E A B X} (e : E X) (x : A)
    (k : A -> itree E B) :
  HNormExpand (wrapped_state e x k)
    (Vis e (fun y => let p := (x, y) in Ret (fst p) >>= k) >>=
       fun u => Ret u).
Proof. constructor. reflexivity. Qed.

(* Expansion introduces a context whose child still needs simplification.
   Check the actual output, not just convertibility of the final equality. *)
Example extension_expand_state {E A B X} (e : E X) (x : A)
    (k : A -> itree E B) :
  wrapped_state e x k =
    (ITree.trigger e >>= fun _ => (Ret x >>= k) >>= fun u => Ret u).
Proof.
  etransitivity; [hnorm_itr|].
  lazymatch goal with
  | |- ?lhs = _ =>
      let expected := constr:(ITree.trigger e >>=
        fun _ => (Ret x >>= k) >>= fun u => Ret u) in
      constr_eq lhs expected
  end.
  reflexivity.
Qed.

Definition wrapped_bool {E} (b : bool) : itree E bool := Ret b.
Arguments wrapped_bool {E} b : simpl never.
Typeclasses Opaque wrapped_bool.

#[local] Instance HNormExpand_wrapped_bool {E} b b'
    (H : HNormBool b b') :
  HNormExpand (@wrapped_bool E b) (Ret b').
Proof. destruct H as [->]. constructor. reflexivity. Qed.

Example local_bool_precedence (b : bool) (H : HNormBool b false) :
  (wrapped_bool b : itree coreE bool) = Ret false.
Proof. hnorm_itr. Qed.

Example or_true_left b :
  (wrapped_bool (true || b) : itree coreE bool) = Ret true.
Proof. hnorm_itr. Qed.

Example or_true_right b :
  (wrapped_bool (b || true) : itree coreE bool) = Ret true.
Proof. hnorm_itr. Qed.

Example and_false_right b :
  (wrapped_bool (b && false) : itree coreE bool) = Ret false.
Proof. hnorm_itr. Qed.

Section MASKS.
  Context {Σ : GRA}.

  Example sandbox_or_right b fn arg (k : Any.t -> itree crisE nat) :
    SB.sandbox (fun _ _ => b || true) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => b || true) (k x)).
  Proof. hnorm_itr. Qed.

  Example sandbox_local_bool b (H : HNormBool b true) fn arg
      (k : Any.t -> itree crisE nat) :
    SB.sandbox (fun _ _ => b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => b) (k x)).
  Proof. hnorm_itr. Qed.
End MASKS.

End HNormTests.

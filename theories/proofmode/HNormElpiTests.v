From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import FSpec ModTr LModTr SModTr Sandbox.
From CRIS.proofmode Require Import
  HNormClasses HNorm HNormInstances HNormElpi.

(* These examples specify the same output for both implementations. *)
Local Ltac check_hnorm :=
  lazymatch goal with
  | |- ?G =>
      let H := fresh "HNORM" in
      assert (H : G) by hnorm_itr; clear H; hnorm_itr_elpi
  end.

Section CORE.
  Context {E : Type -> Type} {A B C X : Type}.

  Example bind_ret (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. check_hnorm. Qed.

  Example bind_tau (t : itree E A) (k : A -> itree E B) :
    (Tau t >>= k) = Tau (t >>= k).
  Proof. check_hnorm. Qed.

  Example bind_vis (e : E X) (k : X -> itree E A)
      (l : A -> itree E B) :
    (Vis e k >>= l) = (ITree.trigger e >>= fun x => k x >>= l).
  Proof. check_hnorm. Qed.

  Example stuck_bind (t : itree E A) (k : A -> itree E B)
      (l : B -> itree E C) :
    ((t >>= k) >>= l) = (t >>= fun x => k x >>= l).
  Proof. check_hnorm. Qed.

  (* The Ret/bind redex in the continuation must remain untouched. *)
  Example under_vis (e : E A) (k : A -> itree E B) :
    Vis e (fun x => Ret x >>= k) =
    (ITree.trigger e >>= fun x => Ret x >>= k).
  Proof. check_hnorm. Qed.

  Example beta_let_under_vis (e : E A) (k : A -> itree E B) :
    Vis e (fun x => let y := (fun z => z) x in Ret y >>= k) =
    (ITree.trigger e >>= fun x => Ret x >>= k).
  Proof. check_hnorm. Qed.

  Example nested_stuck_bind (t : itree E A) (k : A -> itree E A) :
    (((t >>= k) >>= k) >>= k) =
    (t >>= fun x => (k x >>= k) >>= k).
  Proof. check_hnorm. Qed.

  Example existential_rhs (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. etransitivity; [hnorm_itr_elpi|reflexivity]. Qed.

  Example existential_argument (x : A) (k : A -> itree E B) :
    exists y, (Ret y >>= k) = k x.
  Proof. eexists. hnorm_itr_elpi. Qed.

  Example local_definition (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof. pose (y := x). check_hnorm. Qed.

  Example local_function_definition (x : A) (k : A -> itree E B) :
    (Ret x >>= k) = k x.
  Proof.
    pose (f := fun y : A => (Ret y : itree E A)).
    change ((f x >>= k) = k x).
    Fail hnorm_itr_elpi.
    unfold f. check_hnorm.
  Qed.

  Example evar_continuation (e : E A) (k : A -> itree E B) :
    Vis e k = (ITree.trigger e >>= k).
  Proof.
    evar (g : A -> itree E B).
    assert (H : Vis e g = (ITree.trigger e >>= g)) by hnorm_itr_elpi.
    let body := eval unfold g in g in is_evar body.
    instantiate (g := k). exact H.
  Qed.
End CORE.

(* Rules declared after importing HNormElpi are explicitly registered. *)
Definition wrapped_ret {E A} (x : A) : itree E A := Ret x.
Arguments wrapped_ret {E A} x : simpl never.
Typeclasses Opaque wrapped_ret.

#[local] Instance HNormExpand_wrapped_ret {E A} (x : A) :
  HNormExpand (@wrapped_ret E A x) (Ret x).
Proof. constructor. reflexivity. Qed.

Elpi HNormElpi.Register HNormExpand_wrapped_ret.

Example registered_expand {E A B} (x : A) (k : A -> itree E B) :
  (wrapped_ret x >>= k) = k x.
Proof. check_hnorm. Qed.

Example local_expand {E A B} (t : itree E A) (x : A)
    (H : HNormExpand t (Ret x)) (k : A -> itree E B) :
  (t >>= k) = k x.
Proof. check_hnorm. Qed.

Example local_context {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) K t)
    (x : A) (k : A -> itree E A) :
  K (Ret x >>= k) = K (k x).
Proof. check_hnorm. Qed.

(* Here the context equality is not a conversion: the witness is required. *)
Example local_context_nondef {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) (fun u => u) t)
    (x : A) (k : A -> itree E A) :
  K (Ret x >>= k) = k x.
Proof. check_hnorm. Qed.

Example local_reduce {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) K t)
    (HR : forall x, HNormReduce K (Ret x) (Ret x) false) (x : A) :
  K (Ret x) = Ret x.
Proof. check_hnorm. Qed.

(* Alpha matching does not identify K with its eta expansion. *)
Example local_context_eta {E A} (K : itree E A -> itree E A)
    (HC : forall t, HNormContext (K t) (fun u => K u) t)
    (HR : forall x, HNormReduce K (Ret x) (Ret x) false) (x : A) :
  K (Ret x) = Ret x.
Proof.
  Fail hnorm_itr_elpi.
  assert (HC' : forall t, HNormContext (K t) K t) by
    (intro t; exact (HC t)).
  check_hnorm.
Qed.

Definition wrapped_true (b : bool) := b || true.
Arguments wrapped_true b : simpl never.
Typeclasses Opaque wrapped_true.

#[local] Instance HNormBool_wrapped_true b :
  HNormBool (wrapped_true b) true | 1.
Proof. constructor. unfold wrapped_true. apply orb_true_r. Qed.

Definition wrapped_bool {E} (b : bool) : itree E bool := Ret b.
Arguments wrapped_bool {E} b : simpl never.
Typeclasses Opaque wrapped_bool.

(* The boolean result is an output, so an early reflexivity fallback wins. *)
#[local] Instance HNormExpand_wrapped_bool {E} b b'
    (H : HNormBool b b') :
  HNormExpand (@wrapped_bool E b) (Ret b').
Proof. destruct H as [->]. constructor. reflexivity. Qed.

Elpi HNormElpi.Register HNormExpand_wrapped_bool.

(* Re-registering a class preserves priorities over its existing fallback. *)
Elpi HNormElpi.Register HNormBool.

Example registered_priority (b : bool) :
  (wrapped_bool (wrapped_true b) : itree coreE bool) = Ret true.
Proof. check_hnorm. Qed.

Example local_bool_precedence (b : bool) (H : HNormBool b false) :
  (wrapped_bool b : itree coreE bool) = Ret false.
Proof. check_hnorm. Qed.

Section BOOL.
  Example and_false_left b :
    (wrapped_bool (false && b) : itree coreE bool) = Ret false.
  Proof. check_hnorm. Qed.

  Example and_false_right b :
    (wrapped_bool (b && false) : itree coreE bool) = Ret false.
  Proof. check_hnorm. Qed.

  Example or_and_identities b c :
    (wrapped_bool ((b || false) && (c || true)) : itree coreE bool) =
    Ret b.
  Proof. check_hnorm. Qed.

  Example and_or_identities b c :
    (wrapped_bool ((b && true) || (false && c)) : itree coreE bool) =
    Ret b.
  Proof. check_hnorm. Qed.

  Example or_congruence b c :
    (wrapped_bool ((b && true) || (c && true)) : itree coreE bool) =
    Ret (b || c).
  Proof. check_hnorm. Qed.

  Example and_congruence b c :
    (wrapped_bool ((b || false) && (c || false)) : itree coreE bool) =
    Ret (b && c).
  Proof. check_hnorm. Qed.
End BOOL.

Section CRIS.
  Context {Σ : GRA}.

  Example assume_bind P (t : itree crisE nat)
      (k : nat -> itree crisE nat) :
    (assumeK P t >>= k) = (assume P;;; t >>= k).
  Proof. check_hnorm. Qed.

  Example guarantee_bind P (t : itree crisE nat)
      (k : nat -> itree crisE nat) :
    (guaranteeK P t >>= k) = (guarantee P;;; t >>= k).
  Proof. check_hnorm. Qed.

  Example assume_expand P (k : unit -> itree crisE nat) :
    (assume P >>= k) = (assume P;;; Ret tt >>= k).
  Proof. check_hnorm. Qed.

  Example guarantee_expand P (k : unit -> itree crisE nat) :
    (guarantee P >>= k) = (guarantee P;;; Ret tt >>= k).
  Proof. check_hnorm. Qed.

  Example unwrap_upcast (x : nat) :
    (unwrapU (Any.downcast (Any.upcast x)) : itree crisE nat) = Ret x.
  Proof. check_hnorm. Qed.

  Example unwrap_small_upcast (x : nat) :
    (unwrapU (SAny.downcast (SAny.upcast x)) : itree crisE nat) = Ret x.
  Proof. check_hnorm. Qed.

  Example unwrapN_upcast (x : nat) :
    (unwrapN (Any.downcast (Any.upcast x)) : itree crisE nat) = Ret x.
  Proof. check_hnorm. Qed.

  Example unwrapN_small_upcast (x : nat) :
    (unwrapN (SAny.downcast (SAny.upcast x)) : itree crisE nat) = Ret x.
  Proof. check_hnorm. Qed.

  Example unwrap_unknown (x : option nat) (k : nat -> itree crisE nat) :
    (unwrapUK x k >>= k) = (unwrapU x >>= fun y => k y >>= k).
  Proof. check_hnorm. Qed.

  Example unwrap_expand (x : option nat) (k : nat -> itree crisE nat) :
    (unwrapU x >>= k) = (unwrapU x >>= fun y => Ret y >>= k).
  Proof. check_hnorm. Qed.

  Example unwrapN_expand (x : option nat) (k : nat -> itree crisE nat) :
    (unwrapN x >>= k) = (unwrapN x >>= fun y => Ret y >>= k).
  Proof. check_hnorm. Qed.

  Example realupdate_expand pp (k : unit -> itree crisE nat) :
    (RealUpdate pp >>= k) =
    (RealUpdate pp >>= fun x => Ret x >>= k).
  Proof. check_hnorm. Qed.

  Example realupdate_bind pp (k : unit -> itree crisE nat)
      (l : nat -> itree crisE nat) :
    (RealUpdateK pp k >>= l) =
    (RealUpdate pp >>= fun x => k x >>= l).
  Proof. check_hnorm. Qed.

  Example put_expand k (v : nat) :
    (cput k v : itree crisE unit) =
    (trigger (SPut k (Any.upcast v)) >>= fun x => Ret x).
  Proof. check_hnorm. Qed.

  Example get_expand k :
    (cgetU k : itree crisE nat) =
    (trigger (SGet k) >>= fun v => Ret v >>= fun v =>
       unwrapU (Any.downcast v)).
  Proof. check_hnorm. Qed.

  Example getN_expand k :
    (cgetN k : itree crisE nat) =
    (trigger (SGet k) >>= fun v => Ret v >>= fun v =>
       unwrapN (Any.downcast v)).
  Proof. check_hnorm. Qed.

  Example cfunU_expand (ft : fntyp_t nat nat)
      (body : nat -> itree crisE nat) (x : nat) :
    cfunU ft body (Any.upcast x) =
    (v <- body x;; Ret (Any.upcast v)).
  Proof. check_hnorm. Qed.

  Example cfunN_expand (ft : fntyp_t nat nat)
      (body : nat -> itree crisE nat) (x : nat) :
    cfunN ft body (Any.upcast x) =
    (v <- body x;; Ret (Any.upcast v)).
  Proof. check_hnorm. Qed.

  Example ccallU_expand (fs : fnsig_t nat nat) (x : nat) :
    (ccallU fs x : itree crisE nat) =
    (trigger (Call (fn_name fs) (Any.upcast x)) >>= fun v =>
       Ret v >>= fun v => unwrapU (Any.downcast v)).
  Proof. check_hnorm. Qed.

  Example ccallN_expand (fs : fnsig_t nat nat) (x : nat) :
    (ccallN fs x : itree crisE nat) =
    (trigger (Call (fn_name fs) (Any.upcast x)) >>= fun v =>
       Ret v >>= fun v => unwrapN (Any.downcast v)).
  Proof. check_hnorm. Qed.

  Example trivial_expand a :
    @fbody_trivial Σ a =
    (trigger (Choose Any.t) >>= fun v => Ret v).
  Proof. check_hnorm. Qed.

  Example hoarecall_expand omsk fn arg :
    @SModTr.HoareCall Σ None omsk fn arg =
    (trigger (Call fn arg) >>= fun v => Ret v).
  Proof. check_hnorm. Qed.

  Example ub_expand :
    (triggerUB : itree crisE nat) =
    (trigger (Take False) >>= fun v =>
       Ret v >>= fun x => match x : False with end).
  Proof. check_hnorm. Qed.

  Example nb_expand :
    (triggerNB : itree crisE nat) =
    (trigger (Choose False) >>= fun v =>
       Ret v >>= fun x => match x : False with end).
  Proof. check_hnorm. Qed.

  Example sandbox_or_left (b : bool) fn arg
      (k : Any.t -> itree crisE nat) :
    SB.sandbox (fun _ _ => true || b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => true || b) (k x)).
  Proof. check_hnorm. Qed.

  Example sandbox_or_right (b : bool) fn arg
      (k : Any.t -> itree crisE nat) :
    SB.sandbox (fun _ _ => b || true) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => b || true) (k x)).
  Proof. check_hnorm. Qed.

  Example sandbox_local_bool (b : bool) (H : HNormBool b true) fn arg
      (k : Any.t -> itree crisE nat) :
    SB.sandbox (fun _ _ => b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => b) (k x)).
  Proof. check_hnorm. Qed.

  Example modtr_ret (x : nat) : ModTr.trans (Ret x) = Ret x.
  Proof. check_hnorm. Qed.

  Example nested_interpreters msk (t : itree crisE nat) :
    ModTr.trans (SB.sandbox msk (Tau t)) =
    Tau (ModTr.trans (SB.sandbox msk t)).
  Proof. check_hnorm. Qed.

  Example modtr_assume P (t : itree crisE nat) :
    ModTr.trans (assumeK P t) = (assume P;;; ModTr.trans t).
  Proof. check_hnorm. Qed.

  Example modtr_call fn arg (k : Any.t -> itree crisE nat) :
    ModTr.trans (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x => ModTr.trans (k x)).
  Proof. check_hnorm. Qed.

  Example lmodtr_ret (st : lstateT Σ) (x : nat) :
    LModTr.interp_stateE nat (Ret x : itree (lstateE Σ +' coreE) nat) st =
    Ret (st, x).
  Proof. check_hnorm. Qed.

  Example lmodtr_put (st st' : lstateT Σ) :
    LModTr.interp_stateE unit
      (trigger (sPut st') : itree (lstateE Σ +' coreE) unit) st =
    Tau (LModTr.interp_stateE unit (Ret tt) st').
  Proof. check_hnorm. Qed.

  Example lmodtr_get (st : lstateT Σ) :
    LModTr.interp_stateE (lstateT Σ)
      (trigger sGet : itree (lstateE Σ +' coreE) (lstateT Σ)) st =
    Tau (LModTr.interp_stateE (lstateT Σ) (Ret st) st).
  Proof. check_hnorm. Qed.
End CRIS.

Section SMOD.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Example smodtr_ret sp (x : nat) : SModTr.trans sp (Ret x) = Ret x.
  Proof. check_hnorm. Qed.

  Example smodtr_tau sp (t : itree crisE nat) :
    SModTr.trans sp (Tau t) = Tau (SModTr.trans sp t).
  Proof. check_hnorm. Qed.

  Example smodtr_get sp k (l : Any.t -> itree crisE nat) :
    SModTr.trans sp (vis (SGet k) l) =
    (trigger (SGet k) >>= fun x => SModTr.trans sp (l x)).
  Proof. check_hnorm. Qed.
End SMOD.

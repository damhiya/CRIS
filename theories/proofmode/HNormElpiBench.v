From elpi Require Import elpi.
From CRIS.common Require Import Common.
From CRIS.modules Require Import Sandbox.
From CRIS.proofmode Require Import HNorm HNormInstances HNormElpi.

(** Small, reproducible comparisons.  Term construction is outside [Time].
    Re-run this file with [rocq compile] to repeat the measurements; [make]
    intentionally skips an up-to-date file.  These are microbenchmarks, not
    a claim about whole-project build time. *)
Module HNormElpiBench.

(** Return the original goal, without inspecting it or constructing a proof.
    This still enters Elpi with the Rocq goal and its local context. *)
Elpi Tactic hnorm_elpi_noop.
Elpi Accumulate lp:{{
  solve G [seal G].
}}.
Ltac hnorm_elpi_noop := elpi hnorm_elpi_noop.

(** Input conversion happens before either entrypoint.  This variant skips
    the default per-goal context opening used by [solve], returning the
    original sealed goals directly.  Neither variant constructs a proof
    term to convert back to Rocq. *)
Elpi Tactic hnorm_elpi_noop_sealed.
Elpi Accumulate lp:{{
  msolve GS GS.
}}.
Ltac hnorm_elpi_noop_sealed := elpi hnorm_elpi_noop_sealed.

(** Each invocation crosses the Rocq/Elpi boundary.  Do not move the loop
    inside Elpi: that would only pay the conversion cost once.  Warm up
    before timing, and compare with the same Ltac loop around [idtac].
    The difference includes invocation and goal/context marshalling, not
    just term conversion in isolation.  All loops leave the goal intact. *)
Ltac bench_elpi_noop :=
  hnorm_elpi_noop;
  hnorm_elpi_noop_sealed;
  idtac "idtac / 1000 calls";
  time (do 1000 idtac);
  idtac "Elpi no-op (solve) / 1000 calls";
  time (do 1000 hnorm_elpi_noop);
  idtac "Elpi no-op (msolve) / 1000 calls";
  time (do 1000 hnorm_elpi_noop_sealed).

Ltac warm_hnorm normalize :=
  lazymatch goal with
  | |- ?G =>
      let H := fresh "WARM" in
      assert (H : G) by normalize; clear H
  end.

Fixpoint ret_chain (n : nat) : itree coreE nat :=
  match n with
  | O => Ret 0
  | S n => ret_chain n >>= fun x => Ret x
  end.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 10 / warm Ltac". Time hnorm_itr.
Qed.
Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 10 / warm Elpi". Time hnorm_itr_elpi.
Qed.
Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain].
  idtac "ret_chain 10". bench_elpi_noop.
  hnorm_itr.
Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 50 / warm Ltac". Time hnorm_itr.
Qed.
Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 50 / warm Elpi". Time hnorm_itr_elpi.
Qed.
Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain].
  idtac "ret_chain 50". bench_elpi_noop.
  hnorm_itr.
Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 100 / warm Ltac". Time hnorm_itr.
Qed.
Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 100 / warm Elpi". Time hnorm_itr_elpi.
Qed.
Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain].
  idtac "ret_chain 100". bench_elpi_noop.
  hnorm_itr.
Qed.

(** Opaque, non-identity continuations keep every returned value relevant.
    Both the chain and its expected result are constructed before timing.
    The untimed proof warms the same tactic on exactly the same goal.
    [Time Qed] measures closing the entire proof, including its warmup. *)
Fixpoint map_chain (n : nat) (f : nat -> nat) (x : nat) : itree coreE nat :=
  match n with
  | O => Ret x
  | S n => map_chain n f x >>= fun y => Ret (f y)
  end.

Fixpoint map_result (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n => f (map_result n f x)
  end.

Section NONIDENTITY.
  Context (f : nat -> nat) (x : nat).

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 50 / warm Ltac". Time hnorm_itr.
  Time Qed.

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 50 / warm Elpi". Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 100 / warm Ltac". Time hnorm_itr.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 100 / warm Elpi". Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 200 / warm Ltac". Time hnorm_itr.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 200 / warm Elpi". Time hnorm_itr_elpi.
  Time Qed.
End NONIDENTITY.

Section MASKS.
  Context {Σ : GRA}.

  Fixpoint mask_chain (n : nat) (b : bool) : bool :=
    match n with
    | O => true
    | S n => b || mask_chain n b
    end.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr).
    idtac "mask_chain 5 / warm Ltac". Time hnorm_itr.
  Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "mask_chain 5 / warm Elpi". Time hnorm_itr_elpi.
  Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain].
    idtac "mask_chain 5". bench_elpi_noop.
    hnorm_itr.
  Qed.
End MASKS.

End HNormElpiBench.

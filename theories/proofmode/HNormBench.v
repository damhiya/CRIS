From CRIS.common Require Import Common.
From CRIS.modules Require Import Sandbox.
From CRIS.proofmode Require Import
  HNormClasses HNorm HNormInstances HNormElpi.

(** Compare original Ltac, current Ltac, and Elpi in one process.
    The baseline is copied from HNorm.v at commit 51699e56, with only its
    tactic names changed.  It does not call the current implementation.

    A shared, untimed warmup runs all three tactics on a larger input first:
    otherwise early heap/GC effects can dominate whichever tactic runs
    later.  Term construction and a proof of the same goal with the same
    tactic are also outside [Time].  [Time Qed] measures the complete proof,
    including its warmup.  Compile this file directly to repeat timings:
    [make] intentionally skips an up-to-date file.  These microbenchmarks
    do not measure whole-project build time.  A second pass reverses the
    original/current/Elpi order of each group to balance order effects. *)
Module HNormBench.

Local Ltac old_hnorm_itr_core :=
  simpl;
  try (notypeclasses refine (HNormExpand_apply _ _); [tc_solve|]);
  tryif notypeclasses refine (HNormContext_apply _ _ _); [tc_solve|] then
    lazymatch goal with
    | |- HNormContextRes ?K ?b ?b' ?rhs =>
        econstructor;
        [ old_hnorm_itr_core
        | tryif notypeclasses refine
            (@HNormReduce_apply _ _ K b' _ _ _ _ _); [tc_solve|] then
            lazymatch goal with
            | |- HNormReduceRes ?b true ?rhs =>
                econstructor; old_hnorm_itr_core
            | |- HNormReduceRes ?b false ?rhs =>
                econstructor; reflexivity
            end
          else
            reflexivity
        ]
    end
  else
    reflexivity.

Local Ltac old_hnorm_itr :=
  etransitivity;
  [ old_hnorm_itr_core
  | try (notypeclasses refine (HNormFinish_apply _ _); [tc_solve|]);
    reflexivity
  ].

Local Ltac warm_hnorm normalize :=
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

Goal ret_chain 200 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  warm_hnorm ltac:(hnorm_itr). hnorm_itr_elpi.
Qed.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 10 / warm original / forward".
  Time old_hnorm_itr.
Time Qed.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 10 / warm current / forward".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 10 / warm Elpi / forward".
  Time hnorm_itr_elpi.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 50 / warm original / forward".
  Time old_hnorm_itr.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 50 / warm current / forward".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 50 / warm Elpi / forward".
  Time hnorm_itr_elpi.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 100 / warm original / forward".
  Time old_hnorm_itr.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 100 / warm current / forward".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 100 / warm Elpi / forward".
  Time hnorm_itr_elpi.
Time Qed.

(** A local, opaque function keeps every non-identity return relevant. *)
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
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 50 / warm original / forward".
    Time old_hnorm_itr.
  Time Qed.

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 50 / warm current / forward".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 50 / warm Elpi / forward".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 100 / warm original / forward".
    Time old_hnorm_itr.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 100 / warm current / forward".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 100 / warm Elpi / forward".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 200 / warm original / forward".
    Time old_hnorm_itr.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 200 / warm current / forward".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 200 / warm Elpi / forward".
    Time hnorm_itr_elpi.
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
    intros. cbn [mask_chain]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "mask_chain 5 / warm original / forward".
    Time old_hnorm_itr.
  Time Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr).
    idtac "mask_chain 5 / warm current / forward".
    Time hnorm_itr.
  Time Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "mask_chain 5 / warm Elpi / forward".
    Time hnorm_itr_elpi.
  Time Qed.
End MASKS.

(* Repeat the same cases in Elpi/current/original order. *)
Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 10 / warm Elpi / reverse".
  Time hnorm_itr_elpi.
Time Qed.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 10 / warm current / reverse".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 10 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 10 / warm original / reverse".
  Time old_hnorm_itr.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 50 / warm Elpi / reverse".
  Time hnorm_itr_elpi.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 50 / warm current / reverse".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 50 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 50 / warm original / reverse".
  Time old_hnorm_itr.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
  idtac "ret_chain 100 / warm Elpi / reverse".
  Time hnorm_itr_elpi.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(hnorm_itr).
  idtac "ret_chain 100 / warm current / reverse".
  Time hnorm_itr.
Time Qed.

Goal ret_chain 100 = Ret 0.
Proof.
  cbn [ret_chain]. warm_hnorm ltac:(old_hnorm_itr).
  idtac "ret_chain 100 / warm original / reverse".
  Time old_hnorm_itr.
Time Qed.

Section NONIDENTITY_REVERSE.
  Context (f : nat -> nat) (x : nat).

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 50 / warm Elpi / reverse".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 50 / warm current / reverse".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 50 f x = Ret (map_result 50 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 50 / warm original / reverse".
    Time old_hnorm_itr.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 100 / warm Elpi / reverse".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 100 / warm current / reverse".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 100 f x = Ret (map_result 100 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 100 / warm original / reverse".
    Time old_hnorm_itr.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "map_chain 200 / warm Elpi / reverse".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(hnorm_itr).
    idtac "map_chain 200 / warm current / reverse".
    Time hnorm_itr.
  Time Qed.

  Goal map_chain 200 f x = Ret (map_result 200 f x).
  Proof.
    cbn [map_chain map_result]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "map_chain 200 / warm original / reverse".
    Time old_hnorm_itr.
  Time Qed.
End NONIDENTITY_REVERSE.

Section MASKS_REVERSE.
  Context {Σ : GRA}.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr_elpi).
    idtac "mask_chain 5 / warm Elpi / reverse".
    Time hnorm_itr_elpi.
  Time Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(hnorm_itr).
    idtac "mask_chain 5 / warm current / reverse".
    Time hnorm_itr.
  Time Qed.

  Goal forall (b : bool) fn arg (k : Any.t -> itree crisE nat),
    SB.sandbox (fun _ _ => mask_chain 5 b) (vis (Call fn arg) k) =
    (trigger (Call fn arg) >>= fun x =>
       SB.sandbox (fun _ _ => mask_chain 5 b) (k x)).
  Proof.
    intros. cbn [mask_chain]. warm_hnorm ltac:(old_hnorm_itr).
    idtac "mask_chain 5 / warm original / reverse".
    Time old_hnorm_itr.
  Time Qed.
End MASKS_REVERSE.

End HNormBench.

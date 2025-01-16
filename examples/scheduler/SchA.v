Require Import CRIS.

Require Import SchHeader.

Set Implicit Arguments.

Module SchA. Section SchA.
  Context {Σ: GRA}.

  Definition _spawn : (nat * string * SAny.t) -> itree hmodE unit :=
    fun '(mtid, fn, args) =>
      trigger (Yield mtid);;;
      trigger (Call fn args↑);;;
      Sch.terminate
  .

  Definition spawn : (string * SAny.t) -> itree hmodE nat :=
    fun '(fn, args) =>
      mid <- trigger Tid;;
      tid <- trigger (Spawn SchName._spawn (mid, fn, args)↑);;
      Ret tid
  .

  Definition yield: unit -> itree hmodE unit :=
    fun _ =>
      tid <- trigger (Choose nat);;
      trigger (Yield tid)
  .

  Definition join: nat -> itree hmodE (option SAny.t) :=
    fun _ =>
      Sch.yield;;;
      trigger (Choose (option SAny.t))
  .

End SchA. End SchA.

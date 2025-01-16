(* Require Import CRIS.

Require Import SchHeader SchASpec SchGInv.

Set Implicit Arguments.

Module SchA.
Section A.
  Context `{_W: @sinvG Σ Γ α β τ, !SchAS.G Γ}.

  Notation iProp := (iProp Σ).

  Variable univ: positive.

  Variable StbFun: Sk.t -> string -> option fspec.
  Variable GlobalStb: Sk.t -> string -> option fspec.

  Definition scopes := ["Sch"].

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

  Definition fnsems (sk: Sk.t) :=
    [(SchName._spawn, (scopes, mk_specbody (SchAS._spawn_spec univ sk StbFun) (cfunU _spawn)));
     (SchName.spawn, (scopes, mk_specbody (SchAS.spawn_spec univ sk StbFun) (cfunU spawn)));
     (SchName.yield, (scopes, mk_specbody (SchAS.yield_spec univ) (cfunU yield)));
     (SchName.join, (scopes, mk_specbody (SchAS.join_spec univ) (cfunU join)))].

  Program Definition Sem (sk: Sk.t): SModSem.t :=
  {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems sk;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: SMod.t :=
  {|
    SMod.modsem := fun sk => Sem sk;
    SMod.sk := SchSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp :=
    fun _ => (SchAS.initial_threads)%I.
  
  Definition t := Seal.sealing CRIS (SMod.to_hmod (sch_ginv univ) GlobalStb Mod).

End A.
End SchA. *)

Require Import Coqlib ITreelib.
Require Import ImpPrelude.
Require Import Events.
(* Require Import Behavior. *)
Require Import SMod HMod.
Require Import Skeleton.
Require Import STB IPM ITactics.
Require Import RingHeader.
Require Import CellioHeader.

From iris.algebra Require Import excl_auth.

Set Implicit Arguments.

Module CellioA. Section CellioA.
  Context {Σ : GRA.t}.
  Definition set: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      i <- trigger (@IO _ Z "Input" tt);;
      trigger (Guarantee (CellioA.cell i));;;
      Ret tt↑.
  
  Definition get: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      trigger (Guarantee (CellioA.cell x));;;
      Ret x↑.

  Class G Σ := { #[local] RA_inG :: GRA.inG (excl_authR ZO) Σ }.

  Context `{!G Σ}.
  Local Notation iProp := (iProp Σ).

  Definition auth (v : Z) : iProp :=
    Seal.sealing "CRIS"
      (OwnM (●E v)).

  Definition cell (v : Z) : iProp :=
    Seal.sealing "CRIS"
      OwnM (◯E v).

  Definition scopes := [CellioName.mn].

  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellioName.set, (scopes, mk_specbody fspec_trivial set));
     (CellioName.get, (scopes, mk_specbody fspec_trivial get))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := CellioSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp :=
    λ _, CellioA.auth 0.

  Variable GI: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "CRIS" (SMod.to_hmod GI GlobalStb Mod).
End CellioA. End CellioA.
(* Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import RingHeader.
Require Import CellioHeader.

Set Implicit Arguments.

Module CellioR.
Section CellioR.
  Context `{Σ: GRA.t}.

  Definition cellRA: URA.t := (Excl.t Z)%ra.
  Global Instance RA: URA.t := (Auth.t cellRA).
  Context `{@GRA.inG RA Σ}.

  Definition cellraw_r (v: Z) : cellRA :=
    (Excl.just v).
  Definition cell_r (v: Z) : RA :=
    (Auth.white (cellraw_r v)).
  Definition cell (v: Z): iProp :=
    Seal.sealing "ccr"
      (OwnM (cell_r v)).
  Definition auth_r (v: Z) : RA :=
    Auth.black (cellraw_r v).
  Definition auth (v: Z) : iProp :=
    Seal.sealing "ccr"
      (OwnM (auth_r v)).

End CellioR.
End CellioR.

Module CellioRA.
  Class t
    `{Σ: GRA.t}
    `{@GRA.inG CellioR.RA Σ}
    := CellioRA: unit.
End CellioRA.

Module CellioA.
Section CellioA.
  Context `{_W: CellioRA.t}.  

  Definition scopes := [CellioName.mn].

  Definition set: Any.t -> itree hmodE Any.t :=
    fun _ =>
      x <- trigger (Take Z);;
      trigger (Assume (CellioR.cell x));;;
      i <- trigger (@IO _ Z "Input" tt);;
      trigger (Guarantee (CellioR.cell i));;;
      Ret tt↑
  .
  
  Definition get: Any.t -> itree hmodE Any.t :=
    fun _ =>
      x <- trigger (Take Z);;
      trigger (Assume (CellioR.cell x));;;
      trigger (Guarantee (CellioR.cell x));;;
      Ret x↑
  .
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellioName.set, (scopes, mk_specbody fspec_trivial set));
     (CellioName.get, (scopes, mk_specbody fspec_trivial get))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := CellioSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => (CellioR.auth 0)%I.

  Variable GI: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GI GlobalStb Mod).

End CellioA.
End CellioA. *)

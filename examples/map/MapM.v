Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import MapHeader MapMSpec.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.


(*** module M Map
private map := (fun k => 0)
private size := 0

def init(sz: int) ≡
  size := sz

def get(k: int): int ≡
  assume(0 ≤ k < size)
  return map[k]

def set(k: int, v: int) ≡
  assume(0 ≤ k < size)
  map := map[k ← v]

def set_by_user(k: int) ≡
  set(k, input())
***)

Module MapM.
Section M.
  Context `{_W: CtxWD.t}.
  Context `{_M: MapMR.t (Γ:=Γ)}.

  Definition init: list val -> itree smodE val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, _) := data in
      _ <- pput (f, sz);;
      Ret Vundef
  .

  Definition get: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, sz) := data in
      _ <- assume(0 <= k < sz)%Z;;
      Ret (Vint (f k))
  .

  Definition set: list val -> itree smodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, sz) := data in
      assume(0 <= k < sz)%Z;;;
      _ <- pput (<[k:=v]> f, sz);;
      Ret Vundef
  .

  Definition set_by_user: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([]: list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems: list (string * fspecbody) :=
    [(MapName.init, mk_specbody MapMS.init_spec (cfunU init));
     (MapName.get, mk_specbody MapMS.get_spec (cfunU get));
     (MapName.set, mk_specbody MapMS.set_spec (cfunU set));
     (MapName.set_by_user, mk_specbody MapMS.set_by_user_spec (cfunU set_by_user))].

  Definition Sem: SModSem.t := {|
    SModSem.fnsems := fnsems;
    SModSem.initial_cond := True%I;
    SModSem.initial_st := (fun (_: Z) => 0%Z, 0%Z)↑;
  |}
  .

  Definition Mod: SMod.t := {|
    SMod.get_modsem := fun _ => Sem;
    SMod.sk := MapSK.t;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GlobalStb Mod).
  
End M.
End MapM.


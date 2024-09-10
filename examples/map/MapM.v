Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
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

  Definition scopes := ["Map"].
  Definition v_size := "Map" ↯ "size".
  Definition v_map := "Map" ↯ "map".
  
  Definition init: list val -> itree smodE val :=
    fun varg =>
      `size: Z <- (pargs [Tint] varg)?;;
      cput v_size size;;;
      Ret Vundef
  .
  
  Definition get: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      size <- cgetU v_size;;
      f <- cgetU v_map;;
      assume(0 <= k < size)%Z;;;
      Ret (Vint (f k))
  .

  Definition set: list val -> itree smodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      size <- cgetU v_size;;
      f <- cgetU v_map;;
      assume(0 <= k < size)%Z;;;
      cput v_map (<[k:=v]> (f: Z->Z));;;
      Ret Vundef
  .

  Definition set_by_user: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([]: list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems :=
    [(MapName.init, (scopes, mk_specbody MapMS.init_spec (cfunU init)));
     (MapName.get, (scopes, mk_specbody MapMS.get_spec (cfunU get)));
     (MapName.set, (scopes, mk_specbody MapMS.set_spec (cfunU set)));
     (MapName.set_by_user, (scopes, mk_specbody MapMS.set_by_user_spec (cfunU set_by_user)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_size,0%Z↑);
                           (v_map,(fun (_: Z) => 0%Z)↑)];
  |}
  .
  Solve All Obligations with prove_scope.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem; 
    SMod.sk := MapSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => emp%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End M.
End MapM.


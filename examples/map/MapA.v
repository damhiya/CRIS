Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import MapHeader MapASpec MapMSpec.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.


(*** module A Map
private map := (fun k => 0)

def init(sz: int) ≡
  skip

def get(k: int): int ≡
  return map[k]

def set(k: int, v: int) ≡
  map := map[k ← v]

def set_by_user(k: int) ≡
  set(k, input())
***)

Module MapA.
Section A.
  Context `{_W: CtxWD.t}.
  Context `{_A: MapAR.t (Γ:=Γ)}.
  Context `{_M: MapMR.t (Γ:=Γ)}.
  
  Definition init: list val -> itree smodE val :=
    fun varg =>
      Ret Vundef
  .

  Definition set: list val -> itree smodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      f <- pget;;
      _ <- pput (<[k:=v]> (f: Z->Z));;
      Ret Vundef
  .

  Definition get: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      f <- pget;;
      Ret (Vint (f k))
  .

  Definition set_by_user: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([]: list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems: list (string * fspecbody) :=
    [(MapName.init, mk_specbody MapAS.init_spec (cfunU init));
     (MapName.get, mk_specbody MapAS.get_spec (cfunU get));
     (MapName.set, mk_specbody MapAS.set_spec (cfunU set));
     (MapName.set_by_user, mk_specbody MapAS.set_by_user_spec (cfunU set_by_user))].

  Variable initial_condM: iProp.
  
  Definition Sem : SModSem.t := {|
    SModSem.fnsems := fnsems;
    SModSem.initial_cond := (MapAS.initial_map ∗ MapMS.pending ∗ initial_condM)%I;
    SModSem.initial_st := (fun (_: Z) => 0%Z)↑;
  |}
  .

  Definition Mod : SMod.t := {|
    SMod.get_modsem := fun _ => Sem;
    SMod.sk := MapSK.t;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _t: HMod.t := (SMod.to_hmod GlobalStb Mod).
  Definition t := _t.

  Lemma unfold: t = _t.
  Proof. eauto. Qed.

  Global Opaque t.

End A.
End MapA.


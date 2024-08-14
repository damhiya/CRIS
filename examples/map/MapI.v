Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod.
Require Import Skeleton.
Require Import MapHeader.
Require Import PCM.
Require Import STB IPM.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.


(*** module I Map
private data := NULL

def init(sz: int) ≡
  data := calloc(sz)

def get(k: int): int ≡
  return *(data + k)

def set(k: int, v: int) ≡
  *(data + k) := v

def set_by_user(k: int) ≡
  set(k, input())
***)

Module MapI.
Section I.
  Local Open Scope string_scope.
  Context `{_W: CtxWD.t}.
  
  Definition init: list val -> itree hmodE val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `r: val <- ccallU "alloc" [Vint sz];;
      pput r;;;
      _ <- (ITree.iter
              (fun i =>
                 if (Z_lt_le_dec i sz)
                 then
                   vptr <- (vadd r (Vint (i * 8)))?;;
                   `r: val <- ccallU "store" [vptr; Vint 0];;
                   Ret (inl (i + 1)%Z)
                 else
                   Ret (inr tt)) 0%Z);;
      Ret Vundef
  .

  Definition get: list val -> itree hmodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger sGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      `r: val <- ccallU "load" [vptr];; r <- (unint r)?;;
      Ret (Vint r)
  .

  Definition set: list val -> itree hmodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger sGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      `_: val <- ccallU "store" [vptr; Vint v];;
      Ret Vundef
  .

  Definition set_by_user: list val -> itree hmodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([]: list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems :=
    [(MapName.init, cfunU init);
     (MapName.get, cfunU get);
     (MapName.set, cfunU set);
     (MapName.set_by_user, cfunU set_by_user)].
  
  Definition Sem: HModSem.t := {|
    HModSem.fnsems := fnsems;
    HModSem.initial_st := Vnullptr↑;
    HModSem.initial_cond := True%I;
  |}
  .

  Definition Mod: HMod.t := {|
    HMod.get_modsem := fun _ => Sem;
    HMod.sk := MapSK.t;
  |}
  .
  Definition _t := Mod.
  Definition t := _t.
  
  Lemma unfold: t = _t.
  Proof. eauto. Qed.

  Global Opaque t.

End I.
End MapI.

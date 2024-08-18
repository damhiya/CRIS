Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod PMod.
Require Import Skeleton.
Require Import MapHeader.
Require Import PCM.
Require Import STB IPM ITactics.


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
  
  Definition init: list val -> itree pmodE val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `hptr: val <- ccallU "alloc" [Vint sz];;
      trigger (SPut "hptr" hptr↑);;;
      (ITree.iter
         (fun i =>
            if (Z_lt_le_dec i sz)
            then
              vptr <- (vadd hptr (Vint (i * 8)))?;;
              `_: val <- ccallU "store" [vptr; Vint 0];;
              Ret (inl (i + 1)%Z)
            else
              Ret (inr tt)) 0%Z);;;
      Ret Vundef
  .

  Definition get: list val -> itree pmodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      hptr <- trigger (SGet "hptr");; hptr <- hptr↓?;;
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      `r: val <- ccallU "load" [vptr];; r <- (unint r)?;;
      Ret (Vint r)
  .

  Definition set: list val -> itree pmodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      hptr <- trigger (SGet "hptr");; hptr <- hptr↓?;;
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      `_: val <- ccallU "store" [vptr; Vint v];;
      Ret Vundef
  .

  Definition set_by_user: list val -> itree pmodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([]: list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems :=
    [(MapName.init, (["hptr"], cfunU init));
     (MapName.get,  (["hptr"], cfunU get));
     (MapName.set,  (["hptr"], cfunU set));
     (MapName.set_by_user, (["hptr"], cfunU set_by_user))].
  
  Program Definition Sem: PModSem.t := {|
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [("hptr",tt↑)];
  |}
  .
  Next Obligation. prove_scope. Qed.

  Definition Mod: PMod.t := {|
    PMod.get_modsem := fun _ => Sem;
    PMod.sk := MapSK.t;
  |}
  .

  Definition t: HMod.t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End I.
End MapI.

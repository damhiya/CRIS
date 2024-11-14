Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import HMod PMod.
Require Import Skeleton.
Require Import RingHeader.
Require Import CellHeader.
Require Import PCM ITactics.
Require Import STB IPM.

Set Implicit Arguments.

Module CtrlI.
Section I.
  Local Open Scope nat_scope.

  Context `{Σ : GRA.t}.

  Variable max_size : nat.

  Definition scopes := ["Ring"].
  Definition v_hd := "Ring" ↯ "hd".
  Definition v_tl := "Ring" ↯ "tl".

  Definition init : unit -> itree pmodE unit :=
    fun _ =>
      cput v_hd 0;;;
      cput v_tl 0
  .
  
  Definition get_size : unit -> itree pmodE nat :=
    fun _ =>
      `hd : nat <- cgetU v_hd;;
      `tl : nat <- cgetU v_tl;;
      Ret (hd - tl).

  Definition enqueue : Z -> itree pmodE unit :=
    fun x =>
      `hd : nat <- cgetU v_hd;;
      `tl : nat <- cgetU v_tl;;
      if (hd - tl <? max_size)
      then
        `_:() <- ccallU (CellName.set (hd mod max_size)) x;;
        cput v_hd (hd+1)
      else
        trigger (@IO _ void "error" "exceeds the maximum size");;; Ret tt
  .

  Definition dequeue : unit -> itree pmodE Z :=
    fun _ =>
      `hd : nat <- cgetU v_hd;;
      `tl : nat <- cgetU v_tl;;
      if (0 <? hd - tl)
      then
        x <- ccallU (CellName.get (tl mod max_size)) tt;;
        cput v_tl (tl+1);;;
        Ret x
      else      
        trigger (@IO _ void "error" "dequeue the empty queue");;; Ret 0%Z
  .

  Definition fnsems  :=
    [(RingName.init, (scopes, cfunU init));
     (RingName.get_size, (scopes, cfunU get_size));
     (RingName.enqueue, (scopes, cfunU enqueue));
     (RingName.dequeue, (scopes, cfunU dequeue))].
  
  Program Definition Sem : PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_hd,0↑);(v_tl,0↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : PMod.t := {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := RingSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End I.

End CtrlI.

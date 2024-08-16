Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod.
Require Import Skeleton.
Require Import RingHeader.
Require Import CellHeader.
Require Import PCM.
Require Import STB IPM.

Set Implicit Arguments.

Module CtrlI.
Section I.
  Local Open Scope string_scope.

  Context `{Σ: GRA.t}.

  Variable max_size : nat.

  Definition init: unit -> itree hmodE unit :=
    fun _ =>
      trigger (sPut (0: nat, 0: nat)↑);;; Ret ()
      (* ;;; *)
      (* ITree.iter *)
      (* (fun i:nat => *)
      (*    if (i <? max_size)%nat *)
      (*    then *)
      (*      `_:() <- ccallU (CellName.init i) tt;; *)
      (*      Ret (inl (i + 1)) *)
      (*    else *)
      (*      Ret (inr tt)) *)
      (* 0 *)
  .
  
  Definition get_size: unit -> itree hmodE nat :=
    fun _ =>
      st <- trigger sGet;; '(hd,tl) <- (st↓ǃ : itree _ (nat*nat)%type);;
      Ret (hd-tl)%nat.

  Definition enqueue: Z -> itree hmodE unit :=
    fun x =>
      st <- trigger sGet;; '(hd,tl) <- (st↓ǃ : itree _ (nat*nat)%type);;
      if ((hd-tl)%nat <? max_size)%nat
      then
        `_:() <- ccallU (CellName.set (hd mod max_size)) x;;
        trigger (sPut (hd+1,tl)↑)
      else
        trigger (@IO _ unit "error" "exceeds the maximum size")
  .
      
  Definition dequeue: unit -> itree hmodE Z :=
    fun _ =>
      st <- trigger sGet;; '(hd,tl) <- (st↓ǃ : itree _ (nat*nat)%type);;
      if ((hd-tl)%nat >? 0)%nat
      then 
        x <- ccallU (CellName.get (tl mod max_size)) tt;;
        trigger (sPut (hd,tl+1)↑);;;
        Ret x
      else      
        trigger (@IO _ unit "error" "dequeue the empty queue");;; Ret 0%Z
  .

  Definition fnsems  :=
    [(RingName.init, cfunU init);
     (RingName.get_size, cfunU get_size);
     (RingName.enqueue, cfunU enqueue);
     (RingName.dequeue, cfunU dequeue)].
  
  Definition Sem: HModSem.t := {|
    HModSem.fnsems := fnsems;
    HModSem.initial_st := tt↑;
    HModSem.initial_cond := emp
  |}
  .

  Definition Mod: HMod.t := {|
    HMod.get_modsem := fun _ => Sem;
    HMod.sk := RingSK.t;
  |}
  .

  Definition t := Seal.sealing "ccr" Mod.

End I.

End CtrlI.

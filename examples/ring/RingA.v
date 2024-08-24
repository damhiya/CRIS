Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import RingHeader RingASpec CellASpec.

Set Implicit Arguments.

Module RingA.
Section RING_A.
  Context `{Σ: GRA.t}.
  Context `{_R: RingRA.t (Σ:=Σ)}.  
  Context `{_C: CellRA.t (Σ:=Σ)}.  

  Variable max_size : nat.

  Definition scopes := ["Ring"].
  Definition v_que := "Ring" ↯ "que".
  
  Definition init: unit -> itree smodE unit :=
    fun _ =>
      cput v_que ([]:list Z)
  .

  Definition get_size: unit -> itree smodE nat :=
    fun _ =>
      `que: list Z <- cgetU v_que;;
      Ret (List.length que)
  .

  Definition enqueue: Z -> itree smodE unit :=
    fun x =>
      `que: list Z <- cgetU v_que;;
      if (List.length que <? max_size)%nat
      then cput v_que (que ++ [x])
      else trigger (@IO _ void "error" "exceeds the maximum size");;; Ret tt
  .

  Definition dequeue: unit -> itree smodE Z :=
    fun _ =>
      `que: list Z <- cgetU v_que;;
      match que with
      | x :: que' => cput v_que que';;; Ret x
      | _ => trigger (@IO _ void "error" "dequeue the empty queue");;; Ret 0%Z
      end
  .

  Definition fnsems :=
    [(RingName.init, (scopes,mk_specbody fspec_trivial (cfunU init)));
     (RingName.get_size, (scopes,mk_specbody fspec_trivial (cfunU get_size)));
     (RingName.enqueue, (scopes,mk_specbody fspec_trivial (cfunU enqueue)));
     (RingName.dequeue, (scopes,mk_specbody fspec_trivial (cfunU dequeue)))].

  Program Definition Sem base_cond : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_que,([]:list Z)↑)];
    SModSem.initial_cond := (([∗ list] i↦_ ∈ (replicate max_size 0%Z), CellAS.pending i) ∗ base_cond)%I;
  |}
  .
  Solve All Obligations with prove_scope.

  Definition Mod base_cond : SMod.t := {|
    SMod.get_modsem := fun sk => Sem (base_cond sk);
    SMod.sk := RingSK.t;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Variable base_cond: Sk.t -> iProp.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GlobalStb (Mod base_cond)).

End RING_A.
End RingA.

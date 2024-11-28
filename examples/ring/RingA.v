Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM STB sProp sWorld.
Require Import IPM ITactics.
Require Import RingHeader RingASpec CellASpec.
From stdpp Require Import coPset gmap namespaces.
From iris.algebra Require Import auth excl functions.

Set Implicit Arguments.

Module RingA. Section RingA.
  Context `{!Inv.t Σ Γ α β τ, !CellAS.G Γ}.
  Notation iProp := (iProp Σ).

  Variable max_size : nat.

  Definition scopes := ["Ring"].
  Definition v_que := "Ring" ↯ "que".
  
  Definition init : unit -> itree hmodE unit :=
    λ _,
      cput v_que ([]:list Z)
  .

  Definition get_size : unit -> itree hmodE nat :=
    λ _,
      `que : list Z <- cgetU v_que;;
      Ret (List.length que)
  .

  Definition enqueue : Z -> itree hmodE unit :=
    fun x =>
      `que : list Z <- cgetU v_que;;
      if (List.length que <? max_size)%nat
      then cput v_que (que ++ [x])
      else trigger (@IO _ void "error" "exceeds the maximum size");;; Ret tt
  .

  Definition dequeue : unit -> itree hmodE Z :=
    fun _ =>
      `que : list Z <- cgetU v_que;;
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

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_que,([]:list Z)↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := RingSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => ([∗ list] i↦_ ∈ (replicate max_size 0%Z), CellAS.pending i)%I.

  Variable GI : Sk.t -> invspec.
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "RingA" (SMod.to_hmod GI GlobalStb Mod).

End RingA. End RingA.

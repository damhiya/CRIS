Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import RingHeader RingASpec CellASpec.

Set Implicit Arguments.

Module RingA.
Section RING_A.
  Context `{Σ: GRA.t}.
  Context `{_R: RingRA.t (Σ:=Σ)}.  
  Context `{_C: CellRA.t (Σ:=Σ)}.  

  Variable max_size : nat.

  Definition init: unit -> itree smodE unit :=
    fun _ =>
      trigger (sPut (0: nat, []:list Z)↑)
  .

  Definition get_size: unit -> itree smodE nat :=
    fun _ =>
      st <- trigger sGet;; '(sz, _) <- (st↓ǃ : itree _ (nat*list Z)%type);;
      Ret sz
  .

  Definition enqueue: Z -> itree smodE unit :=
    fun x =>
      st <- trigger sGet;; '(sz, q) <- st↓ǃ ;;
      if ((sz:nat) <? max_size)%nat
      then trigger (sPut (sz + 1, q ++ [x])↑)
      else trigger (@IO _ unit "error" "exceeds the maximum size")
  .

  Definition dequeue: unit -> itree smodE Z :=
    fun _ =>
      st <- trigger sGet;; '(sz, q) <- st↓ǃ ;;
      if ((sz:nat) >? 0)%nat
      then match (q: list Z) with
           | x :: q' => trigger (sPut (sz - 1, q')↑);;; Ret x
           | _ => triggerNB
           end
      else trigger (@IO _ unit "error" "dequeue the empty queue");;; Ret 0%Z
  .

  Definition fnsems: list (string * fspecbody) :=
    [(RingName.init, mk_specbody fspec_trivial (cfunU init));
     (RingName.get_size, mk_specbody fspec_trivial (cfunU get_size));
     (RingName.enqueue, mk_specbody fspec_trivial (cfunU enqueue));
     (RingName.dequeue, mk_specbody fspec_trivial (cfunU dequeue))].

  Definition Sem: SModSem.t := {|
    SModSem.fnsems := fnsems;
    SModSem.initial_st := tt↑;
    SModSem.initial_cond := ([∗ list] i↦_ ∈ (repeat tt max_size), CellAS.pending i)%I;
  |}
  .

  Definition Mod: SMod.t := {|
    SMod.get_modsem := fun _ => Sem;
    SMod.sk := RingSK.t;
  |}
  .

  Definition _t: HMod.t := SMod.to_hmod (fun _ _ => None) Mod.
  Definition t := _t.

  Lemma unfold: t = _t.
  Proof. eauto. Qed.

  Global Opaque t.

End RING_A.
End RingA.

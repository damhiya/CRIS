Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import SMod HMod Translate.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import MapHeader.

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

Section M.
  Context `{_M: MapRA.t}.
  (* Context `{@GRA.inG MapRA0 Γ}.
  Context `{@GRA.inG CallableRA Γ}. *)

  (* Let Es := (hAPCE +' Es). *)

  Definition initF: list val -> itree smodE val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, _) := data in
      _ <- pput (f, sz);;
      Ret Vundef
  .

  Definition getF: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, sz) := data in
      _ <- assume(0 <= k < sz)%Z;;
      Ret (Vint (f k))
  .

  Definition setF: list val -> itree smodE val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      `data: (Z -> Z) * Z <- pget;; let (f, sz) := data in
      assume(0 <= k < sz)%Z;;;
      _ <- pput (<[k:=v]> f, sz);;
      Ret Vundef
  .

  Definition set_by_userF: list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" (([]: list Z)↑) (fun _ => True));; v <- v↓?;;
      ccallU "set" [Vint k; Vint v]
  .

  Definition MapSbtbM: list (string * fspecbody) :=
    [("init", mk_specbody init_specM (cfunU initF));
     ("get", mk_specbody get_specM (cfunU getF));
     ("set", mk_specbody set_specM (cfunU setF));
     ("set_by_user", mk_specbody set_by_user_specM (cfunU set_by_userF))].

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtbM;
    SModSem.initial_cond := Map0_initial_cond;
    SModSem.initial_st := (fun (_: Z) => 0%Z, 0%Z)↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := [("init", Gfun↑); ("get", Gfun↑); ("set", Gfun↑); ("set_by_user", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _HMap: HMod.t := (SMod.to_hmod GlobalStb SMap).
  Definition HMap := _HMap.

  Lemma HMap_unfold: HMap = _HMap.
  Proof. eauto. Qed.
  
  Global Opaque HMap.
  
End M.



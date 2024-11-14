Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import Events HMod.
Require Import IRed.
Require Import Behavior.
Require Import PCM IPM.
Require Import World sWorld.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section FSPEC.
  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Definition invspec := nat -> iProp.
  
  Record fspec: Type := mk_fspec {
    meta: Type;
    (*** thread id -> meta-variable -> new logical arg -> current logical arg -> iProp ***)
    precond: nat -> meta -> Any.t -> Any.t -> iProp; 
    (*** thread id -> meta-variable -> new logical ret -> current logical ret -> iProp ***)
    postcond: nat -> meta -> Any.t -> Any.t -> iProp; 
  }.

  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree hmodE Any.t;
  }
  .
  
  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit)
             (fun _ _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ _ reth retl => (⌜reth = retl⌝: iProp)%I).

  Definition fbody_trivial: Any.t -> itree hmodE Any.t :=
    fun _ => trigger (Choose _).

  Definition fspec_virtual (M VA VR: Type) (precond: nat -> M -> VA -> Any.t -> iProp) (postcond: nat -> M -> VR -> Any.t -> iProp) :=
    mk_fspec (meta:=M)
      (fun tid x varg arg => (∃ va: VA, ⌜varg = va↑⌝ ∗ precond tid x va arg)%I)
      (fun tid x vret ret => (∃ vr: VR, ⌜vret = vr↑⌝ ∗ postcond tid x vr ret)%I).

  Definition fspec_simple {X: Type} (DPQ: X -> (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fun _ x y a => (((fst ∘ DPQ) x a: iProp) ∗ ⌜y = a⌝)%I)
             (fun _ x z a => (((snd ∘ DPQ) x a: iProp) ∗ ⌜z = a⌝)%I)
  .

  Definition fspec_simple_tid {X: Type} (DPQ: nat -> X -> (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fun tid x y a => (((fst ∘ DPQ tid) x a: iProp) ∗ ⌜y = a⌝)%I)
             (fun tid x z a => (((snd ∘ DPQ tid) x a: iProp) ∗ ⌜z = a⌝)%I)
  .

  Definition app_DPQ {X0} {X1}
    (DPQ0: nat -> X0 -> (Any.t -> iProp) * (Any.t -> iProp))
    (DPQ1: nat -> X1 -> (Any.t -> iProp) * (Any.t -> iProp))
  :
    nat -> (X0 + X1) -> (Any.t -> iProp) * (Any.t -> iProp) :=
    fun tid meta =>
      match meta with
      | inl meta0 => DPQ0 tid meta0
      | inr meta1 => DPQ1 tid meta1
      end.

  Definition fspec_false : fspec :=
  {| 
    meta := Empty_set;
    precond := fun _ _ _ _ => False%I;
    postcond := fun _ _ _ _ => False%I; 
  |}.
  
  Definition app_fspec (fspecs : list fspec): fspec :=
  {| 
    meta := { i : nat & (nth i fspecs fspec_false).(meta) };
    precond := fun tid '(existT i meta_i) => (nth i fspecs fspec_false).(precond) tid meta_i;
    postcond := fun tid '(existT i meta_i) => (nth i fspecs fspec_false).(postcond) tid meta_i 
  |}.

  Context `{_W: CtxWD.t (Σ:=Σ)}.

  Variant meta_inv {X: positive -> nat -> Type} : Type :=
  | mk_meta (u: positive) (n: nat) (x: X u n).  

  Definition fspec_inv (k: nat) (fsp: positive -> nat -> fspec): fspec :=
    mk_fspec (meta := @meta_inv (fun u n => (fsp u n).(meta)))
      (fun tid '(mk_meta u n x) varg arg =>
         closed_universe u (k+n) ⊤ ∗ (fsp u n).(precond) tid x varg arg)%I
      (fun tid '(mk_meta u n x) vret ret =>
         closed_universe u (k+n) ⊤ ∗ (fsp u n).(postcond) tid x vret ret)%I.
  
End FSPEC.

Notation "DPQ0 @ DPQ1" := (app_DPQ DPQ0 DPQ1) (at level 60, right associativity).

Arguments precond : simpl never.
Arguments postcond : simpl never.

Section HOARE.

  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Variable ginv : invspec.
  Variable stb: gname -> option fspec.

  Definition HoareCall (fsp: fspec): gname -> Any.t -> (itree hmodE) Any.t 
    := 
    fun fn varg =>
      my_tid <- trigger Tid;;
      x <- trigger (Choose fsp.(meta));; 

      (*** precondition ***)
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (fsp.(precond) my_tid x varg arg));;;

      (*** call ***)
      ret <- trigger (Call fn arg);;

      (*** postcondition ***)
      vret <- trigger (Take Any.t);;
      trigger (Assume (fsp.(postcond) my_tid x vret ret));;;

      Ret vret.

  Definition HoareSpawn (fsp: fspec) (fn: gname) (arg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; 
    varg <- trigger (Choose Any.t);;
    tid <- trigger (Spawn fn arg);;
    trigger (Guarantee (ginv tid -∗ fsp.(precond) tid x arg varg));;;
    Ret tid.

  Definition HoareYield (tid: nat) : itree hmodE unit :=
    trigger (Guarantee (ginv tid));;;
    trigger (Yield tid);;;
    my_tid <- trigger Tid;;
    trigger (Assume (ginv my_tid)).
  
  Definition handle_schE_hmodE : schE ~> itree hmodE :=
    fun _ e =>
      match e in schE T return itree hmodE T with
      | Spawn fn arg =>
          fsp <- (stb fn)!;;
          HoareSpawn fsp fn arg
      | Yield tid =>
          HoareYield tid
      | Tid => trigger Tid
      end.
  
  Definition handle_callE_hmodE: callE ~> itree hmodE :=
    fun _ '(Call fn varg) => 
        fsp <- (stb fn)!;;
        HoareCall fsp fn varg.

  Definition interp_smod R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_schE_hmodE
           (case_ (bif:=sum1) handle_callE_hmodE
            trivial_Handler))) it.

  Definition HoareFun {X: Type}
    (P: nat -> X -> Any.t -> Any.t -> iProp)
    (Q: nat -> X -> Any.t -> Any.t -> iProp)
    (body: Any.t -> itree hmodE Any.t): Any.t -> itree hmodE Any.t
    :=
    fun arg =>
      my_tid <- trigger Tid;;
      x <- trigger (Take X);;

      varg <- trigger (Take _);;
      trigger (Assume (P my_tid x varg arg));;; (*** precondition ***)

      vret <- interp_smod (body varg);;

      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (Q my_tid x vret ret));;; (*** postcondition ***)

      Ret ret.
  
  Definition interp_sb_hp (sb: fspecbody): (Any.t -> itree hmodE Any.t) :=
    let fs: fspec := sb.(fsb_fspec) in
    HoareFun fs.(precond) fs.(postcond) sb.(fsb_body).

End HOARE.

Notation "↧ it" := (interp_smod _ _ it) (at level 59, only printing).

Module SModRed.
Section RED.

  Context `{Σ : GRA.t}.

  Lemma interp_bind
        (R S: Type)
        ginv stb
        (s : itree hmodE R) (k : R -> itree hmodE S)
    :
      interp_smod ginv stb (s >>= k)
      =
      st <- interp_smod ginv stb s;; interp_smod ginv stb (k st).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_tau
        (U : Type)
        (t : itree _ U)
        ginv stb
    :
      interp_smod ginv stb (tau;; t)
      =
      tau;; (interp_smod ginv stb t).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_ret
        (U: Type)
        (t: U)
        ginv stb
    :
      interp_smod ginv stb (Ret t)
      =
      Ret t.
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_sch
        (R: Type)
        (i: schE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- handle_schE_hmodE ginv stb i;; tau;; Ret r.
  Proof.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_call
        (R: Type)
        (i: callE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- handle_callE_hmodE stb i;; tau;; Ret r.
  Proof.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_pg
        (R: Type)
        (i: pgE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_core
        (R: Type)
        (i: coreE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_ag {A} (e: agE A)
        ginv stb
    :
      interp_smod ginv stb (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_unwrapU 
        (R: Type)
        (i: option R)
        ginv stb
    :
      interp_smod ginv stb (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof.
    unfold interp_smod, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_unwrapN
        (R: Type)
        (i: option R)
        ginv stb
    :
      interp_smod ginv stb (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof.
    unfold interp_smod, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma interp_asm
        ginv stb P
    : 
      interp_smod ginv stb (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof.
    unfold assume. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed. 

  Lemma interp_guar
        ginv stb P
    : 
      interp_smod ginv stb (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof.
    unfold guarantee. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed.

(*  
  Lemma interp_triggerUB
        (R: Type)
        stb
    :
      interp_smod stb (triggerUB)
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_smod, triggerUB in *. rewrite unfold_interp. grind.
  Qed.  

  Lemma interp_triggerNB
        (R: Type)
        stb
    :
      interp_smod stb (triggerNB)
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_smod, triggerNB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
        stb
    :
      interp_smod stb itr0
      =
      interp_smod stb itr1.
  Proof. subst; et. Qed.
*)
  
End RED.
End SModRed.

(*
Global Program Instance interp_rdb `{Σ : GRA.t} : red_database (mk_box (@interp_smod)) :=
  mk_rdb
    1
    (mk_box SModRed.interp_bind)
    (mk_box SModRed.interp_tau)
    (mk_box SModRed.interp_ret)
    (mk_box SModRed.interp_call)
    (mk_box SModRed.interp_triggere)
    (mk_box SModRed.interp_triggerp)
    (mk_box SModRed.interp_triggerp)
    (mk_box SModRed.interp_triggerUB)
    (mk_box SModRed.interp_triggerNB)
    (mk_box SModRed.interp_unwrapU)
    (mk_box SModRed.interp_unwrapN)
    (mk_box SModRed.interp_Assume)
    (mk_box SModRed.interp_Guarantee)
    (mk_box SModRed.interp_ext)
.
*)

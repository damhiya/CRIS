Require Import Coqlib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Require Import base_logic.
Require Import iprop.
(* TODO : delete this dependency after gra mod *)

Set Implicit Arguments.

Section EVENTS.

  Variant coreE : Type -> Type :=
  | Choose (X : Type) : coreE X
  | Take X : coreE X
  | IO {I : Type} {O : Type} (fn : string) (args : I) : coreE O.

  Inductive callE : Type -> Type :=
  | Call (fn : string) (args : Any.t) : callE Any.t.

  Variant stateE (V : Type) : Type :=
  | SUpdate (run : Any.t -> Any.t * V) : stateE V.

  Variant schE : Type -> Type :=
  | Spawn (fn : string) (args : Any.t) : schE nat
  | Yield (tid : nat) : schE unit.

  Definition sPut x : stateE unit := SUpdate (fun _ => (x, tt)).
  Definition sGet : stateE Any.t := SUpdate (fun x => (x, x)).

  Definition modE : Type -> Type := schE +' callE +' stateE +' coreE.

End EVENTS.

Section WRAP.

  Context {E : Type -> Type}.
  Context `{coreE -< E}.

  Definition assumeK {R} (P : Prop) (itr : itree E R) := vis (Take P) (fun _ => itr).

  Definition guaranteeK {R} (P : Prop) (itr : itree E R) := vis (Choose P) (fun _ => itr).

  Definition assume (P : Prop) : itree E unit := trigger (Take P) ;;; Ret tt.

  Definition guarantee (P : Prop) : itree E unit := trigger (Choose P) ;;; Ret tt.

  Definition triggerUB {A} : itree E A := v <- trigger (Take False);; match v: False with end.

  Definition triggerNB {A} : itree E A := v <- trigger (Choose False);; match v: False with end.

  Definition unwrapUK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => triggerUB
    end.

  Definition unwrapNK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => triggerNB
    end.

  Definition unwrapU {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition unwrapN {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unleftU {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

  Lemma assume_assumeK (P : Prop) :
    assume P = assumeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_assume {R} (P : Prop) (itr : itree E R) :
    assumeK P itr = assume P;;; itr.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (assumeK P k1 >>= k2) = assumeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma guarantee_guaranteeK (P : Prop) :
    guarantee P = guaranteeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_guarantee {R} (P : Prop) (k : itree E R) :
    guaranteeK P k = guarantee P;;; k.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (guaranteeK P k1 >>= k2) = guaranteeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapU_unwrapUK {X} (x : option X) :
    unwrapU x = unwrapUK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK_unwrapU {X R} (x : option X) (k : X -> itree E R) :
    unwrapUK x k = unwrapU x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapUK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapUK x k1 >>= k2) = unwrapUK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapN_unwrapNK {X} (x : option X) :
    unwrapN x = unwrapNK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapNK_unwrapN {X R} (x : option X) (k : X -> itree E R) :
    unwrapNK x k = unwrapN x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapNK x k1 >>= k2) = unwrapNK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

End WRAP.

Section EVENTS_OTHER.
  Context {Σ : GRA}.

  Definition key := (string * string)%type.

  Global Program Instance dec_key `{Dec string} : Dec key.
  Next Obligation.
    intro DEC. i. destruct a0, a1.
    destruct (DEC s0 s2).
    - subst. destruct (DEC s s1).
      + subst. left. refl.
      + right. ii. apply n. inv H.
    - right. ii. apply n. inv H.
  Defined.

  Definition sf (s : string) (f : string) := (s,f).

  Inductive pgE : Type -> Type :=
  | SPut (k : key) (v : Any.t) : pgE unit
  | SGet (k : key) : pgE Any.t.

  Variant agE : Type -> Type :=
  | Assume (P : iProp Σ) : agE unit
  | Guarantee (P : iProp Σ) : agE unit.

  Definition pmodE := schE +' callE +' pgE +' coreE.

  Definition hmodE := agE +' pmodE.

End EVENTS_OTHER.

Notation "f '?'" := (unwrapU f) (at level 9).
Notation "f '!'" := (unwrapN f) (at level 9).
Notation "s ↯ f" := (sf s f) (at level 9).

Section SYNTAX.

  Context `{coreE -< E}.
  Context `{callE -< E}.
  Context `{pgE -< E}.

  Definition cfunN {X Y} (body : X -> itree E Y) : Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓!;; vret <- body varg;; Ret vret↑.

  Definition cfunU {X Y} (body : X -> itree E Y) : Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

  Definition ccallU {X Y} fn (varg : X) : itree E Y :=
    vret <- trigger (Call fn (varg↑));; vret↓?.

  Definition ccallN {X Y} (fn : string) (varg : X) : itree E Y :=
    vret <- trigger (Call fn (varg↑));; vret↓!.

  Definition cput {T} k (v : T) : itree E unit :=
    trigger (SPut k v↑).

  Definition cgetU {T} k : itree E T :=
    v <- trigger (SGet k);; v↓?.

  Definition cgetN {T} k : itree E T :=
    v <- trigger (SGet k);; (v↓!).

End SYNTAX.

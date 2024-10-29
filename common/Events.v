Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Require Import PCM IPM.

Set Implicit Arguments.

Notation gname := string (only parsing). (*** convention: not capitalized ***)

Section EVENTS.

  Variant coreE : Type -> Type :=
  | Choose (X: Type): coreE X
  | Take X: coreE X
  | IO {I: Type} {O: Type} (fn: gname) (args: I) : coreE O.

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t) : callE Any.t.

  Variant stateE (V: Type): Type :=
  | SUpdate (run : Any.t -> Any.t * V) : stateE V.

  Variant schE: Type -> Type :=
  | Spawn (fn: gname) (args: Any.t): schE nat
  | Yield (tid: nat) : schE unit
  | Tid : schE nat
  .

  Definition sPut x : stateE unit := SUpdate (fun _ => (x, tt)).
  Definition sGet : stateE Any.t := SUpdate (fun x => (x, x)).

  Definition modE : Type -> Type := schE +' callE +' stateE +' coreE.

End EVENTS.

Section WRAP.

  Definition assume {E} `{coreE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
  Definition guarantee {E} `{coreE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

  Definition triggerUB {E A} `{coreE -< E}: itree E A := v <- trigger (Take void);; match v: void with end.
  Definition triggerNB {E A} `{coreE -< E}: itree E A := v <- trigger (Choose void);; match v: void with end.

  Definition unwrapU {E X} `{coreE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition unwrapN {E X} `{coreE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unleftU {E X Y} `{coreE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {E X Y} `{coreE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {E X Y} `{coreE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {E X Y} `{coreE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.
End WRAP.

Section EVENTS_OTHER.

  Context `{Σ: GRA.t}.

  Definition key := (string * string)%type.

  Global Program Instance dec_key `{Dec string}: Dec key.
  Next Obligation.
    intro DEC. i. destruct a0, a1.
    destruct (DEC s0 s2).
    - subst. destruct (DEC s s1).
      + subst. left. refl.
      + right. ii. apply n. inv H. refl.
    - right. ii. apply n. inv H. refl.
  Defined.

  Definition sf (s: string) (f: string) := (s,f).

  Inductive pgE: Type -> Type :=
  | SPut (k: key) (v: Any.t): pgE unit
  | SGet (k: key): pgE Any.t.

  Variant agE: Type -> Type :=
  | Assume (P: iProp): agE unit
  | Guarantee (P: iProp): agE unit.

  Definition pmodE := schE +' callE +' pgE +' coreE.
  
  Definition hmodE := agE +' pmodE.

End EVENTS_OTHER.

Notation "f '?'" := (unwrapU f) (at level 9).
Notation "f '!'" := (unwrapN f) (at level 9).
Notation "s ↯ f" := (sf s f) (at level 9).

Section SYNTAX.
  Context `{Σ: GRA.t}.
  Context `{coreE -< E}.
  Context `{callE -< E}.
  Context `{pgE -< E}.

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓!;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. 
  
  Definition ccallU {X Y} fn (varg: X) : itree E Y :=
    vret <- trigger (Call fn (varg↑));; vret↓?.
                                 
  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));; vret↓!.
                                          
  Definition cput {T} k (v:T) : itree E unit :=
    trigger (SPut k v↑).

  Definition cgetU {T} k : itree E T :=
    v <- trigger (SGet k);; v↓?.

  Definition cgetN {T} k : itree E T :=
    v <- trigger (SGet k);; (v↓!).

End SYNTAX.

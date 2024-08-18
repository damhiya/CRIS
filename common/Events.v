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

  Definition sPut x : stateE Any.t := SUpdate (fun _ => (x, tt↑)).
  Definition sGet : stateE Any.t := SUpdate (fun x => (x, x)).

  Definition modE : Type -> Type := (callE +' stateE +' coreE).

  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
    interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.  

  Definition handle_stateE {E}: stateE ~> stateT Any.t (itree E) := 
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {E}: itree (stateE +' E) ~> stateT Any.t (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_stateE pure_state).

  Definition interp_modE A (prog: callE ~> itree modE) (itr0: itree modE A) (st0: Any.t): itree coreE (Any.t * _)%type :=
    '(st1, v) <- interp_stateE (interp_mrec prog itr0) st0;;
    Ret (st1, v).

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



End EVENTS.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).


Section EVENTSCOMMON.
(*** casting call, fun ***)
  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: coreE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));; 
    vret <- vret↓ǃ;; Ret vret
    .
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));;
    vret <- vret↓?;; Ret vret
    .

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. 

End EVENTSCOMMON.

Section EVENTS_OTHER.

  Context `{Σ: GRA.t}.

  Inductive pgE: Type -> Type :=
  | SPut (k: string) (v: Any.t): pgE Any.t
  | SGet (k: string): pgE Any.t.

  Variant agE: Type -> Type :=
  | Assume (P: iProp): agE unit
  | Guarantee (P: iProp): agE unit.

  Definition pmodE := callE +' pgE +' coreE.
  
  Definition hmodE := agE +' pmodE.

  Variant apcE: Type -> Type :=
  | APC: apcE unit.

  Definition smodE := apcE +' hmodE.

End EVENTS_OTHER.

Opaque interp_modE.


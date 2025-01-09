Require Import CRIS.

Require Import MapHeader.

Set Implicit Arguments.

(*** module A Map
private map := (fun k => 0)

def init(sz : int) ≡
  skip

def get(k : int) : int ≡
  return map[k]

def set(k : int, v : int) ≡
  map := map[k ← v]

def set_by_user(k : int) ≡
  set(k, input())
***)

Module MapA. Section MapA.
  Context {Σ : GRA}.

  Definition scopes := ["Map"].
  Definition v_map := "Map" ↯ "map".

  Definition set : list val → itree hmodE val :=
    λ varg,
      '(k, v): _ <- (pargs [Tint; Tint] varg)!;;
      f <- cgetN v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition get : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      f <- cgetN v_map;;
      Ret (Vint (f k)).

  Definition set_by_user : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      v <- trigger (IO "input" ());;
      ccallN MapName.set [Vint k; Vint v].
End MapA. End MapA.
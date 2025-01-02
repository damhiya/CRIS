Require Import CRIS.

Require Import MapHeader.

Set Implicit Arguments.

(*** module M Map
private map := (fun k => 0)
private size := 0

def init(sz : int) ≡
  size := sz

def get(k : int) : int ≡
  assume(0 ≤ k < size)
  return map[k]

def set(k : int, v : int) ≡
  assume(0 ≤ k < size)
  map := map[k ← v]

def set_by_user(k : int) ≡
  set(k, input())
***)
Module MapM. Section MapM.
  Context {Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Definition scopes := ["Map"].
  Definition v_size := "Map" ↯ "size".
  Definition v_map := "Map" ↯ "map".

  Definition init : list val → itree hmodE val :=
    λ varg,
      size <- (pargs [Tint] varg)?;;
      cput v_size size;;;
      Ret Vundef.
  
  Definition get : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      Ret (Vint (f k)).

  Definition set : list val → itree hmodE val :=
    λ varg,
      '(k, v):_ <- (pargs [Tint; Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition set_by_user : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ());;
      ccallU MapName.set [Vint k; Vint v].
End MapM. End MapM.

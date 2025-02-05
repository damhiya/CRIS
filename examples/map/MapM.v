Require Import CRIS.

Require Import MapHeader.

Set Implicit Arguments.

(* Resource algebra for MapI ⊆ MapM *)
Class MapMGΓ (Γ : HRA) := {
  #[global] map_inG :: inG (exclR unitO) Γ;
}.
Definition MapMΓ : HRA := #[exclR unitO].
Global Instance subG_GΓ {Γ} : subG MapMΓ Γ → MapMGΓ Γ.
Proof. solve_inG. Qed.

Module MapMS. Section MapMS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !MapMGΓ Γ}.

  Definition pending : iProp Σ := own base_γ (Excl ()).
  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    rewrite /pending; unseal "MapMS".
    iIntros "P1 P2"; iCombine "P1 P2" as "P" gives %CONT; ss.
  Qed.

  Definition init_spec : fspec :=
    fspec_simple
      (λ (sz : nat),
        (λ varg, ⌜varg = [Vint sz]↑ ∧ (8 * sz < modulus_64)%Z⌝ ∗ pending,
          λ vret, emp))%I.

  Definition get_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
          λ vret, emp))%I.

  Definition set_spec : fspec :=
    fspec_simple
      (λ '(k, v),
        (λ varg, ⌜varg = ([Vint k; Vint v])↑⌝,
          λ vret, emp))%I.

  Definition set_by_user_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
          λ vret, emp))%I.

  Definition Stb : alist string fspec :=
    Seal.sealing CRIS
      [(MapName.init, init_spec);
       (MapName.get, get_spec);
       (MapName.set, set_spec);
       (MapName.set_by_user, set_by_user_spec)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof. by rewrite /Stb; unseal CRIS; prove_nodup. Qed.

End MapMS. End MapMS.

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
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !MapMGΓ Γ}.

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

  Definition fnsems :=
    [(MapName.init, (scopes, mk_specbody MapMS.init_spec (cfunU init)));
     (MapName.get, (scopes, mk_specbody MapMS.get_spec (cfunU get)));
     (MapName.set, (scopes, mk_specbody MapMS.set_spec (cfunU set)));
     (MapName.set_by_user, (scopes, mk_specbody MapMS.set_by_user_spec (cfunU set_by_user)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_size, 0%Z↑);
                           (v_map,  (λ (_ : Z), 0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := MapSK.t;
  |}.

  Definition InitCond : Sk.t → iProp Σ :=
    λ _, emp%I.

  Definition t ginv Stb := Seal.sealing CRIS (@SMod.to_hmod Σ ginv Stb Mod).
End MapM. End MapM.

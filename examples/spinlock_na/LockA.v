Require Import CRIS.
Require Import LockHeader.
Require Import ImpPrelude MemHeader MemA.
Require Import SchHeader SchA.
From iris Require Import excl.

(** Specification Module of the spinlock library *)

(* Resource algebra *)
(* Structure of the resource algebra definition is similar to that of iris,
  but few differences exist. *)
(* HRAs are structs similar to GRAs, but for RAs that sProps can own. *)
Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  
  Class spinlockG `{!crisG Γ Σ α β τ _S _I} := {
    spinlock_inG :: inG (exclR unitO) Γ;
  }.
  Definition spinlockΓ : HRA := #[exclR unitO].
  (* Be sure to annotate Γ as HRA, or tc search may not work properly. *)
  Global Instance subG_spinlockG : subG spinlockΓ Γ → spinlockG.
  Proof. solve_inG. Defined.
  (* Be sure to add these two instances to hint database so that we can resolve inG instances
    in the cancellation phase. *)
End RA.
Hint Unfold subG_spinlockG spinlock_inG : GRA_index.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module LockAS. Section LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG}.

  (* Initial resource *)
  Definition ir : spinlockΓ := *[None].

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : GTerm.t n := <own> γ (Excl ()).

  Definition lock_inv {n} bofs (P : GTerm.t n) γ : GTerm.t n :=
    bofs ↦ (Vint 1)
    ∨ bofs ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} γ val P : iProp Σ :=
    ∃ bofs, ⌜val = Vptr bofs⌝ ∗ inv n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)
  Definition newlock_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := {n & GTerm.t n})
        (λ '(existT n P),
          ((λ _, ⟦P⟧),
          (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock γ val P))
      ))%I).

  Definition acquire_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock γ val (projT2 P)),
          (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      )))%I.

  Definition release_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝
            ∗ is_lock γ val (projT2 P)
            ∗ ⟦token (projT1 P) γ⟧
            ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = Vundef↑⌝))
      )))%I.

  Definition sp E : spl_type :=
    [(Some SpinLockHdr.newlock, Some (newlock_spec E));
     (Some SpinLockHdr.acquire, Some (acquire_spec E));
     (Some SpinLockHdr.release, Some (release_spec E))].
End LockAS. End LockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition acquire : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.
  Definition release : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.

  Definition fnsems E : fnsems_type :=
    [(Some SpinLockHdr.newlock, (true, wmask_all, scopes, (Some (LockAS.newlock_spec E), cfunU newlock)));
     (Some SpinLockHdr.acquire, (true, wmask_all, scopes, (Some (LockAS.acquire_spec E), cfunU acquire)));
     (Some SpinLockHdr.release, (true, wmask_all, scopes, (Some (LockAS.release_spec E), cfunU release)))].

  Program Definition smod E : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems E;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t E sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp (smod E)).
End SpinLockA. End SpinLockA.

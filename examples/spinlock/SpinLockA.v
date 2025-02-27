Require Import CRIS.
Require Import ImpPrelude SchHeader MemHeader MemA SpinLockHeader.
Require Import wsim.
From iris Require Import excl.

Notation 𝒴 := (Sch.yield).

Class SpinLockAGΓ (Γ : HRA) := {
  #[local] spinlock_inG :: inG (exclR unitO) Γ;
}.
Definition SpinLockΓ : HRA := #[exclR unitO].
Global Instance subG_GΓ {Γ} : subG SpinLockΓ Γ → SpinLockAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ spinlock_inG : GRA_index.

Module SpinLockAS. Section SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : SRFSyn.t n := <own> γ (Excl ()).

  Definition lock_inv {n} blk ofs (P : SRFSyn.t n) γ : SRFSyn.t n :=
    (blk, ofs) ↦ (Vint 1)
    ∨ (blk, ofs) ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} u γ val P : iProp Σ :=
    ∃ blk ofs, ⌜val = Vptr blk ofs⌝ ∗ inv u n N_SpinLockA (lock_inv blk ofs P γ).

  Definition newlock_spec u : fspec :=
    w_fspec u
      (fspec_simple (λ P : {n & SRFSyn.t n},
        ((λ _, ⟦projT2 P⟧),
        (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock u γ val (projT2 P)))
      ))%I.

  Definition acquire_spec u : fspec :=
    w_fspec u
      (fspec_simple (X := gname * val * {n & SRFSyn.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock u γ val (projT2 P)),
          (λ ret, ⌜ret = [Vundef]↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      ))%I.

  Definition release_spec u : fspec :=
    w_fspec u
      (fspec_simple (X := gname * val * {n & SRFSyn.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock u γ val (projT2 P) ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = [Vundef]↑⌝))
      ))%I.

  Definition spc u : alist string fspec :=
    [(SpinLockName.newlock, newlock_spec u);
     (SpinLockName.acquire, acquire_spec u);
     (SpinLockName.release, release_spec u)].
End SpinLockAS. End SpinLockAS.

Module SpinLockA. Section SpinLockA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree hmodE val := λ _, 𝒴;;; trigger (Choose val).
  Definition acquire : list val → itree hmodE val := λ _, 𝒴;;; Ret Vundef.
  Definition release : list val → itree hmodE val := λ _, 𝒴;;; Ret Vundef.

  Definition fnsems u :=
    [(SpinLockName.newlock, (scopes, mk_specbody (SpinLockAS.newlock_spec u) (cfunU newlock)));
     (SpinLockName.acquire, (scopes, mk_specbody (SpinLockAS.acquire_spec u) (cfunU acquire)));
     (SpinLockName.release, (scopes, mk_specbody (SpinLockAS.release_spec u) (cfunU release)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u spc : HMod.t := Seal.sealing CRIS SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u).
End SpinLockA. End SpinLockA.

Require Import CRIS.

Require Import SchHeader SchA.
Require Import MemA MemHeader.
Require Import ImpPrelude.
Require Import SpinLockHeader.
From iris.algebra Require Import excl.

Set Implicit Arguments.

Section SpinLockRA.

Definition lockRA := exclR unitR.

Class lockGΓ (Γ : HRA) := { 
  #[global] lock_G :: inG lockRA Γ;
}.
Definition lockΓ : HRA := #[lockRA].

End SpinLockRA.

Module SpinLockAS.
Section SpinLockAS.
  
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !lockGΓ Γ}.
  Context `{!CtxST.t τ, !SL.G Σ Γ α β τ, !syn_invG Σ Γ α β τ}.
  
  Notation iProp := (iProp Σ).

  Definition locked {n} γ : SRFSyn.t n := <own> γ (Excl ()).

  Definition lockN := nroot .@ "lock" .

  Definition mem_points_to_singleton_s {n} (loc : mblock * Z) (q: Qp) (v : val) : SRFSyn.t n :=
    <own> base_γ ((mem_points_to_singleton_r loc q v): memRA).

  Notation "loc ⟾ v" := (mem_points_to_singleton_s loc 1 v) (at level 20).

  Definition is_lock γ (v: val) u n (P:SRFSyn.t n) :=
    (∃ (l: mblock * Z), ⌜v = (Vptr l.1 l.2)⌝ 
    ∧ inv u n (lockN) ((
          ( @mem_points_to_singleton_s n l 1 (Vint 0)) ∗ P ∗ @locked n γ) 
        ∨ 
          ( @mem_points_to_singleton_s n l 1 (Vint 1))))%I.
  
  Global Instance is_lock_persistent γ v u n (p: SRFSyn.t n) : Persistent (is_lock γ v u p).
  Proof. apply _. Qed.

  Definition new_lock_spec u: fspec := 
    w_fspec u (fspec_simple (fun '(u, existT n P) => (
                (fun varg => (⌜varg = tt↑⌝ ∗ (⟦P, n⟧))%I),
                (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝) 
                                    ∗ ∃ γ, is_lock γ (Vptr b 0) u P)%I)
    ))).
  
  Definition acquire_spec u: fspec :=
    w_fspec u (fspec_simple (fun '(b, ofs, γ, u, existT n P) => (
                (fun varg => ((⌜varg = (Vptr b ofs)↑⌝) ∗ (is_lock γ (Vptr b ofs) u P))%I),
                (fun vret => (⌜vret = tt↑⌝ ∗ ⟦P, n⟧ ∗ ⟦locked γ, n⟧)%I)
    ))).

  Definition release_spec u: fspec :=
    w_fspec u (fspec_simple (fun '(b, ofs, γ, u, existT n P) => (
                (fun varg => (  ⌜varg = (Vptr b ofs)↑⌝ 
                              ∗ (is_lock γ (Vptr b ofs) u P) 
                              ∗ (⟦locked γ, n⟧)
                              ∗ ⟦P, n⟧)%I),
                (fun vret => (⌜vret = tt↑⌝)%I)
    ))).
  
  Definition Spc u: alist string fspec :=
    Seal.sealing CRIS 
      [(SpinLockName.new_lock, new_lock_spec u);
       (SpinLockName.acquire, acquire_spec u);
       (SpinLockName.release, release_spec u)].

End SpinLockAS.
End SpinLockAS.

Module SpinLockA.
Section SpinLockA.

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !lockGΓ Γ}.

  Variable univ: positive. 

  Definition new_lock: unit -> itree hmodE val :=
    λ _, 
      Sch.yield;;;
      v <- trigger (Choose val);;
      Sch.yield;;;
      Ret v
    .

  Definition acquire: val -> itree hmodE unit :=
    λ _, 
      Sch.yield;;;
      Ret tt
    .

  Definition release: val -> itree hmodE unit :=
    λ _, 
      Sch.yield;;;
      Ret tt
    .

  Definition scopes := ["SpinLock"].

  Definition fnsems u :=
    [(SpinLockName.new_lock, (scopes, mk_specbody (SpinLockAS.new_lock_spec u) (cfunN new_lock)));
     (SpinLockName.acquire, (scopes, mk_specbody (SpinLockAS.acquire_spec u) (cfunN acquire)));
     (SpinLockName.release, (scopes, mk_specbody (SpinLockAS.release_spec u) (cfunN release)))
    ].

  Program Definition Mod u: SMod.t :=
  {|
      SMod.scopes := scopes;
      SMod.fnsems := fnsems u;
      SMod.initial_st := [];
  |}.
    Solve All Obligations with prove_scope.
    Next Obligation. prove_nodup. Qed.

    Definition InitCond : iProp Σ := emp%I.
    
    Definition t u Spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) (Spc) (Mod u)).

End SpinLockA.
End SpinLockA.
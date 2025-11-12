Require Import CRIS.
Require Import LockHeader LockA.
Require Import ImpPrelude SchHeader SchA MemHeader MemA.
From iris Require Import frac_auth numbers.

(** Specification Module of SpinLockMainI *)

(* Resource algebra - same as Counter.v example from iris *)
Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Class spinlockmainG `{!crisG Γ Σ α β τ _S _I} := {
    spinlockmain_inG :: inG (frac_authR ZR) Γ;
  }.
  Definition spinlockmainΓ : HRA := #[frac_authR ZR].
  Global Instance subG_spinlockmainG : subG spinlockmainΓ Γ → spinlockmainG.
  Proof. solve_inG. Defined.
End RA.
Hint Unfold subG_spinlockmainG spinlockmain_inG : GRA_index.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module MainAS. Section MainAS.
  Import LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG, !spinlockmainG}.

  (* initial resource *)
  Definition ir : spinlockmainΓ := *[None].

  Definition lock_P loc γ : GTerm.t 0 :=
    ∃ v : τ{Z}%SAT, loc ↦ (Vint v) ∗ <own> γ (●F v).

  Definition init_cond E : iProp Σ :=
    winv (E, E) ∗ Tid 0 0.

  Definition incr_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (λ '(bofs_l, bofs_v, γ_v),
        ((λ arg,
          ⌜arg = ([Vptr bofs_l; Vptr bofs_v]↑↑)↑⌝ ∗
          (∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v) ∗
          own γ_v (◯F{1/2} 0%Z))),
        (λ ret,
          ⌜ret = ((Vundef)↑↑)↑⌝
          ∗ own γ_v (◯F{1/2} 1%Z)))
      )))%I.

  (* pre/postconditions for threads to be spawned *)
  Definition incr_pre bofs_l bofs_v γ_v : SAny.t → SAny.t → iProp Σ :=
    λ varg arg,
      (⌜varg = arg⌝
      ∗ (⌜varg = [Vptr bofs_l; Vptr bofs_v]↑↑⌝
      ∗ ∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v)
          ∗ own γ_v (◯F{1/2} 0%Z)))%I.

  Definition incr_post γ_v : SAny.t → SAny.t → leibnizO {n & GTerm.t n} :=
    (λ _ _, existT 0 (<own> γ_v (◯F{1/2} 1%Z)))%SAT.

  Lemma incr_spawnable E bofs_l bofs_v γ_v :
    SchA.fspec_spawnable E (incr_spec E)
      (incr_pre bofs_l bofs_v γ_v) (incr_post γ_v).
  Proof.
    intros [x1 x2]; ss.
    exists (x1, x2, (bofs_l, bofs_v, γ_v)); split.
    { intros varg arg. unfold_pre_post.
      iIntros "[W [%va [-> [TID [%sarg [-> [-> [-> P]]]]]]]]".
      iFrame. iModIntro. iSplit; eauto.
    }
    { iIntros (vret ret); rewrite /postcond /incr_spec /=.
      iIntros "[$ [$ [[-> F] ->]]]".
      iFrame. iModIntro; iExists _; iSplit; eauto. iExists _. iSplit; eauto. SL_red; done.
    }
  Qed.

  Definition sp E : spl_type := [(Some SpinLockMainHdr.incr, Some (incr_spec E))].
End MainAS. End MainAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockMainA. Section SpinLockMainA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !spinlockG, !spinlockmainG}.

  Definition scopes : list string := [].

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; '(l, v) : val * val <- trigger (Choose (val * val));;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : SAny.t <- Sch.join t1;;
      𝒴;;; '_ : SAny.t <- Sch.join t2;;
      𝒴;;; '_ : unit <- trigger (IO "printf" 2%Z);;
      𝒴;;; Ret tt↑.

  Definition incr : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.

  Definition fnsems E : fnsems_type :=
    [(None,                      (true, wmask_all, scopes, (Some fspec_trivial, main)));
     (Some SpinLockMainHdr.incr, (true, wmask_all, scopes, (Some (MainAS.incr_spec E), cfunN (sfunN incr))))].

  Program Definition smod E : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems E;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t E sp : Mod.t := Seal.sealing CRIS SMod.to_mod sp (smod E).
End SpinLockMainA. End SpinLockMainA.

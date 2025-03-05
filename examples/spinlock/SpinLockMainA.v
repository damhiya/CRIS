Require Import CRIS.
Require Import ImpPrelude SchHeader SchA MemHeader MemA SpinLockMainHeader SpinLockA.
Require Import wsim.

From iris Require Import frac_auth numbers.

Class SpinLockMainAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG (frac_authR ZR) Γ;
}.
Definition SpinLockMainAΓ : HRA := #[frac_authR ZR].
Global Instance subG_GΓ {Γ : HRA} : subG SpinLockMainAΓ Γ → SpinLockMainAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ SpinLockMainAΓ : GRA_index.

Module SpinLockMainAS. Section SpinLockMainAS.
  Import SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!memGΓ Γ, !SchAGΣ Σ, !SchAGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Definition main_spec u : fspec :=
    w_fspec u
      (fspec_simple (λ _ : unit,
        (λ arg, ⌜arg = tt↑⌝ ∗ SchAS.tid_user 0,
        λ ret, ⌜ret = tt↑⌝)))%I.

  Definition lock_P loc γ : SRFSyn.t 0 :=
    ∃ v : τ{Z}%SRF, loc ↦ (Vint v) ∗ <own> γ (●F v).

  Program Definition fspec_tid (fsp : fspec) : fspec :=
    mk_fspec (meta:=(nat * fsp.(meta))) _ _.
  Definition incr_spec u : fspec :=
    w_fspec u
      (fspec_simple (λ '(tid, blk_l, ofs_l, blk_v, ofs_v, γ_v),
        ((λ arg,
          ⌜arg = ([Vptr blk_l ofs_l; Vptr blk_v ofs_v]↑↑)↑⌝
          ∗ SchAS.tid_user tid
          ∗ (∃ γ_l, is_lock u γ_l (Vptr blk_l ofs_l) (lock_P (blk_v, ofs_v) γ_v)
          ∗ own γ_v (◯F{1/2} 0%Z))),
        (λ ret,
          ⌜ret = ((Vundef)↑↑)↑⌝
          ∗ SchAS.tid_user tid
          ∗ own γ_v (◯F{1/2} 1%Z)))
      ))%I.

  Definition incr_pre u blk_l ofs_l blk_v ofs_v γ_v : iProp Σ :=
    ∃ γ_l, is_lock u γ_l (Vptr blk_l ofs_l) (lock_P (blk_v, ofs_v) γ_v)
      ∗ own γ_v (◯F{1/2} 0%Z).

  Definition incr_post γ_v : SAny.t → SynDepO :=
    (λ _, existT 0 (<own> γ_v (◯F{1/2} 1%Z)))%SRF.

  Lemma incr_spawnable u tid blk_l ofs_l blk_v ofs_v γ_v :
    SchAS.fspec_spawnable u (incr_spec u) tid (tid, blk_l, ofs_l, blk_v, ofs_v, γ_v)
      (([Vptr blk_l ofs_l; Vptr blk_v ofs_v]↑↑)↑) (([Vptr blk_l ofs_l; Vptr blk_v ofs_v]↑↑)↑)
      (incr_pre u blk_l ofs_l blk_v ofs_v γ_v) (incr_post γ_v).
  Proof.
    rr. split.
    { iIntros "[$ [TID [% [#L O]]]]". iFrame. iSplit; eauto. }
    { iIntros (ret) "[%vret [$ P]]". iDestruct "P" as "[[-> [$ O]] ->] /=".
      SL_red. iExists _; eauto.
    }
  Qed.

  Definition spc u : alist string fspec :=
    [(SpinLockMainName.main, main_spec u);
     (SpinLockMainName.incr, incr_spec u)].
End SpinLockMainAS. End SpinLockMainAS.

Module SpinLockMainA. Section SpinLockMainA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!memGΓ Γ, !SchAGΣ Σ, !SchAGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Definition scopes : list string := [].

  Definition main : unit → itree hmodE unit :=
    λ _,
      𝒴;;; '(l, v) : val * val <- trigger (Choose (val * val));;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : val <- Sch.join val t1;;
      𝒴;;; '_ : val <- Sch.join val t2;;
      (ITree.iter
        (λ _, 𝒴;;; 'x : bool <- trigger (Choose bool);; Ret (if x then inr tt else inl tt)) tt);;;
      𝒴;;; '_ : unit <- trigger (IO "printf" 2%Z);;
      𝒴;;; Ret tt.

  Definition incr : list val → itree hmodE val :=
    λ _,
      (ITree.iter (λ _,
        𝒴;;; 'x : bool <- trigger (Choose bool);;
        Ret (if x then inr tt else inl tt)
      ) tt);;;
      Ret Vundef.

  Definition fnsems u :=
    [(SpinLockMainName.main, (scopes, mk_specbody (SpinLockMainAS.main_spec u) (cfunN main)));
     (SpinLockMainName.incr, (scopes, mk_specbody (SpinLockMainAS.incr_spec u) (cfunN (sfunN incr))))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u spc : HMod.t := Seal.sealing CRIS SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u).
End SpinLockMainA. End SpinLockMainA.
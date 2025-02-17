Require Import CRIS wsim.
Require Export ImpPrelude IncrHeader SchHeader MemA.

Module IncrAS. Section IncrAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.

  Definition incr_spec u n : fspec :=
    w_fspec u n
      (fspec_simple (λ '(blk, ofs),
        ((λ varg, ⌜varg = [Vptr blk ofs]↑⌝), (λ vret, ∃ v, ⌜vret = [Vint v]↑⌝))%I
      )).

  Definition spc u n : alist string fspec :=
    [(IncrName.incr, incr_spec u n)].
End IncrAS. End IncrAS.

Module IncrA. Section IncrA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.
  Definition scopes : list string := [].

  Definition incr : list val → itree hmodE unit :=
    λ loc,
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] loc)!;;
      Sch.yield;;;
      v <- trigger (Take Z);;
      trigger (Assume ((blk, ofs) ⤇ (Vint v)));;;
      trigger (Guarantee ((blk, ofs) ⤇ (Vint (v + 1)%Z)));;;
      Sch.yield;;;
      Ret tt.

  Definition fnsems u n :=
    [(IncrName.incr, (scopes, mk_specbody (IncrAS.incr_spec u n) (cfunU incr)))].

  Program Definition Mod u n : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u n;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u n ginv spc : HMod.t :=
    Seal.sealing CRIS (SMod.to_hmod ginv spc (Mod u n)).
End IncrA. End IncrA.
Require Import CRIS.
Require Import SchHeader RRSHeader SchA RRSA.
Require Import MemHeader MemA.
Require Import RRSNodeHeader.

Set Implicit Arguments.

Module RRSNodeI. Section RRSNodeI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.

  Definition scopes := [RRSNODE].

  Definition f_main : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      'x: val <- ccallU MemHdr.alloc [Vint 1];; ℛ𝒴;;;
      '_: val <- ccallU MemHdr.store [x; Vint 0];; ℛ𝒴;;;
      'tid1: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f, x↑↑);; ℛ𝒴;;;
      'tid2: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f, x↑↑);; ℛ𝒴;;; ℛℛ;;;
      Ret (tt↑↑)
  .

  Definition f : SAny.t -> itree crisE SAny.t :=
    fun arg =>
      'x: val <- (arg↓↓)?;; ℛ𝒴;;;
      'v: val <- ccallU MemHdr.load [x];; ℛ𝒴;;;
      'tid : nat <- ccallU RRSHdr.get_tid tt;; ℛ𝒴;;;
      o <- (vsub (Vint tid) v)?;; ℛ𝒴;;;
      nx <- (vadd v (Vint 1))?;; ℛ𝒴;;;
      '_: val <- ccallU MemHdr.store [x; nx];; ℛ𝒴;;;
      trigger (@IO _ unit "print" o);;; ℛ𝒴;;; ℛℛ;;; 
      Ret (tt↑↑)
  .
  
  Definition fnsems : fnsems_type :=
    [(Some RRSNodeHdr.f_main, (false, wmask_all, scopes, (None, cfunU f_main)));
     (Some RRSNodeHdr.f,      (false, wmask_all, scopes, (None, cfunU f)))].

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).

End RRSNodeI. End RRSNodeI.

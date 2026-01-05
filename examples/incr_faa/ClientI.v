Require Import CRIS.
Require Import ImpPrelude MemHeader SchHeader.
Require Import FaaHeader.

Module ClientI. Section ClientI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : gmultiset string := ∅.

  Definition incr : list val → itree crisE unit :=
    λ arg,
      𝒴;;; '_ : unit <- ccallU FaaHdr.faa2 arg;;
      𝒴;;; Ret tt.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; bofs <- (pargs [Tptr] [ptr_raw])?;;
      𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr bofs; Vint 0%Z];;
      𝒴;;; tid1 <- Sch.spawn (IncrHdr.incr, [Vptr bofs]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (IncrHdr.incr, [Vptr bofs]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; 'v_raw : val <- ccallU MemHdr.load [Vptr bofs];;
      𝒴;;; 'v : Z <- (pargs [Tint] [v_raw])?;;
      𝒴;;; '_ : unit <- trigger (IO "OUT" v);;
      𝒴;;; Ret (tt↑).

  Definition fnsems : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some IncrHdr.incr := Some (msk_scp scopes msk_true, (None, cfunU (sfunU incr)));
      None := Some (msk_scp scopes msk_true, (None, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try done.
  Next Obligation. rewrite ?omap_insert /= omap_empty. mod_tac scope_solver. Qed.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End ClientI. End ClientI.

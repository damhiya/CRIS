Require Import CRIS LMod SchHeader SchI.

Definition main_name (name: string) (idx: nat) :=
  (name ++ "." ++ of_nat idx)%string.

Module Init.
  Section Init.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition init : unit → itree crisE nat :=
    fun _ =>
      ITree.iter
        (λ l,
          match l with
          | [] => Ret (inr tt↑)
          | hd :: tl =>
              trigger (IO (I := unit) "dprint" "spawn!");;;
              ccallU (Y:=nat) SchHdr.spawn (main_name "main" hd, tt↑↑);;;
              Ret (inl tl)
          end) [1; 2];;;
      ITree.iter (R := unit)
        (λ _,
          ccallU (Y:=unit) SchHdr.yield ();;;
          Ret (inl tt)) ();;;
      Ret 2.
  
  Definition fnsems : fnsemmap :=
    {[entry # (msk_real (msk_scp ["MEM"] msk_true), (fsp_none, cfunU init))]}.

  Program Definition smod : SMod.t :=
    {|
      SMod.scopes := ["MEM"];
      SMod.fnsems := fnsems;
      SMod.initial_st := ∅;
    |}
  .
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.

  End Init.
End Init.

Module Unit.
  Section Unit.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Variable idx : nat.

  Definition main : SAny.t → itree crisE unit :=
    fun _ =>
      trigger (IO (I := unit) "dprint" (of_nat idx));;;
      ITree.iter (R := unit)
        (λ _,
          ccallU (Y:=unit) SchHdr.yield ();;;
          Ret (inl tt)) ().
  
  Definition fnsems : fnsemmap :=
    {[fid (main_name "main" idx) # (msk_real (msk_scp ["MEM"] msk_true), (fsp_none, cfunU main))]}.

  Program Definition smod : SMod.t :=
    {|
      SMod.scopes := ["MEM"];
      SMod.fnsems := fnsems;
      SMod.initial_st := ∅;
    |}
  .
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.

  End Unit.
End Unit.

(* Definition md : Mod.t := Init.t ★ Unit.t 1 ★ Unit.t 2 ★ SchI.t. *)

(* Definition ttitr : itree coreE Any.t := LMod.compile (Mod.to_lmod md ε) tt↑. *)

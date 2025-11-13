Require Import CRIS.
Require Import PFMemHeader PFMemUser SchHeader HistoryRA.
Require Import SystemHeader.

Notation flag := 0 (only parsing).
Notation data := 1 (only parsing).

Module MPHdr.
  Definition mp2 : string := "mp2".
End MPHdr.

(* Message passing - implementation *)
Module MPI. Section MPI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Definition scopes : list string := [].

  Definition mp : Any.t → itree crisE Any.t :=
    λ _,
      (* alloc *)
      𝒴;;; m <- ccallU SystemHdr.alloc 2;;
      𝒴;;; loc <- parse_loc m;;
      (* store *)
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> flag, Val.Vnum 0, Ordering.na);;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> data, Val.Vnum 0, Ordering.na);;
      (* spawn *)
      𝒴;;; '_ : () <- ccallU SystemHdr.spawn (MPHdr.mp2, m↑↑);;
      (* loop *)
      iterC (λ _,
        𝒴;;; r <- ccallU SystemHdr.read (loc >> flag, Ordering.acqrel);;
        𝒴;;; n <- parse_num r;;
        𝒴;;;
          if (decide (n = 0))
          then Ret (inl tt)
          else 
            𝒴;;; r <- ccallU SystemHdr.read (loc >> data, Ordering.acqrel);;
            𝒴;;; n <- parse_num r;;
            Ret (inr (Val.Vnum n)↑)
      ) ().

  Definition mp2 : Val.t → itree crisE Val.t :=
    λ m,
      𝒴;;; loc <- parse_loc m;;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> data, Val.Vnum 42, Ordering.relaxed);;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> flag, Val.Vnum 1, Ordering.acqrel);;
      𝒴;;; Ret Val.zero.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some MPHdr.mp2, (false, wmask_all, scopes, (None, cfunU (sfunU mp2))));
     (None,           (false, wmask_all, scopes, (None, mp)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End MPI. End MPI.
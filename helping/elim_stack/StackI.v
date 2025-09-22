Require Import CRIS.
Require Import MemHeader.
Require Import SchHeader.
From CRIS.helping Require Import Header.
Require Import StackHeader.

Module StackI. Section StackI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : list string := [].

  Definition new_stack : list val → itree crisE val := λ _,
    𝒴;;; 'stack : val <- ccallU MemHdr.alloc [Vint 2];;
    𝒴;;; Ret stack.

  Definition _push : list val → itree crisE (() + val) := λ args,
    𝒴;;; '((stackb, stackofs), v) : (mblock * ptrofs) * val <- (pargs [Tptr; Tuntyped] args)?;;
    𝒴;;; 'head_old : val <- ccallU MemHdr.load [Vptr (stackb, stackofs)];;
    𝒴;;; 'head_new : val <- ccallU MemHdr.alloc [Vint 2];;
    𝒴;;; '(head_newb, head_newofs) : mblock * ptrofs <- (pargs [Tptr] [head_new])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (head_newb, head_newofs); v];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (head_newb, head_newofs + 1)%Z; head_old];;
    𝒴;;; 'ret : val <-
      ccallU MemHdr.cas [Vptr (stackb, stackofs); head_old; Vptr (head_newb, head_newofs)];;
    𝒴;;;
      if (decide (ret ≠ head_old)) then
          𝒴;;; 'offer : val <- ccallU MemHdr.alloc [Vint 2];;
          𝒴;;; '(offerb, offerofs) : mblock * ptrofs <- (pargs [Tptr] [offer])?;;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (offerb, offerofs); v];;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (offerb, offerofs + 1)%Z; Vint 0];;
          𝒴;;; '_ : val <-
            ccallU MemHdr.store [Vptr (stackb, stackofs + 1)%Z; Vptr (offerb, offerofs)];;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (stackb, stackofs + 1)%Z; Vint 0];;
          𝒴;;; 'ret : val <- ccallU MemHdr.cas [Vptr (offerb, offerofs + 1)%Z; Vint 0; Vint 2];;
          𝒴;;; 'cmpret : val <- ccallU MemHdr.cmp [Vint 0; ret];;
          match cmpret with
          | Vint 0%Z => Ret (inr Vundef)
          | Vint 1%Z => Ret (inl ())
          | _ => triggerUB
          end
      else Ret (inr Vundef).

  Definition push : list val → itree crisE val :=
    λ args, ITree.iter (λ _, (_push args)) ().

  Definition fnsems : fnsems_type :=
    [(Some StackHdr.new_stack, (false, wmask_all, scopes, (None, cfunU new_stack)));
     (Some StackHdr.push,      (false, wmask_all, scopes, (None, cfunU push)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End StackI. End StackI.
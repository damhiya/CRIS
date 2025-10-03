Require Import CRIS.
Require Import SchHeader.
Require Import MemHeader.
Require Import StackHeader.
Require Import PQueueHeader.

Module PQueueI. Section PQueueI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : list string := [].

  Definition new : list val → itree crisE val := λ args,
    𝒴;;; 'n : Z <- (pargs [Tint] args)?;;
    𝒴;;; 'queue : val <- ccallU MemHdr.alloc [Vint n];;
    𝒴;;; '(b, ofs) : _ <- (pargs [Tptr] [queue])?;;
    let n := Z.to_nat n in
    ITree.iter (λ '(n, ofs),
      match n with
      | 0 => Ret (inr ())
      | S n' =>
          'bin : val <- ccallU StackHdr.new_stack (@nil val);;
          '_ : val <- ccallU MemHdr.store [Vptr (b, ofs); bin];; Ret (inl (n', (ofs + 1)%Z))
      end
    ) (n, ofs);;;
    𝒴;;; Ret queue.

  Definition add : list val → itree crisE val := λ args,
    𝒴;;; '(queueb, queueofs, (p, v)) : _ <- (pargs [Tptr; Tint; Tuntyped] args)?;;
    𝒴;;; 'bin : val <- ccallU MemHdr.load [Vptr (queueb, queueofs + p)%Z];;
    𝒴;;; '_ : val <- ccallU StackHdr.push [bin; v];;
    𝒴;;; Ret Vundef.

  Definition fnsems : fnsems_type :=
    [(Some PQueueHdr.new, (false, wmask_all, scopes, (None, cfunU new)));
     (Some PQueueHdr.add, (false, wmask_all, scopes, (None, cfunU add)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End PQueueI. End PQueueI.
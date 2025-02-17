Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader SchHeader.

Module IncrI. Section IncrI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  (* faa(loc, 1) *)
  Definition incr : list val → itree pmodE val :=
    λ arg,
      Sch.yield;;;
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      v <- (ITree.iter
        (λ _,
          Sch.yield;;;
          'v_raw : val <- ccallU MemName.load [Vptr blk ofs];;
          Sch.yield;;;
          'v : Z <- (pargs [Tint] [v_raw])?;;
          Sch.yield;;;
          'flag_raw : val <- ccallU MemName.cas [Vptr blk ofs; Vint v; Vint (v + 1)%Z];;
          Sch.yield;;;
          flag <- (pargs [Tint] [flag_raw])?;;
          Sch.yield;;;
          match flag with
          | 0%Z => Ret (inl tt)
          | 1%Z => Ret (inr (Vint (v + 1)%Z))
          | _ => triggerUB
          end
        ) tt);;
      Ret v.

  Definition fnsems :=
    [(IncrName.incr, (scopes, cfunU incr))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End IncrI. End IncrI.

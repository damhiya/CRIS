Require Import CRIS.
Require Import ImpPrelude IncrMainHeader MemHeader SchHeader.

Module IncrMainI. Section IncrMainI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition main : unit → itree pmodE unit :=
    λ _,
      Sch.yield;;;
      'ptr_raw : val <- ccallU MemName.alloc [Vint 1%Z];;
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] [ptr_raw])?;;
      Sch.yield;;;
      '_ : val <- ccallU MemName.store [Vptr blk ofs; Vint 0%Z];;
      Sch.yield;;;
      tid1 <- Sch.spawn ("f", [Vptr blk ofs]↑↑);;
      Sch.yield;;;
      tid2 <- Sch.spawn ("f", [Vptr blk ofs]↑↑);;
      Sch.yield;;;
      Sch.join unit tid1;;;
      Sch.yield;;;
      Sch.join unit tid2;;;
      Sch.yield;;;
      'v_raw : val <- ccallU MemName.load [Vptr blk ofs];;
      'v : Z <- (pargs [Tint] [v_raw])?;;
      Sch.yield;;;
      '_ : unit <- trigger (IO "OUT" v);;
      Ret tt.
  
  Definition f : list val → itree pmodE unit :=
    λ arg,
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      Sch.yield;;;
      'v_raw : val <- ccallU MemName.load [Vptr blk ofs];;
      'v : Z <- (pargs [Tint] [v_raw])?;;
      '_ : val <- ccallU MemName.store [Vptr blk ofs; Vint (v + 1)%Z];;
      Ret tt.

  Definition fnsems :=
    [(MainName.main, (scopes, cfunU main));
     (MainName.f,    (scopes, cfunU (sfunU f)))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End IncrMainI. End IncrMainI.

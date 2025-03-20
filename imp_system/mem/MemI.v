Require Import CRIS.

Require Export MemHeader.

Set Implicit Arguments.
Set Typeclasses Depth 5.

Module MemI. Section MemI.
  Context {Σ: GRA}.

  Definition scopes := ["Mem"].
  Definition v_mem := "Mem" ↯ "mem".

  Definition alloc : list val → itree pmodE val :=
    fun varg =>
      'sz : Z <- (pargs [Tint] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
      then (delta <- trigger (Choose _);;
            let mem0 : Mem.t := Mem.mem_pad mem delta in
            let (blk, mem1) := Mem.alloc mem0 sz in
            trigger (SPut v_mem mem1↑);;;
            Ret (Vptr blk 0))
      else triggerUB
. 

  Definition free : list val → itree pmodE val :=
    λ varg,
      '(b, ofs): (nat * Z) <- (pargs [Tptr] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem b ofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  . 

  Definition load: list val -> itree pmodE val :=
    fun varg =>      
      '(b, ofs): (nat * Z) <- (pargs [Tptr] varg)?;;        
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem b ofs)?;;
      Ret v
  .

  Definition store : list val → itree pmodE val :=
    fun varg =>
      '(b, ofs, v): (nat * Z * val) <- (pargs [Tptr; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem b ofs v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition cmp : list val → itree pmodE val :=
    fun varg =>
      '(v0, v1): (val * val) <- (pargs [Tuntyped; Tuntyped] varg)?;;
      '(v0, v1): (val * val) <- (pargs [Tuntyped; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      b <- (vcmp mem v0 v1)?;;
      if b: bool
      then 
        Ret (Vint 1%Z)
      else
        Ret (Vint 0%Z)
  .

  Definition cas: list val -> itree pmodE val :=
    fun varg =>
     ' (b, ofs, (v_old, v_new)): (nat * Z * (val * val)) <- (pargs [Tptr; Tuntyped; Tuntyped] varg)?;;        
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      d <- (Mem.load mem b ofs)?;;
      if (dec d v_old)
      then
        mem1 <- (Mem.store mem b ofs v_new)?;;
        _ <- trigger (SPut v_mem mem1↑);;
        Ret (Vint 1%Z)
      else
        Ret (Vint 0%Z)
  .
  
  Definition fnsems : alist string (list string * (Any.t -> itree pmodE Any.t)) :=
    [(MemHdr.alloc, (scopes, cfunU alloc)) ;
     (MemHdr.free,  (scopes, cfunU free)) ;
     (MemHdr.load,  (scopes, cfunU load)) ;
     (MemHdr.store, (scopes, cfunU store)) ;
     (MemHdr.cmp,   (scopes, cfunU cmp)) ;
     (MemHdr.cas,   (scopes, cfunU cas))].

  Program Definition Mem csl genv : PMod.t :=
    {|
      PMod.scopes := scopes;
      PMod.fnsems := fnsems ;
      PMod.initial_st := [(v_mem, (Mem.load_mem csl genv)↑)];
    |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t csl genv : HMod.t := Seal.sealing CRIS (PMod.to_hmod (Mem csl genv)).
End MemI. End MemI.
   
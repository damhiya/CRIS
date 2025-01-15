Require Import CRIS.

Require Import ImpPrelude.
Require Export MemHeader.

Set Implicit Arguments.
Set Typeclasses Depth 5.

Module MemI.
Section MEMI.

  Definition scope := "Mem".
  Definition v_mem := scope ↯ "mem".

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
    fun varg =>
      '(b, ofs): _ <- (pargs [Tptr] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem b ofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition load : list val → itree pmodE val :=
    fun varg =>
      '(b, ofs): _ <- (pargs [Tptr] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem b ofs)?;;
      Ret v
  .

  Definition store : list val → itree pmodE val :=
    fun varg =>
      '(b, ofs, v): _ <- (pargs [Tptr; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem b ofs v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition cmp : list val → itree pmodE val :=
    fun varg =>
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      b <- (vcmp mem v0 v1)?;;
      if b : bool
      then Ret (Vint 1%Z)
      else Ret (Vint 0%Z)
  .

  Definition fnsems : alist string (list string * (Any.t → itree pmodE Any.t)) :=
    [(MemName.alloc, ([scope], cfunU alloc)) ;
     (MemName.free,  ([scope], cfunU free)) ;
     (MemName.load,  ([scope], cfunU load)) ;
     (MemName.store, ([scope], cfunU store)) ;
     (MemName.cmp,   ([scope], cfunU cmp))].

  Variable csl : string → bool.

  Program Definition MemSem (sk : Sk.t) : PModSem.t :=
    {|
      PModSem.scopes := [scope];
      PModSem.fnsems := fnsems ;
      PModSem.initial_st := [(v_mem, (Mem.load_mem csl sk)↑)];
    |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mem : PMod.t := {|
    PMod.modsem := MemSem;
    PMod.sk := Sk.unit;
  |}
  .

  Context `{Σ : GRA}.
  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mem).

End MEMI.
End MemI.

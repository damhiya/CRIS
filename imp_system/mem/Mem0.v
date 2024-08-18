Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import PMod HMod Events.
Require Import Skeleton.
Require Import PCM ITactics.

Set Implicit Arguments.
Set Typeclasses Depth 5.





Section PROOF.
  (* Let memRA: URA.t := (RA.excl Mem.t). *)
  (* Context `{@GRA.inG memRA Σ}. *)
  (* Let GURA: URA.t := GRA.to_URA Σ. *)
  (* Local Existing Instance GURA. *)
  (* Compute (URA.car (t:=memRA)). *)

  Section BODY.
    Definition allocF: (list val) -> itree pmodE val :=
      fun varg =>
        `sz: Z <- (pargs [Tint] varg)?;;
        mem <- trigger (SGet "Mem.mem");; mem <- mem↓?;;
        if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
        then (delta <- trigger (Choose _);;
              let mem0: Mem.t := Mem.mem_pad mem delta in
              let (blk, mem1) := Mem.alloc mem0 sz in
              trigger (SPut "Mem.mem" mem1↑);;;
              Ret (Vptr blk 0))
        else triggerUB
    .

    Definition freeF: list val -> itree pmodE val :=
      fun varg =>
        '(b, ofs) <- (pargs [Tptr] varg)?;;        
        mem <- trigger (SGet "Mem.mem");; mem <- mem↓?;;
        mem1 <- (Mem.free mem b ofs)?;;
        trigger (SPut "Mem.mem" mem1↑);;;
        Ret (Vint 0)
    .

    Definition loadF: list val -> itree pmodE val :=
      fun varg =>
        '(b, ofs) <- (pargs [Tptr] varg)?;;        
        mem <- trigger (SGet "Mem.mem");; mem <- mem↓?;;
        v <- (Mem.load mem b ofs)?;;
        Ret v
    .

    Definition storeF: list val -> itree pmodE val :=
      fun varg =>
        '(b, ofs, v) <- (pargs [Tptr; Tuntyped] varg)?;;
        mem <- trigger (SGet "Mem.mem");; mem <- mem↓?;;
        mem1 <- (Mem.store mem b ofs v)?;;
        trigger (SPut "Mem.mem" mem1↑);;;
        Ret (Vint 0)
    .

    Definition cmpF: list val -> itree pmodE val :=
      fun varg =>
        '(v0, v1) <- (pargs [Tuntyped; Tuntyped] varg)?;;        
        mem <- trigger (SGet "Mem.mem");; mem <- mem↓?;;
        b <- (vcmp mem v0 v1)?;;
        if b: bool
        then Ret (Vint 1%Z)
        else Ret (Vint 0%Z)
    .

  End BODY.

  Require Import IPM.
  Context `{Σ: GRA.t}.
  
  Definition fnsems : alist string (list string * (Any.t -> itree pmodE Any.t)) :=
    [("alloc", (["Mem.mem"], cfunU allocF)) ;
     ("free",  (["Mem.mem"], cfunU freeF)) ;
     ("load",  (["Mem.mem"], cfunU loadF)) ;
     ("store", (["Mem.mem"], cfunU storeF)) ;
     ("cmp",   (["Mem.mem"], cfunU cmpF))].

  Variable csl: gname -> bool.

  Program Definition MemSem (sk: Sk.t): PModSem.t :=
    {|
      PModSem.fnsems := fnsems ;
      PModSem.initial_st := [("Mem.mem", (Mem.load_mem csl sk)↑)];
    |}
  .
  Next Obligation. prove_scope. Qed.

  Definition _Mem: PMod.t := {|
    PMod.get_modsem := MemSem;
    PMod.sk := Sk.unit;
  |}
  .

  Definition Mem : HMod.t := Seal.sealing "ccr" (PMod.to_hmod _Mem).
  
End PROOF.

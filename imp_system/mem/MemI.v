Require Import CRIS.

Require Export MemHeader.

Set Implicit Arguments.
Set Typeclasses Depth 5.

Module Mem.

  (* Definition t : Type := mblock -> option (Z -> val). *)
  Record t : Type := mk {
    cnts : mblock -> Z -> option val;
    nb : mblock;
    (*** Q : wf conditions like nextmblock_noaccess ? ***)
    (*** A : Unlike in CompCert, the memory object will not float in various places in the program.
            It suffices to state wf only inside Mem module. (probably by utilizing URA.wf)
     ***)
  }
  .

  Definition wf (m0 : t) : Prop := forall blk ofs (LT : (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition alloc (m0 : Mem.t) (sz : Z) : (mblock * Mem.t) :=
    ((m0.(nb)),
     Mem.mk (update (m0.(cnts)) (m0.(nb))
                    (fun ofs => if (0 <=? ofs)%Z && (ofs <? sz)%Z then Some (Vundef) else None))
            (S m0.(nb))
    )
  .

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.
  (* Definition empty : t := mk (update (fun _ _ => None) 0 (fun ofs => if dec ofs 0%Z then Some Vundef else None)) 0. *)
  Definition empty : t := mk (fun _ _ => None) 0.
  (* Let empty2 : t := Eval compute in *)
  (*   let m0 := mk (fun _ _ => None) 0 in *)
  (*   let (_, m1) := alloc m0 1%Z in *)
  (*   m1 *)
  (* . *)
  (*** shoul allocated with Vundef, not 0 ***)

  (*** TODO : Unlike CompCert, this "free" function does not take offset.
       In order to support this, we need more sophisticated RA. it would be interesting.
   ***)
  (* Definition free (m0 : Mem.t) (b : mblock) : option (Mem.t) := *)
  (*   match m0.(cnts) b ofs0 with *)
  (*   | Some _ => Some (Mem.mk (update m0.(cnts) b (fun _ => None)) m0.(nb)) *)
  (*   | _ => None *)
  (*   end *)
  (* . *)

  Definition free (m0 : Mem.t) := fun '(b,ofs) =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end
  .

  Definition load (m0 : Mem.t) := fun '(b,ofs) =>
    m0.(cnts) b ofs.

  Definition store (m0 : Mem.t) := fun '(b,ofs) v =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end
  .

  Definition valid_ptr (m0 : Mem.t) := fun '(b,ofs) =>
    is_some (m0.(cnts) b ofs).

(*** NOTE : Probably we can support comparison between nullptr and 0 ***)
(*** NOTE : Unlike CompCert, we don't support comparison with weak_valid_ptr (for simplicity) ***)

  Definition load_mem (csl : string -> bool) (genv : GEnv.t) : Mem.t :=
    Mem.mk
      (fun blk ofs =>
         do '(g, gd) <- (List.nth_error genv blk);
         match gd↓ with
         | Some Gfun =>
           None
         | Some (Gvar gv) =>
           if csl g then None else
           if (dec ofs 0%Z) then Some (Vint gv) else None
          | _ => None
         end)
      (*** TODO : This simplified model doesn't allow function pointer comparsion.
           To be more faithful, we need to migrate the notion of "permission" from CompCert.
           CompCert expresses it with "nonempty" permission.
       ***)
      (*** TODO : When doing so, I would like to extend val with "Vfid (id : string)" case.
           That way, I might be able to support more higher-order features (overriding, newly allocating function)
       ***)
      (List.length genv)
  .

  Definition mem_pad (m0 : Mem.t) (delta : nat) : Mem.t :=
    Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta)
  .

  Definition vcmp (m0 : Mem.t) (x y : val) : option bool :=
    match x, y with
    | Vint x, Vint y => Some (dec x y : bool)
    | Vptr (x, xofs), Vptr (y, yofs) =>
      if Mem.valid_ptr m0 (x, xofs) && Mem.valid_ptr m0 (y, yofs)
      then Some (dec x y && dec xofs yofs)
      else None
    | Vptr (x, xofs), Vint y =>
      if Mem.valid_ptr m0 (x, xofs) && dec y 0%Z
      then Some false
      else None
    | Vint x, Vptr (y, yofs) =>
      if Mem.valid_ptr m0 (y, yofs) && dec x 0%Z
      then Some false
      else None
    | _, _ => None
    end.

End Mem.

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
            Ret (Vptr (blk, 0%Z)))
      else triggerUB
. 

  Definition free : list val → itree pmodE val :=
    λ varg,
      bofs <- (pargs [Tptr] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem bofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  . 

  Definition load: list val -> itree pmodE val :=
    fun varg =>      
      bofs <- (pargs [Tptr] varg)?;;        
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem bofs)?;;
      Ret v
  .

  Definition store : list val → itree pmodE val :=
    fun varg =>
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem bofs v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition cmp : list val → itree pmodE val :=
    fun varg =>
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] varg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      'b: bool <- (Mem.vcmp mem v0 v1)?;;
      if b
      then 
        Ret (Vint 1%Z)
      else
        Ret (Vint 0%Z)
  .

  Definition cas: list val -> itree pmodE val :=
    fun varg =>
      ' (bofs, (v_old, v_new)): _ <- (pargs [Tptr; Tuntyped; Tuntyped] varg)?;;
      'd: val <- ccallU MemHdr.load [Vptr bofs];;
      if (dec d v_old)
      then
        '_: val <- ccallU MemHdr.store [Vptr bofs; v_new];;
        Ret d
      else
        Ret d
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

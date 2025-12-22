From CRIS Require Import CRIS MemHeader.

Set Implicit Arguments.
Set Typeclasses Depth 5.

Module Mem.
  Record t : Type := mk {
    cnts : mblock → Z → option val;
    nb : mblock;
  }
  .

  Definition wf (m0 : t) : Prop := ∀ blk ofs (LT : (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition alloc (m0 : Mem.t) (sz : Z) : mblock * Mem.t :=
    ((nb m0),
     Mem.mk (update (m0.(cnts)) (m0.(nb))
                    (fun ofs => if (0 <=? ofs)%Z && (ofs <? sz)%Z then Some (Vundef) else None))
            (S m0.(nb))
    ).

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.

  Definition empty : t := mk (fun _ _ => None) 0.

  Definition free (m0 : Mem.t) := fun '(b,ofs) =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end.

  Definition load (m0 : Mem.t) := fun '(b,ofs) =>
    m0.(cnts) b ofs.

  Definition store (m0 : Mem.t) := fun '(b,ofs) v =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end.

  Definition valid_ptr (m0 : Mem.t) := fun '(b,ofs) =>
    is_some (m0.(cnts) b ofs).

  Definition load_mem (csl : string → bool) (genv : GEnv.t) : Mem.t :=
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
      (List.length genv).

  Definition mem_pad (m0 : Mem.t) (delta : nat) : Mem.t :=
    Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta).

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
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition scopes : gmultiset string := {[+"Mem"+]}.
  Definition v_mem : key := "Mem" ↯ "mem".

  Definition alloc : list val → itree crisE val :=
    λ arg,
      'sz : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
      then (delta <- trigger (Choose _);;
            let mem0 : Mem.t := Mem.mem_pad mem delta in
            let (blk, mem1) := Mem.alloc mem0 sz in
            trigger (SPut v_mem mem1↑);;;
            Ret (Vptr (blk, 0%Z)))
      else triggerUB. 

  Definition free : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem bofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  . 

  Definition load: list val → itree crisE val :=
    λ arg,      
      bofs <- (pargs [Tptr] arg)?;;        
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem bofs)?;;
      Ret v
  .

  Definition store : list val → itree crisE val :=
    λ arg,
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem bofs v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition cmp : list val → itree crisE val :=
    λ arg,
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      'b: bool <- (Mem.vcmp mem v0 v1)?;;
      Ret (Vint (if b then 1 else 0))
  .

  Definition cas: list val → itree crisE val :=
    λ arg,
      '(bofs, (v_old, v_new)) : _ <- (pargs [Tptr; Tuntyped; Tuntyped] arg)?;;
      'v_cur : val <- ccallU MemHdr.load [Vptr bofs];;
      'succ : val <- ccallU MemHdr.cmp [v_cur; v_old];;
      (if (decide (succ = (Vint 1)))
       then ccallU MemHdr.store [Vptr bofs; v_new]
       else Ret Vundef);;;
      Ret v_cur.

  Definition fnsems : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some MemHdr.alloc := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU alloc)));
      Some MemHdr.free := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU free)));
      Some MemHdr.load := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU load)));
      Some MemHdr.store := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU store)));
      Some MemHdr.cmp := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU cmp)));
      Some MemHdr.cas := Some (msk_real (msk_scp scopes msk_true), (None, (cfunU cas)))]}.

  Program Definition smod csl genv : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem := Some (Mem.load_mem csl genv)↑]};
  |}.
  Solve Obligations with auto.
  Next Obligation.
    i.
    rewrite ?omap_insert /= omap_empty.
    mod_tac scope_solver.
  Qed.
  Next Obligation.
    i. mod_tac scope_solver.
  Qed.

  (* TODO : Sealing *)
  Definition t csl genv := (SMod.to_mod ∅ (smod csl genv)).
End MemI. End MemI.

Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader.
(** * Implementation of the queue operations ********************************)

Module HWQI. Section HWQI.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.

  Definition new_queue : list val → itree crisE val := λ sz,
    𝒴;;; sz <- (pargs [Tint] sz)?;;
    𝒴;;; 'q : val <- ccallU MemHdr.alloc [Vint (2 + sz)];;
    𝒴;;; '(qblk, qofs) : _ <- (pargs [Tptr] [q])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs); Vint sz];; (* size of the queue *)
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 1)%Z; Vint 0];; (* first free cell *)
    𝒴;;; ITree.iter (λ (x : nat), (* initialization *)
      𝒴;;;
        if Nat.ltb x (Z.to_nat sz) 
        then 
          '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 2 + x)%Z; Vint 0];; Ret (inl (S x))
        else
          Ret (inr ())
    ) 0;;;
    𝒴;;; Ret q.

  Definition enqueue : list val → itree crisE val := λ q,
    𝒴;;; '(qblk, qofs, v) : mblock * ptrofs * _ <- (pargs [Tptr; Tptr] q)?;;
    𝒴;;; 'sz : val <- ccallU MemHdr.load [Vptr (qblk, qofs)];;
    𝒴;;; 'sz : Z <- (pargs [Tint] [sz])?;;
    𝒴;;; 'back : val <- MemHdr.faa [Vptr (qblk, qofs + 1)%Z];;
    𝒴;;; 'back : Z <- (pargs [Tint] [back])?;;
    𝒴;;;
      if (Z.ltb back sz)
      then
        𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 2 + back)%Z; Vptr v];;
        𝒴;;; Ret Vundef
      else
        𝒴;;; ITree.iter (λ _, 𝒴;;; Ret (inl ())) ().
    (** enqueue(q : queue, x : item){
      let i : int := FAA(q.back, 1) in
      if(i < q.size){
        q.items[i] := x
      } else {
        while true;
      }
    } *)
(* Definition enqueue : val :=
  λ: "q" "x",
    let: "q_size" := Fst (Fst (Fst "q")) in
    let: "q_ar"   := Snd (Fst (Fst "q")) in
    let: "q_back" := Snd (Fst "q") in
    (* Get the next free index. *)
    let: "i" := FAA "q_back" #1 in
    (* Check not full, and actually insert. *)
    if: "i" < "q_size" then "q_ar"<[["i"]]> <- SOME "x" ;; Skip
    else diverge #(). *)

(** dequeue(q : queue){
      let range = min(!q.back, q.size) in
      let rec dequeue_aux(i) =
        if i = 0 {
          dequeue(q)
        } else {
          let j = range - i in
          let x = ! q.ar[j] in
          if x == null {
            dequeue_aux(i-1)
          } else {
            if resolve (CAS q.ar[j] x null) q.p (j, x) {
              v
            } else {
              dequeue_aux(i-1)
            }
          }
        }
      in
      dequeue_aux(range)
    } *)
(* Definition dequeue_aux : val :=
  rec: "loop" "dequeue" "q" "range" "i" :=
    if: "i" = #0 then "dequeue" "q" else
      let: "q_ar" := Snd (Fst (Fst "q")) in
      let: "q_p"  := Snd "q" in
      let: "j"    := "range" - "i" in
      let: "x"    := ! "q_ar"<[["j"]]> in
      match: "x" with
        NONE     => "loop" "dequeue" "q" "range" ("i" - #1)
      | SOME "v" =>
        let: "c" := Resolve (CmpXchg ("q_ar"<[["j"]]>) "x" NONE) "q_p" "j" in
        if: Snd "c" then "v" else "loop" "dequeue" "q" "range" ("i" - #1)
      end.
Definition dequeue : val :=
  rec: "dequeue" "q" :=
    let: "q_size" := Fst (Fst (Fst "q")) in
    let: "q_back" := Snd (Fst "q") in
    let: "range"  := minimum !"q_back" "q_size" in
    dequeue_aux "dequeue" "q" "range" "range". *)

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_real (msk_scp [] msk_true), (None, cfunU new_queue));
      fid HWQHdr.enqueue   # (msk_real (msk_scp [] msk_true), (None, cfunU enqueue));
      fid HWQHdr.dequeue   # (msk_real (msk_scp [] msk_true), (None, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HWQI. End HWQI.

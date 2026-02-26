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
      fid HWQHdr.enqueue   # (msk_real (msk_scp [] msk_true), (None, fbody_trivial));
      fid HWQHdr.dequeue   # (msk_real (msk_scp [] msk_true), (None, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HWQI. End HWQI.


(* Lemma big_lemma γe γs (ls : list loc) slots (p : list nat) :
  NoDup p →
  (∀ i, i ∈ p → was_committed <$> slots !! i = Some false) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
   ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) -∗
   own γe (● (Excl' ls)) ={⊤ ∖ ↑N}=∗
    own γs (● (of_slot_data <$> map_imap (helped p) slots) : slotUR) ∗
    ([∗ map] i ↦ d ∈ map_imap (helped p) slots, per_slot_own γe γs i d) ∗
    own γe (● (Excl' (ls ++ get_values slots p))).
Proof.
  revert p. iIntros (p).
  iInduction p as [|n ps] "IH" forall (slots ls); iIntros (HNoDup H) "Hs● Hbig He●".
  - iModIntro. rewrite /= app_nil_r map_imap_helped_nil. iFrame.
  - assert (∀ i : nat, i ∈ ps → was_committed <$> slots !! i = Some false) as H1.
    { intros i Hi. apply H. apply elem_of_list_further, Hi. }
    assert (was_committed <$> slots !! n = Some false) as H2.
    { apply H. apply elem_of_list_here. }
    assert (∃ ln γn wn, slots !! n = Some (ln, Pend γn, wn)) as Hn.
    { destruct (slots !! n) as [[[ln sn] wn]|]; last by inversion H2.
      (destruct sn as [γn|γn|]; last by inversion H2); by exists ln, γn, wn. }
    apply NoDup_cons in HNoDup. destruct HNoDup as [Hn_not_in_ps HNoDup].
    destruct Hn as [l [γ [w Hn]]].
    assert (slots = <[n:=(l, Pend γ, w)]> (delete n slots)) as Hs.
    { by rewrite insert_delete_insert insert_id. }
    rewrite [in ([∗ map] _ ↦ _ ∈ slots, _)%I]Hs.
    iDestruct (big_sepM_insert with "Hbig")
      as "[Hbig_n Hbig]"; first by apply lookup_delete_eq.
    iDestruct "Hbig_n" as "[Hval_wit_n [Hwritten_n [Hpending_tok_n H]]]".
    iDestruct "H" as (Q) "[Hsaved AU]".
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (ls ++ [l]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HPost".
    iMod (use_pending_tok with "Hs● Hpending_tok_n")
      as "[Hs● Hcommitted_wit_n]"; first by rewrite Hn.
    iCombine "Hsaved HPost" as "Hn".
    iDestruct (big_sepM_insert _ (delete n slots) n (l, Help γ, w)
      with "[Hn Hval_wit_n Hwritten_n Hcommitted_wit_n Hbig]")
      as "Hbig"; first by apply lookup_delete_eq.
    { iClear "IH". iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
      iExists Q. iDestruct "Hn" as "[$ HPost]". iNext. done. }
    rewrite insert_delete_insert /update_slot Hn insert_delete_insert.
    assert (∀ i : nat, i ∈ ps → was_committed <$> <[n:=(l, Help γ, w)]> slots !! i = Some false) as HHH.
    { intros i Hi. rewrite lookup_insert_ne; [ by apply H1 | by set_solver ]. }
    iMod ("IH" $! (<[n:=(l, Help γ, w)]> slots) (ls ++ [l]) HNoDup HHH
            with "Hs● Hbig He●") as "[Hs● [Hbig He●]]"; iClear "IH".
    assert (map_imap (helped ps) (<[n:=(l, Help γ, w)]> slots)
            = map_imap (helped (n :: ps)) slots) as ->.
    { apply map_eq. intros i. destruct (decide (i = n)) as [->|Hi_not_n].
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert Hn /=.
        rewrite /helped /=. rewrite decide_True; first done. set_solver.
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_ne; last done.
        destruct (slots !! i) as [[[li si] wi]|]; last done. simpl.
        rewrite /helped /=. destruct si; try done.
        destruct (decide (i ∈ n :: ps)).
        + rewrite decide_True; first done. set_solver.
        + rewrite decide_False; first done. set_solver. }
    iModIntro. iFrame.
    by rewrite /= Hn -app_assoc /= get_values_not_in.
Qed. *)

(* Lemma array_contents_cases γs slots deqs i li :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i li -∗
    ⌜array_get slots deqs i = SOMEV #li ∨ array_get slots deqs i = NONEV⌝.
Proof.
  iIntros "Hs● Hval_wit_i".
  iDestruct (use_val_wit with "Hs● Hval_wit_i") as %Hslots_i.
  destruct (slots !! i) as [d|] eqn:HEq; last by inversion Hslots_i.
  destruct d as [[li' si] wi]. inversion Hslots_i as [H]; subst li'.
  rewrite /array_get HEq. simpl. iPureIntro.
  destruct (decide (i ∈ deqs)); first by right.
  destruct wi; by [ left | right ].
Qed. *)

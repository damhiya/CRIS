Require Import CRIS.
Require Export ImpPrelude MemHeader MemA.

Section mem.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG}.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap (option string) (option (Any.t → itree crisE Any.t))).
  Context (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Context (sp : specmap).

  Lemma wsim_mem_alloc (sz : Z) k_s k_t E1 E2 r g :
    fl_t !! (Some MemHdr.alloc) =
      Some (Some (SB.sandbox_body
        (msk_scp MemA.scopes msk_true,
         SModTr.trans_fnsem sp (Some MemSpec.alloc, fbody_trivial)))) →
    (0 <= 8 * sz < modulus_64)%Z →
    (∀ blk,
      ([∗ list] i ↦ v ∈ replicate (Z.to_nat sz) Vundef, (blk, Z.of_nat i)%Z ↦ v) -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
      (st_src, k_s)
      (st_tgt, k_t (Vptr (blk, 0%Z))↑)) ⊢
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- (trigger (Call MemHdr.alloc [Vint sz]↑));; k_t x).
  Proof.
    intros Hin Hsz.
    iIntros "K".
    inline_r. force_r (nroot, 0). force_r (Z.to_nat sz). forces_r. iSplit; eauto.
    { rewrite Z2Nat.id //; try lia. iSplit; eauto. iSplit; eauto. iPureIntro; lia. }
    steps_r. iDestruct "GRT" as "[-> [% [-> ↦]]]". iApply "K".
    iApply (big_sepL_impl with "↦").
    iIntros "!> % % %"; rewrite Z.add_0_l; iIntros "$".
  Qed.

  Lemma wsim_mem_store b ofs v v' k_s k_t E1 E2 r g :
    fl_t !! Some MemHdr.store =
      Some (Some (SB.sandbox_body
        (msk_scp MemA.scopes msk_true,
         SModTr.trans_fnsem sp (Some MemSpec.store, fbody_trivial)))) →
    (b, ofs) ↦ v' -∗
    ((b, ofs) ↦ v -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.store [Vptr (b, ofs); v]↑);; k_t x).
  Proof.
    intros Hin.
    iIntros "↦ K".
    inline_r. force_r (nroot, 0). force_r (b, ofs, v', v). forces_r. iFrame "↦"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[-> [↦ ->]]". iApply "K"; iFrame.
  Qed.

  Lemma wsim_mem_load b ofs q v k_s k_t E1 E2 r g :
     fl_t !! Some MemHdr.load =
      Some (Some (SB.sandbox_body
        (msk_scp MemA.scopes msk_true,
         SModTr.trans_fnsem sp (Some MemSpec.load, fbody_trivial)))) →
    (b, ofs) ↦{q} v -∗
    ((b, ofs) ↦{q} v -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.load [Vptr (b, ofs)]↑);; k_t x).
  Proof.
    intros Hin.
    iIntros "↦ K".
    inline_r. force_r (nroot, 0). force_r (b, ofs, q, v). forces_r. iFrame "↦"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[-> [↦ ->]]". iApply "K"; iFrame.
  Qed.

  Lemma wsim_mem_cas b ofs v v_old v_new succ E k_s k_t E1 E2 r g  :
    fl_t !! Some MemHdr.cas =
      Some (Some (SB.sandbox_body
        (msk_scp MemA.scopes msk_true,
         SModTr.trans_fnsem sp (Some MemSpec.cas, fbody_trivial)))) →
    MemSpec.compare_val v v_old = Vint succ →
    (b, ofs) ↦ v -∗
    E -∗
    (E ==∗ ∃ q0 q1 v0 v1, MemSpec.val_r v q0 v0 ∗ MemSpec.val_r v_old q1 v1 ∗
          (MemSpec.val_r v q0 v0 ∗ MemSpec.val_r v_old q1 v1 ==∗ E)) -∗
    (((b, ofs) ↦ if (bool_decide (succ = 1)) then v_new else v) -∗
     E -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.cas [Vptr (b, ofs); v_old; v_new]↑);; k_t x).
  Proof.
    intros Hin Hmsk.
    iIntros "↦ E HE K".
    inline_r. force_r (nroot, 0). force_r (b, ofs, v, v_old, v_new, succ, E). forces_r.
    iFrame "↦ E HE"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[-> [-> [↦ E]]]". iApply ("K" with "↦ E"); iFrame.
  Qed.

  (* 
  Lemma wsim_mem_cmp v1 v2 succ E k_s k_t E1 E2 r g img_t msk_t scp_t msk_m :
    alist_find (Some MemHdr.cmp) fl_t =
      Some (SB.sandbox_body
        (SModTr.trans_fnsem sp
          (true, msk_m, MemA.scopes, (Some (MemSpec.cmp), fbody_trivial)))) →
    (msk_t MemHdr.cmp : bool) →
    MemSpec.compare_val v1 v2 = Vint succ →
    E -∗
    (E ==∗ ∃ q0 q1 v1' v2', MemSpec.val_r v1 q0 v1' ∗ MemSpec.val_r v2 q1 v2' ∗
          (MemSpec.val_r v1 q0 v1' ∗ MemSpec.val_r v2 q1 v2' ==∗ E)) -∗
    (E -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint succ)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt,
        x <- (SB.sandbox img_t msk_t scp_t
          (trigger (Call MemHdr.cmp [v1; v2]↑)));;
        k_t x).
  Proof.
    intros Hin Hmsk Hcmp.
    iIntros "E HE K".
    inline_r. steps_r. force_r (v1, v2, succ, E). forces_r.
    iFrame "E HE"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[-> E] ->]". iApply ("K" with "E"); iFrame.
  Qed. *)
End mem.

Require Import CRIS.
Require Export ImpPrelude MemHeader MemA.

Section mem.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : alist (option string) (Any.t → itree crisE Any.t)).
  Context (Ist : alist key Any.t → alist key Any.t → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Lemma wsim_mem_alloc (sz : Z) k_s k_t E1 E2 r g img_t msk_t scp_t :
    alist_find (Some MemHdr.alloc) fl_t =
      Some (SB.sandbox_body
        (SModTr.trans_ktree sp_none
          (true, wmask_all, MemA.scopes, (Some (to_fspec MemSpec.alloc), fbody_trivial)))) →
    (msk_t MemHdr.alloc : bool) →
    (0 <= 8 * sz < modulus_64)%Z →
    (∀ blk,
      ([∗ list] i ↦ v ∈ repeat Vundef (Z.to_nat sz), (blk, Z.of_nat i)%Z ↦ v) -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
      (st_src, k_s)
      (st_tgt, k_t (Vptr (blk, 0%Z))↑))
    ⊢ wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
    (st_src, k_s)
    (st_tgt, x <- (SB.sandbox img_t msk_t scp_t (trigger (Call MemHdr.alloc [Vint sz]↑)));; k_t x).
  Proof.
    intros Hin Hmsk Hsz.
    iIntros "K".
    inline_r. steps_r. force_r (Z.to_nat sz). forces_r. iSplit; eauto.
    { rewrite Z2Nat.id //; try lia. iSplit; eauto. iSplit; eauto. iPureIntro; lia. }
    steps_r. iDestruct "GRT" as "[[% [-> ↦]] ->]". iApply "K".
    iApply (big_sepL_impl with "↦").
    iIntros "!> % % %"; rewrite Z.add_0_l; iIntros "$".
  Qed.
End mem.
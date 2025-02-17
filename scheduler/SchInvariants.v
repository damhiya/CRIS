Require Import CRIS.

Require Import functions.
From iris Require Import gmap_view.

Set Implicit Arguments.

(** TODO: The following code will be deprecated once wsim, an improved version of isim that avoids the direct use of wsats, is developed. This file contains lemmas that can be used to explicitly open and close invariants at the isim level. *)

Local Notation univ_id := positive.
Local Notation level := nat.

Section wsats_aux.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.

  Local Definition wsatseq u n := ([∗ list] n ∈ (seq 0 n), wsat u n)%I.

  Lemma wsatseq_fold u n:
    wsatseq u n = ([∗ list] n ∈ (seq 0 n), wsat u n)%I.
  Proof. ss. Qed.

  Lemma wsats_fold u b :
    wsatseq u (S b) ⊣⊢ (wsat u b ∗ wsatseq u b)%I.
  Proof.
    iSplit; replace (S b) with (b + 1) by lia; rewrite /wsatseq (seq_app b 1 0); ss;
      iIntros; by rewrite big_sepL_app big_sepL_singleton comm.
  Qed.

  Lemma free_worlds_alloc u (b b' : level) (NIN : b < b') :
    wsat_auth u b ⊢ wsat_auth u b' ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    rewrite /wsat_auth /wsat_authR.
    induction NIN; iIntros "FW".
    { replace (S b - b) with 1 by lia; ss.
      iEval (rewrite (discrete_fun_delete b (λ n, if n <? b then ε else gmap_view_auth (DfracOwn 1) ∅))) in "FW".
      rewrite -discrete_fun_singleton_op own_op. des_ifs; first by rewrite Nat.ltb_lt in Heq; lia.
      iDestruct "FW" as "[FW1 FW2]"; iSplitL "FW1"; last iSplitL; [|iApply wsat_init; iFrame|eauto].
      iPoseProof (own_mono with "FW1") as "?"; last iFrame.
      exists ε; rewrite right_id; intros i; destruct (decide (i = u)); clarify;
        [rewrite !discrete_fun_lookup_singleton|rewrite !discrete_fun_lookup_singleton_ne]; eauto.
      intros x; ss; des_ifs. 
      { rewrite Nat.ltb_ge in Heq0; lia. }
      { rewrite Nat.ltb_ge in Heq1; rewrite Nat.ltb_lt in Heq0; lia. }
      { rewrite Nat.ltb_ge in Heq0; rewrite Nat.ltb_lt in Heq1; lia. }
    }
    { iPoseProof (IHNIN with "FW") as "FW".
      iEval (rewrite (discrete_fun_delete m (λ n, if n <? m then ε else gmap_view_auth (DfracOwn 1) ∅))) in "FW".
      rewrite -discrete_fun_singleton_op own_op. des_ifs; first by rewrite Nat.ltb_lt in Heq; lia.
      iDestruct "FW" as "[[FW1 FW2] FW3]"; iPoseProof (wsat_init with "FW2") as "FW2".
      iSplitR "FW2 FW3".
      { iPoseProof (own_mono with "FW1") as "?"; last iFrame.
        exists ε; rewrite right_id; intros i; destruct (decide (i = u)); clarify;
          [rewrite !discrete_fun_lookup_singleton|rewrite !discrete_fun_lookup_singleton_ne]; eauto.
        intros x; ss; des_ifs. 
        { rewrite Nat.ltb_ge in Heq0; lia. }
        { rewrite Nat.ltb_ge in Heq1; rewrite Nat.ltb_lt in Heq0; lia. }
        { rewrite Nat.ltb_ge in Heq0; rewrite Nat.ltb_lt in Heq1; lia. }
      }
      replace (S m - b) with ((m - b) + 1) by lia.
      rewrite (seq_app _ 1); ss; replace (b + (m - b)) with m by lia.
      rewrite big_sepL_app; iFrame; iApply big_sepL_nil; eauto.
    }
  Qed.

  Lemma wsats_split u (b b' : level) (LE : b <= b'):
    wsatseq u b ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n) ⊣⊢ wsatseq u b'.
  Proof.
    replace b' with (b + (b' - b)) at 2 by lia.
    rewrite /wsatseq (seq_app b _) /= big_sepL_app; eauto.
  Qed.
  
  Lemma wsats_ownI_open u b n i p (LE : n < b) :
    ownI u n i p ∗ wsatseq u b ∗ ownE u {[i]} ⊢ |==> ⟦p⟧ ∗ wsatseq u b ∗ ownD u {[i]}.
  Proof.
    iIntros "(I & SAT & EN)".
    rewrite -(@wsats_split u (S n)); last by lia.
    rewrite ?wsats_fold; iDestruct "SAT" as "((SAT1 & SAT2) & SAT3)".
    iMod (wsat_ownI_open with "[I SAT1 EN]") as "[P [WSAT D]]"; first iFrame.
    iModIntro; iFrame.
  Qed.

  Lemma wsats_ownI_close u b n i p (LE : n < b) :
    ownI u n i p -∗ wsatseq u b -∗ ⟦p⟧ -∗ ownD u {[i]} ==∗ wsatseq u b ∗ ownE u {[i]}.
  Proof.
    iIntros "#I SAT P D".
    rewrite -(@wsats_split u (S n)); last by lia.
    rewrite ?wsats_fold; iDestruct "SAT" as "((SAT1 & SAT2) & SAT3)".
    iMod (wsat_ownI_close with "[I SAT1 D P]") as "[WSAT EN]"; first by iFrame; done.
    iModIntro; iFrame.
  Qed.

  Lemma closed_universe_mon {u} b b' (LE : b <= b') E:
    wsats u b E ⊢ wsats u b' E.
  Proof.
    unfold wsats. iIntros "(W & E & D & FU)". inv LE; iFrame.
    rewrite (@free_worlds_alloc _ b (S m)); [|nia].
    iDestruct "W" as "[FW L]". iCombine "FU L" as "W". rewrite wsats_split; [iFrame|nia].
  Qed.

End wsats_aux.

Section fancy_aux.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.
  Notation iProp := (iProp Σ).

  Local Definition fancy_wsats u b (E: coPset): iProp :=
    ownE u E ∗ ownD_auth u ∗ wsatseq u b.
  Definition fancy_upd u b (E1 E2 : coPset) (P : iProp) : iProp :=
    fancy_wsats u b E1 ==∗ (fancy_wsats u b E2 ∗ P).
  
  Lemma fupd_mono u b b' E1 E2 P (LE : b <= b') :
    fancy_upd u b E1 E2 P ⊢ fancy_upd u b' E1 E2 P.
  Proof.
    iIntros "FUPD (A & R & SAT)". unfold FUpd, fancy_wsats.
    rewrite -(wsats_split _ LE).
    iDestruct "SAT" as "[SAT1 SAT2]".
    iMod ("FUPD" with "[A SAT1 R]") as "T"; iFrame. iModIntro; iFrame.
  Qed.

  Lemma fupd_mask_frame u b E1 E2 E P (DISJ : E1 ## E):
    fancy_upd u b E1 E2 P ⊢ fancy_upd u b (E1 ∪ E) (E2 ∪ E) P.
  Proof.
    iIntros "FUPD (E & D & SAT)". unfold FUpd, fancy_wsats.
    iPoseProof (ownE_op _ _ _ DISJ with "E") as "(E1 & E)".
    iPoseProof ("FUPD" with "[SAT E1 D]") as ">((E1 & D & SAT) & P)"; iFrame.
    iPoseProof (ownE_exploit with "[E E1]") as "%EN"; iFrame.
    iModIntro. iApply ownE_op; et; iFrame.
  Qed.

  Lemma fupd_open u b n N E (LT : n < b) (IN : ↑N ⊆ E) p :
    inv u n N p ⊢ fancy_upd u b E (E∖↑N) (⟦p⟧ ∗ ((⟦p⟧) -∗ fancy_upd u b (E∖↑N) E emp)).
  Proof.
    unfold inv. rewrite seal_eq. unfold invariants.inv_def, fancy_upd, fancy_wsats.
    iIntros "[% (%iN & #HI)] (EN & D & WSAT)".
    rewrite {1}(union_difference_L (↑N) E); eauto.
    iPoseProof (ownE_op with "EN") as "[EN EE]"; first by set_solver.
    rewrite {1}(union_difference_singleton_L i (↑N)); eauto.
    iPoseProof (ownE_op with "EN") as "[EN Ei]"; first by set_solver.
    iMod (@wsats_ownI_open _ _ _ _ _ _ u b n i p with "[WSAT EN]") as "(P & SAT & Di)"; [eauto|iFrame; done|].
    iModIntro; iFrame. iIntros "P (E & D & WSAT)".
    iMod (@wsats_ownI_close _ _ _ _ _ _ u b n i p with "HI WSAT P Di") as "[SAT EE]"; first by auto.
    iModIntro; iFrame.
    iAssert (ownE u ({[i]} ∪ (↑N ∖ {[i]})))%I with "[Ei EE]" as "EE".
    { iPoseProof (ownE_exploit with "[Ei EE]") as "%"; iFrame.
      iApply ownE_op; et. iFrame. }
    rewrite -union_difference_singleton_L; last by eauto.
    iAssert (ownE u (↑N ∪ (E ∖ ↑N)))%I with "[E EE]" as "E".
    { iPoseProof (ownE_exploit with "[E EE]") as "%"; iFrame.
      iApply ownE_op; et. iFrame. }
    rewrite -union_difference_L; by done.
  Qed.

End fancy_aux.

Section invariants.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.
  Notation iProp := (iProp Σ).

  Definition close_inv (u: positive) (n invn: nat) (ns: namespace) (p: SRFSyn.t invn) : iProp :=
    (⟦p⟧ -∗ wsats u n (⊤ ∖ ↑ns) ==∗ wsats u n ⊤).

  Lemma open_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    inv u lv0 ns p ∗ wsats u lv1 ⊤
    ⊢
    |==> (⟦ p ⟧ ∗ @close_inv u lv1 lv0 ns p ∗ wsats u lv1 (⊤∖↑ns)).
  Proof.
    iIntros "[#INV W]".
    iPoseProof (fupd_open with "[INV]") as "F"; et.
    unfold fancy_upd, fancy_wsats, wsats.
    iDestruct "W" as "(A & E & D & W)".
    iPoseProof ("F" with "[E D W]") as "FU". { iFrame. }
    iMod "FU". iDestruct "FU" as "(W & P & CI)". iSplitL "P"; et.
    iSplitR "A W". 2:{ iFrame. et. }
    iModIntro. unfold close_inv. iIntros "P W". iPoseProof ("CI" with "[P]") as "P"; et.
    iDestruct "W" as "[U W]". iPoseProof ("P" with "[W]") as ">((E & D & W) & _)". { iFrame. }
    iModIntro. iFrame.
  Qed.

  Lemma close_invariant u lv0 lv1 ns p
    (LT: lv0 < lv1)
  :
    ⟦ p ⟧ ∗ wsats u lv1 (⊤∖↑ns) ∗ @close_inv u lv1 lv0 ns p
    ⊢
    |==> wsats u lv1 ⊤.
  Proof.
    iIntros "(INV & W & CLOSE)".
    unfold close_inv. iPoseProof ("CLOSE" with "[INV]") as "INV"; et.
    iPoseProof ("INV" with "[W]") as "W"; et.
  Qed.

End invariants.

Global Opaque fancy_upd.
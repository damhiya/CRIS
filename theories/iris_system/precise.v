Require Import sflib.
From iris.algebra Require Import ofe auth agree coPset gset gmap_view.
From iris.proofmode Require Import proofmode.
From iris Require Import bi.big_op.
Require Import Coqlib.
Require Import functions.
Require Import own.

Section Precise.

  Context `{Σ: GRA}.

  Definition precise (P: iProp Σ) : iProp Σ :=
    □ (∃ pr, (Own pr ==∗ P) ∗ (P ==∗ Own pr)).

  Lemma precise_sep P Q :
    precise P ∗ precise Q ⊢ precise (P ∗ Q).
  Proof.
    rewrite /precise !bi.intuitionistically_exist.
    iIntros "[[%r1 [#H1 #H2]] [%r2 [#H3 #H4]]]".
    iExists (r1 ⋅ r2). iModIntro. iSplitL.
    - iIntros "[P Q]". iSplitL "P"; [iApply "H1"|iApply "H3"]; et.
    - iIntros "[P Q]". iSplitL "P"; [iApply "H2"|iApply "H4"]; et.
  Qed.

  Lemma precise_or_ex_sep_l X P (Q: X → _) :
    precise P ∗ precise (∃ x, Q x) ⊢ precise (∃ x, P ∗ Q x).
  Proof.
    rewrite /precise !bi.intuitionistically_exist.
    iIntros "[[%r1 [#H1 #H2]] [%r2 [#H3 #H4]]]".
    iExists (r1 ⋅ r2). iModIntro. iSplitL.
    - iIntros "[P1 P2]".
      iMod ("H3" with "P2") as (?) "Q".
      iMod ("H1" with "P1") as "P". iModIntro. iExists _. iFrame.
    - iIntros "H". iDestruct "H" as (?) "[P Q]".
      iSplitL "H2 P".
      + iApply "H2"; et.
      + iApply "H4"; et.
  Qed.

  Lemma ex_sep_comm {X} (P Q: X → iProp Σ) :
    (∃ x, P x ∗ Q x) ⊣⊢ (∃ x, Q x ∗ P x).
  Proof.
    iSplit; iIntros "[% H]"; iExists _; rewrite comm; et.
  Qed.
  
  Lemma precise_or_ex_sep_r X (P: X → _) Q :
    precise (∃ x, P x) ∗ precise Q ⊢ precise (∃ x, P x ∗ Q).
  Proof.
    rewrite comm. iIntros "H".
    iPoseProof (precise_or_ex_sep_l with "H") as "H".
    rewrite /precise !bi.intuitionistically_exist.
    iDestruct "H" as "[% H]". iExists _.
    rewrite ex_sep_comm. et.
  Qed.
  
  Lemma precise_or_l P Q1 Q2 :
    precise P ∗ precise (Q1 ∨ Q2) ⊢ precise ((P ∗ Q1) ∨ (P ∗ Q2)).
  Proof.
    rewrite /precise !bi.intuitionistically_exist.
    iIntros "[[%r1 [#H1 #H2]] [%r2 [#H3 #H4]]]".
    iExists (r1 ⋅ r2). iModIntro. iSplitL.
    - iIntros "[P1 P2]".
      iMod ("H1" with "P1") as "P".
      iMod ("H3" with "P2") as "[Q|Q]"; [iLeft|iRight]; iFrame; et.
    - iIntros "[[P Q]|[P Q]]"; (iSplitL "P"; [iApply "H2"|iApply "H4"]); et.
  Qed.

  Lemma precise_or_r P1 P2 Q :
    precise (P1 ∨ P2) ∗ precise Q ⊢ precise ((P1 ∗ Q) ∨ (P2 ∗ Q)).
  Proof.
    rewrite comm. iIntros "H".
    iPoseProof (precise_or_l with "H") as "H".
    rewrite {1}/precise !bi.intuitionistically_exist.
    iDestruct "H" as "[% H]". rewrite (comm (∗) Q P1)%I (comm (∗) Q P2)%I.
    iExists _. et.
  Qed.

  Lemma precise_emp:
    ⊢ precise emp%I.
  Proof.
    iIntros. iExists ε. iSplitL ""; et. iModIntro. iIntros "H". iApply Own_unit.
  Qed.

  Lemma precise_Own r:
    ⊢ precise (Own r).
  Proof.
    iIntros. iExists r. iSplitL ""; et.
  Qed.

  Lemma precise_own {A} `{IN: @inG A Σ} γ (r: A) :
    ⊢ precise (own γ r).
  Proof.
    iExists (own.iRes_singleton γ r).
    rewrite own.Own_eq /own seal_eq /own.own_def /own.Own_def.
    iSplitL ""; et.
  Qed.
    
End Precise.

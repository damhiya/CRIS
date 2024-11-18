(* TODO : This file seems like a small iris proofmode.
   Find a way to integrate the usages of this file to proofmodes. *)
(* Note : codes until start_ipm_proof are useless codes - move below codes to separate file
   (or maybe remove them) *)

Require Import Coqlib.
Require Export IPM PCM.

Section IMOD.

  Lemma imod_trans `{Σ : GRA.t} (P Q R : iProp Σ) :
    (P ⊢ |==> Q) -> (Q ⊢ |==> R) -> (P ⊢ |==> R).
  Proof.
    etransitivity; eauto.
    iIntros ">Q". by iApply H0.
  Qed.

  Lemma imod_elim_trueL `{Σ : GRA.t} (P Q : iProp Σ) :
    (P ⊢ |==> Q) -> (P ⊢ |==> (True ∗ Q)).
  Proof.
    i. iIntros "H". iSplitR; eauto. iStopProof. eauto.
  Qed.

  Lemma imod_intro_trueL `{Σ : GRA.t} (P Q : iProp Σ) :
    (P ⊢ |==> (True ∗ Q)) -> (P ⊢ |==> Q).
  Proof.
    i. iIntros "H". iPoseProof (H with "H") as "H".
    iMod "H". iDestruct "H" as "[X Y]". eauto.
  Qed.

  Lemma imod_elim_trueR `{Σ : GRA.t} (P Q : iProp Σ) :
    (P ⊢ |==> Q) -> (P ⊢ |==> (Q ∗ True)).
  Proof.
    i. iIntros "H". iSplitL; eauto. iStopProof. eauto.
  Qed.

  Lemma imod_intro_trueR `{Σ : GRA.t} (P Q : iProp Σ) :
    (P ⊢ |==> (Q ∗ True)) -> (P ⊢ |==> Q).
  Proof.
    i. iIntros "H". iPoseProof (H with "H") as "H".
    iMod "H". iDestruct "H" as "[X Y]". eauto.
  Qed.
End IMOD.

Create HintDb imodL.
Hint Resolve imod_trans imod_elim_trueL : imodL.

Ltac imodIntroL :=
  i; repeat match goal with [H : (_ ⊢ |==> (True ∗ _)) |- _ ] => apply imod_intro_trueL in H end; eauto with imodL.

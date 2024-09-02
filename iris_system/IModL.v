Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.
Require Import Coq.Init.Decimal.
Require Export IPM.

Section ILIST.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Definition iPropL := alist string iProp.

  Fixpoint from_iPropL (l: iPropL): iProp :=
    match l with
    | [] => (emp)%I
    | (_, Phd)::Ptl => Phd ∗ (from_iPropL Ptl)
    end.

  Fixpoint get_ipm_pat (l: iPropL): string :=
    match l with
    | [] => "_"
    | (Hn, _) :: tl =>
      append "[" (append Hn (append " " (append (get_ipm_pat tl) "]")))
    end.

  Fixpoint is_fresh_name (Hn: string) (l: iPropL): bool :=
    match l with
    | [] => true
    | (Hn', _)::tl =>
      match String.eqb Hn Hn' with
      | true => false
      | false => is_fresh_name Hn tl
      end
    end.

  Fixpoint uint_to_string (n: uint) (acc: string): string :=
    match n with
    | Nil => acc
    | D0 tl => uint_to_string tl (append "0" acc)
    | D1 tl => uint_to_string tl (append "1" acc)
    | D2 tl => uint_to_string tl (append "2" acc)
    | D3 tl => uint_to_string tl (append "3" acc)
    | D4 tl => uint_to_string tl (append "4" acc)
    | D5 tl => uint_to_string tl (append "5" acc)
    | D6 tl => uint_to_string tl (append "6" acc)
    | D7 tl => uint_to_string tl (append "7" acc)
    | D8 tl => uint_to_string tl (append "8" acc)
    | D9 tl => uint_to_string tl (append "9" acc)
    end.

  Definition nat_to_string :=
    (fun n => uint_to_string (Nat.to_little_uint n Nil) "").

  Fixpoint get_fresh_name'
           (base: string) (n: nat) (fuel: nat) (l: iPropL): string :=
    match fuel with
    | 0 => "TMP"
    | S fuel' =>
      let Hn := append base (nat_to_string n) in
      if is_fresh_name Hn l
      then Hn
      else get_fresh_name' base (S n) fuel' l
    end.

  Definition get_fresh_name (base: string) (l: iPropL): string :=
    if is_fresh_name base l
    then base
    else get_fresh_name' base 0 100 l.

  Lemma iPropL_clear (Hn: string) (l: iPropL)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_remove Hn l).
  Proof.
    induction l; ss.
    { iIntros "H". iModIntro. iFrame. }
    { destruct a. iIntros "[H0 H1]". rewrite eq_rel_dec_correct. des_ifs; ss.
      { iPoseProof (IHl with "H1") as "> H1".
        iModIntro. iFrame. }
      { iPoseProof (IHl with "H1") as "> H1".
        iClear "H0". iModIntro. iFrame. }
    }
  Qed.

  Lemma iPropL_find_remove (Hn: string) (l: iPropL) P
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ #=> (P ∗ from_iPropL (alist_remove Hn l)).
  Proof.
    revert P FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in FIND.
    rewrite eq_rel_dec_correct. des_ifs; ss.
    { iPoseProof (IHl with "H1") as "> H1"; et.
      iModIntro. iFrame. iFrame. }
    { iFrame. iApply iPropL_clear. iFrame. }
  Qed.

  Lemma iPropL_one Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ #=> P.
  Proof.
    iIntros "H". iPoseProof (iPropL_find_remove with "H") as "> [H0 H1]"; et.
  Qed.

  Lemma iPropL_init (Hn: string) (P: iProp)
    :
      P -∗ from_iPropL [(Hn, P)].
  Proof.
    ss. iIntros "H". iFrame.
  Qed.

  Lemma iPropL_uentail Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ #=> P1)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    revert P0 P1 FIND ENTAIL. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in FIND.
    rewrite eq_rel_dec_correct. des_ifs.
    { ss. iPoseProof (IHl with "H1") as "H1"; et. repeat iFrame. }
    { ss. iPoseProof (ENTAIL with "H0") as "> H0".
      iPoseProof (iPropL_clear with "H1") as "> H1".
      iModIntro. iFrame. }
  Qed.

  Lemma iPropL_entail Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    eapply iPropL_uentail; et. iIntros "H".
    iPoseProof (ENTAIL with "H") as "H". iModIntro. iFrame.
  Qed.

  Lemma iPropL_upd Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some (#=> P))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P l).
  Proof.
    hexploit (@iPropL_uentail Hn l (#=> P) P); et.
  Qed.

  Lemma iPropL_destruct_ex Hn (l: iPropL) A (P: A -> iProp)
        (FIND: alist_find Hn l = Some (∃ (a: A), P a)%I)
    :
      from_iPropL l -∗ ∃ (a: A), #=> from_iPropL (alist_add Hn (P a) l).
  Proof.
    revert FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in FIND.
    rewrite eq_rel_dec_correct. des_ifs; ss.
    { iPoseProof (IHl with "H1") as (a) "H1"; et.
      iExists a. repeat iFrame. }
    { iDestruct "H0" as (a) "H0". iExists a.
      iFrame. iApply iPropL_clear. iFrame. }
  Qed.

  Lemma iPropL_destruct_or Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      from_iPropL l -∗ (#=> from_iPropL (alist_add Hn P0 l)) ∨ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    revert FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in FIND.
    rewrite eq_rel_dec_correct. des_ifs; ss.
    { iPoseProof (IHl with "H1") as "[H1|H1]"; et.
      { iLeft. repeat iFrame. }
      { iRight. repeat iFrame. }
    }
    { iDestruct "H0" as "[H0|H0]".
      { iLeft. iFrame. iApply iPropL_clear. iFrame. }
      { iRight. iFrame. iApply iPropL_clear. iFrame. }
    }
  Qed.

  Lemma iPropL_add (Hn: string) (l: iPropL) P
    :
      P ∗ from_iPropL l -∗ #=> (from_iPropL (alist_add Hn P l)).
  Proof.
    unfold alist_add. ss. iIntros "[H0 H1]".
    iFrame. iApply iPropL_clear. iFrame.
  Qed.

  Lemma iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn_old l = Some (P0 ∗ P1)%I)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
    iIntros "H".
    iPoseProof (iPropL_find_remove with "H") as "> [H0 H1]"; et.
    iDestruct "H0" as "[H0 H2]". iCombine "H0 H1" as "H0".
    iPoseProof (iPropL_add with "H0") as "> H".
    iApply iPropL_add. iFrame.
  Qed.

  Lemma iPropL_alist_pop Hn P (l0 l1: iPropL)
        (FIND: alist_pop Hn l0 = Some (P, l1))
    :
      from_iPropL l0 ⊢ P ∗ from_iPropL l1.
  Proof.
    revert P l1 FIND. induction l0; ss. i.
    destruct a. rewrite eq_rel_dec_correct in FIND. des_ifs.
    ss. hexploit IHl0; et. i.
    iIntros "[H0 H1]". iFrame. iApply H. iFrame.
  Qed.

  Lemma iPropL_alist_pops l Hns
    :
      from_iPropL l ⊢ from_iPropL (fst (alist_pops Hns l)) ∗ from_iPropL (snd (alist_pops Hns l)).
  Proof.
    induction Hns. ss.
    { iIntros "H0". iFrame. }
    { ss. des_ifs. ss. etrans; et.
      iIntros "[H0 H1]". iFrame.
      iApply iPropL_alist_pop; et. }
  Qed.

  Lemma iPropL_assert (Hns: list string) (Hn_new: string) (l: iPropL) (P: iProp)
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new P (snd (alist_pops Hns l))).
  Proof.
    iIntros "H". iPoseProof (iPropL_alist_pops with "H") as "[H0 H1]".
    iPoseProof (FIND with "H0") as "H0".
    iApply iPropL_add. iFrame.
  Qed.

  Fixpoint parse_hyps (b: bool) (k: string -> string) (Hns: string): list string :=
    match Hns with
    | EmptyString => if b then [k ""] else []
    | String (Ascii.Ascii false false false false false true false false) tl =>
      (k "") :: parse_hyps false id tl
    | String c tl =>
      parse_hyps true (fun str => k (String c str)) tl
    end.

  Definition parse_hyps_complete (Hns: string): (bool * list string) :=
    match Hns with
    | EmptyString => (true, [])
    | "*" => (false, [])
    | String (Ascii.Ascii true false true true false true false false)
             (String (Ascii.Ascii false false false false false true false false)
                     tl) => (false, parse_hyps true id tl)
    | String (Ascii.Ascii true false true true false true false false)
             tl => (false, parse_hyps true id tl)
    | _ => (true, parse_hyps true id Hns)
    end.

  Definition list_compl (l0 l1: list string): list string :=
    List.filter (fun str0 => forallb (fun str1 => negb (beq_str str0 str1)) l0) l1.
End ILIST.
Arguments from_iPropL: simpl never.

Ltac start_ipm_proof :=
  match goal with
  | |- from_iPropL ?l -∗ _ =>
    let pat := (eval simpl in (get_ipm_pat l)) in
    simpl; iIntros pat
  | _ => try unfold from_iPropL
  end.

Section IMOD.


  Lemma bind_ret_l_eta A {E R} (k: A -> itree E R):
    (λ x : A, x0 <- Ret x;; k x0) = k.
  Proof. extensionality x. grind. Qed.

  Lemma imod_trans `{Σ: GRA.t} (P Q R: iProp Σ) :
    (P ⊢ #=> Q) -> (Q ⊢ #=> R) -> (P ⊢ #=> R).
  Proof.
    etransitivity; eauto.
    iIntros ">Q". by iApply H0.
  Qed.

  Lemma imod_elim_trueL `{Σ: GRA.t} (P Q : iProp Σ) :
    (P ⊢ #=> Q) -> (P ⊢ #=> (True ∗ Q)).
  Proof.
    i. iIntros "H". iSplitR; eauto. iStopProof. eauto.
  Qed.

  Lemma imod_intro_trueL `{Σ: GRA.t} (P Q : iProp Σ) :
    (P ⊢ #=> (True ∗ Q)) -> (P ⊢ #=> Q).
  Proof.
    i. iIntros "H". iPoseProof (H with "H") as "H".
    iMod "H". iDestruct "H" as "[X Y]". eauto.
  Qed.

  Lemma imod_elim_trueR `{Σ: GRA.t} (P Q : iProp Σ) :
    (P ⊢ #=> Q) -> (P ⊢ #=> (Q ∗ True)).
  Proof.
    i. iIntros "H". iSplitL; eauto. iStopProof. eauto.
  Qed.

  Lemma imod_intro_trueR `{Σ: GRA.t} (P Q : iProp Σ) :
    (P ⊢ #=> (Q ∗ True)) -> (P ⊢ #=> Q).
  Proof.
    i. iIntros "H". iPoseProof (H with "H") as "H".
    iMod "H". iDestruct "H" as "[X Y]". eauto.
  Qed.
End IMOD.

Create HintDb imodL.
Hint Resolve imod_trans imod_elim_trueL: imodL.


Ltac imodIntroL :=
  i; repeat match goal with [H: (_ ⊢ #=> (True ∗ _)) |- _ ] => apply imod_intro_trueL in H end; eauto with imodL.

Ltac grind_ret := try rewrite !bind_ret_l_eta in *; subst.

Ltac itree_clarify H :=
  revert H; grind; try unfold trigger in H; try rewrite !bind_vis in H; try depdes H; grind_ret.



